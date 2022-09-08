
open Syntax
open Normalization

module Env = Map.Make(String)

type context =
    { level  : int
    ; values : value list
    ; typs   : value list
    ; locals : (string * (int * value)) list }


let empty_ctx =
    { level  = 0
    ; values = []
    ; typs   = []
    ; locals = [] }


let add_local name typ ctx =
    { level  = ctx.level + 1
    ; values = V_Ne(N_Level ctx.level) :: ctx.values
    ; typs   = typ :: ctx.typs
    ; locals = (name, (ctx.level, typ)) :: ctx.locals }



let rec infer globals ctx expr =
    match expr.shape with
    | E_Var name ->
        begin match List.assoc name ctx.locals with
        | lvl, typ ->
            typ, C_Local(ctx.level - lvl - 1)
        | exception Not_found ->
            match Hashtbl.find globals name with
            | V_Axiom typ | V_Def(_, typ) -> typ, C_TopVar name
            | exception Not_found         -> failwith ("unbound variable " ^ name)
        end

    | E_Ann(expr', typ) ->
        let _, ctyp = check_typ globals ctx typ in
        let typv = eval globals ctx.values ctyp in
        let cexpr' = check globals ctx typv expr' in
        typv, cexpr'

    | E_Type ulevel ->
        (* V_Type(ulevel + 1), C_Type ulevel *)
        V_Type ulevel, C_Type ulevel

    | E_TyFun((name, a), b) ->
        let ul_a, ca = check_typ globals ctx a in
        let va = eval globals ctx.values ca in
        let ul_b, cb = check_typ globals (add_local name va ctx) b in
        V_Type(max ul_a ul_b), C_TyFun(ca, cb)

    | E_Fun((_, None), _) ->
        failwith "cannot infer type of function without parameter annotation"

    | E_Fun((name, Some param_ty), body) ->
        let _, c_param_ty = check_typ globals ctx param_ty in
        let v_param_ty = eval globals ctx.values c_param_ty in
        let ctx' = add_local name v_param_ty ctx in
        let v_ret_ty, c_body = infer globals ctx' body in
        let c_ret_ty, _ = quote_typ globals ctx'.level ctx'.typs v_ret_ty in
        ( V_TyFun(v_param_ty, fun v -> eval globals (v :: ctx.values) c_ret_ty)
        , C_Fun c_body )

    | E_App(func, arg) ->
        begin match infer globals ctx func with
        | V_TyFun(a, b), c_func ->
            let c_arg = check globals ctx a arg in
            b (eval globals ctx.values c_arg), C_App(c_func, c_arg)
        | _ ->
            failwith "type error: application: not a function"
        end

    | E_TyPair((name, fst_ty), snd_ty) ->
        let ul_fst, c_fst_ty = check_typ globals ctx fst_ty in
        let v_fst_ty = eval globals ctx.values c_fst_ty in
        let ul_snd, c_snd_ty = check_typ globals (add_local name v_fst_ty ctx) snd_ty in
        V_Type(max ul_fst ul_snd), C_TyPair(c_fst_ty, c_snd_ty)

    | E_Pair(fst, snd) ->
        let fst_ty, c_fst = infer globals ctx fst in
        let snd_ty, c_snd = infer globals ctx snd in
        V_TyPair(fst_ty, fun _ -> snd_ty), C_Pair(c_fst, c_snd)

    | E_Proj(pair, field) ->
        begin match infer globals ctx pair with
        | V_TyPair(fst_ty, snd_ty), c_pair ->
            begin match field with
            | `Fst -> fst_ty, C_Proj(c_pair, field)
            | `Snd ->
                let v_fst = value_proj (eval globals ctx.values c_pair) `Fst in
                snd_ty v_fst, C_Proj(c_pair, field)
            end
        | _ ->
            failwith "type error: projection: not a pair"
        end

    | E_TyEq(lhs, rhs) ->
        let lhs_ty, c_lhs = infer globals ctx lhs in
        let rhs_ty, c_rhs = infer globals ctx rhs in
        let c_lhs_ty, ul_lhs = quote_typ globals ctx.level ctx.typs lhs_ty in
        let c_rhs_ty, ul_rhs = quote_typ globals ctx.level ctx.typs rhs_ty in
        V_Type(max ul_lhs ul_rhs), C_TyEq((c_lhs, c_lhs_ty), (c_rhs, c_rhs_ty))

    | E_Coe(target, eq) ->
        begin match infer globals ctx eq with
        | V_TyEq((lhs, V_Type ul_lhs), (rhs, V_Type ul_rhs)), c_eq ->
            let c_target = check globals ctx lhs target in
            let c_lhs, _ = quote_typ globals ctx.level ctx.typs lhs in
            let c_rhs, _ = quote_typ globals ctx.level ctx.typs rhs in
            rhs, C_Coe { target = c_target
                       ; eq     = Lazy.from_val c_eq
                       ; lhs    = c_lhs
                       ; rhs    = c_rhs }
        | _ ->
            failwith "type error: coercion: not a type equality"
        end

and check globals ctx typ expr =
    match typ, expr.shape with
    | V_TyFun(param_ty, ret_ty), E_Fun((name, param_ann), body) ->
        begin match param_ann with
        | Some ann ->
            let _, c_ann = check_typ globals ctx ann in
            let ann_typ = eval globals ctx.values c_ann in
            if not @@ typ_equal globals ctx.level ctx.typs param_ty ann_typ then
                failwith "type error: parameter annotation mismatch"
        | None ->
            ()
        end;
        let ret_ty' = ret_ty @@ V_Ne(N_Level ctx.level) in
        let c_body = check globals (add_local name param_ty ctx) ret_ty' body in
        C_Fun c_body
    | V_TyPair(fst_ty, snd_ty), E_Pair(fst, snd) ->
        let c_fst = check globals ctx fst_ty fst in
        let v_fst = eval globals ctx.values c_fst in
        let c_snd = check globals ctx (snd_ty v_fst) snd in
        C_Pair(c_fst, c_snd)
    | _ ->
        let typ', c_expr = infer globals ctx expr in
        if not @@ typ_equal globals ctx.level ctx.typs typ typ' then
            failwith "type error: type mismatch";
        c_expr

and check_typ globals ctx expr =
    match infer globals ctx expr with
    | V_Type ulevel, c_expr -> ulevel, c_expr
    | _                     -> failwith "type error: type expected"



let process_top_level globals top =
    match top with
    | AxiomDecl(name, typ) ->
        begin match Hashtbl.find_opt globals name with
        | Some _ -> failwith ("re-declaring variable " ^ name)
        | None   -> ()
        end;
        let _, c_typ = check_typ globals empty_ctx typ in
        Hashtbl.add globals name (V_Axiom(eval globals [] c_typ));
        C_AxiomDecl(name, c_typ)
    | Definition(name, def) ->
        let typ, c_def =
            match Hashtbl.find_opt globals name with
            | Some(V_Axiom typ) -> (typ, check globals empty_ctx typ def)
            | Some(V_Def _)     -> failwith ("re-defining variable " ^ name)
            | None              -> infer globals empty_ctx def
        in
        Hashtbl.add globals name (V_Def(eval globals [] c_def, typ));
        C_Definition(name, c_def, fst @@ quote_typ globals 0 [] typ)


let rec process_program globals = function
    | []          -> []
    | top :: tops ->
        let c_top = process_top_level globals top in
        c_top :: process_program globals tops
