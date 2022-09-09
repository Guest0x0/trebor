
open Syntax
open Normalization

module Env = Map.Make(String)

type context =
    { level  : int
    ; values : value list
    ; typs   : value list
    ; locals : (string * value) list }


let empty_ctx =
    { level  = 0
    ; values = []
    ; typs   = []
    ; locals = [] }


let add_local name typ ctx =
    { level  = ctx.level + 1
    ; values = V_Ne(N_Level ctx.level) :: ctx.values
    ; typs   = typ :: ctx.typs
    ; locals = (name, typ) :: ctx.locals }


let lookup_local name ctx =
    let rec loop idx = function
        | [] ->
            raise Not_found
        | (name', typ) :: _ when name = name' ->
            idx, typ
        | _ :: rest ->
            loop (idx + 1) rest
    in
    loop 0 ctx.locals


let quote_locals globals ctx =
    let rec loop level typs locals =
        match typs, locals with
        | [], [] ->
            []
        | typ :: typs', (name, _) :: locals' ->
            let typ, _ = quote_typ globals (level - 1) typs' typ in
            (name, typ) :: loop (level - 1) typs' locals'
        | _ ->
            failwith "Core.Typecheck.runtime_error"
    in
    loop ctx.level ctx.typs ctx.locals




let rec infer globals ctx expr =
    match expr.shape with
    | E_Var name ->
        begin match lookup_local name ctx with
        | idx, typ ->
            typ, C_Local idx
        | exception Not_found ->
            match Hashtbl.find globals name with
            | V_Axiom typ | V_Def(_, typ) -> typ, C_TopVar name
            | exception Not_found         -> raise @@ TypeError(expr.span, UnboundVar name)
        end

    | E_Ann(expr', typ) ->
        let _, ctyp = check_typ globals ctx typ in
        let typv = eval globals ctx.values ctyp in
        let cexpr' = check "type annotation" globals ctx typv expr' in
        typv, cexpr'

    | E_Type ulevel ->
        V_Type(ulevel + 1), C_Type ulevel

    | E_Shift(shift, expr') ->
        let typ, core = infer globals ctx expr' in
        value_shift shift typ, C_Shift(shift, core)

    | E_TyFun((name, a), b) ->
        let ul_a, ca = check_typ globals ctx a in
        let va = eval globals ctx.values ca in
        let ul_b, cb = check_typ globals (add_local name va ctx) b in
        V_Type(max ul_a ul_b), C_TyFun((name, ca), cb)

    | E_Fun((_, None), _) ->
        raise @@ TypeError(expr.span, CannotInfer "function without parameter annotation")

    | E_Fun((name, Some param_ty), body) ->
        let _, c_param_ty = check_typ globals ctx param_ty in
        let v_param_ty = eval globals ctx.values c_param_ty in
        let ctx' = add_local name v_param_ty ctx in
        let v_ret_ty, c_body = infer globals ctx' body in
        let c_ret_ty, _ = quote_typ globals ctx'.level ctx'.typs v_ret_ty in
        ( V_TyFun((name, v_param_ty), fun v -> eval globals (v :: ctx.values) c_ret_ty)
        , C_Fun(name, c_body) )

    | E_App(func, arg) ->
        begin match infer globals ctx func with
        | V_TyFun((_, a), b), c_func ->
            let c_arg = check "function application" globals ctx a arg in
            b (eval globals ctx.values c_arg), C_App(c_func, c_arg)
        | typ_v, _ ->
            let typ, _ = quote_typ globals ctx.level ctx.typs typ_v in
            raise @@ TypeError(expr.span, WrongType(quote_locals globals ctx, typ, "function"))
        end

    | E_TyPair((name, fst_ty), snd_ty) ->
        let ul_fst, c_fst_ty = check_typ globals ctx fst_ty in
        let v_fst_ty = eval globals ctx.values c_fst_ty in
        let ul_snd, c_snd_ty = check_typ globals (add_local name v_fst_ty ctx) snd_ty in
        V_Type(max ul_fst ul_snd), C_TyPair((name, c_fst_ty), c_snd_ty)

    | E_Pair(fst, snd) ->
        let fst_ty, c_fst = infer globals ctx fst in
        let snd_ty, c_snd = infer globals ctx snd in
        V_TyPair(("", fst_ty), fun _ -> snd_ty), C_Pair(c_fst, c_snd)

    | E_Proj(pair, field) ->
        begin match infer globals ctx pair with
        | V_TyPair((_, fst_ty), snd_ty), c_pair ->
            begin match field with
            | `Fst -> fst_ty, C_Proj(c_pair, field)
            | `Snd ->
                let v_fst = value_proj (eval globals ctx.values c_pair) `Fst in
                snd_ty v_fst, C_Proj(c_pair, field)
            end
        | typ_v, _ ->
            let typ, _ = quote_typ globals ctx.level ctx.typs typ_v in
            raise @@ TypeError(expr.span, WrongType(quote_locals globals ctx, typ, "pair"))
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
            let c_target = check "coerced value" globals ctx lhs target in
            let c_lhs, _ = quote_typ globals ctx.level ctx.typs lhs in
            let c_rhs, _ = quote_typ globals ctx.level ctx.typs rhs in
            rhs, C_Coe { target = c_target
                       ; eq     = Lazy.from_val c_eq
                       ; lhs    = c_lhs
                       ; rhs    = c_rhs }
        | typ_v, _ ->
            let typ, _ = quote_typ globals ctx.level ctx.typs typ_v in
            raise @@ TypeError(expr.span, WrongType(quote_locals globals ctx, typ, "equality"))
        end

and check err_ctx globals ctx typ expr =
    match typ, expr.shape with
    | V_TyFun((_, param_ty), ret_ty), E_Fun((name, None), body) ->
        let ret_ty' = ret_ty @@ V_Ne(N_Level ctx.level) in
        let c_body = check err_ctx globals (add_local name param_ty ctx) ret_ty' body in
        C_Fun(name, c_body)
    | V_TyPair((_, fst_ty), snd_ty), E_Pair(fst, snd) ->
        let c_fst = check err_ctx globals ctx fst_ty fst in
        let v_fst = eval globals ctx.values c_fst in
        let c_snd = check err_ctx globals ctx (snd_ty v_fst) snd in
        C_Pair(c_fst, c_snd)
    | _ ->
        let typ', c_expr = infer globals ctx expr in
        if not @@ typ_equal globals ctx.level ctx.typs typ typ' then begin
            let expected, _ = quote_typ globals ctx.level ctx.typs typ in
            let received, _ = quote_typ globals ctx.level ctx.typs typ' in
            raise @@ TypeError(
                expr.span,
                TypeMismatch(quote_locals globals ctx, expected, received, err_ctx)
            )
        end;
        c_expr

and check_typ globals ctx expr =
    match infer globals ctx expr with
    | V_Type ulevel, c_expr ->
        ulevel, c_expr
    | typ_v, _ ->
        let typ, _ = quote_typ globals ctx.level ctx.typs typ_v in
        raise @@ TypeError(expr.span, WrongType(quote_locals globals ctx, typ, "type"))



let rec check_context globals ctx_expr =
    match ctx_expr with
    | [] ->
        [], empty_ctx
    | (name, typ_expr) :: ctx_expr' ->
        let c_ctx, ctx = check_context globals ctx_expr' in
        let _, c_typ = check_typ globals ctx typ_expr in
        ( (name, c_typ) :: c_ctx
        , add_local name (eval globals ctx.values c_typ) ctx )





let check_top_level globals top =
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
            | Some(V_Axiom typ) -> (typ, check "global definition" globals empty_ctx typ def)
            | Some(V_Def _)     -> failwith ("re-defining variable " ^ name)
            | None              -> infer globals empty_ctx def
        in
        Hashtbl.add globals name (V_Def(eval globals [] c_def, typ));
        C_Definition(name, c_def, fst @@ quote_typ globals 0 [] typ)



let rec check_program globals = function
    | []          -> []
    | top :: tops ->
        let c_top = check_top_level globals top in
        c_top :: check_program globals tops
