
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



let rec infer top ctx expr =
    match expr.shape with
    | E_Var name ->
        begin match List.assoc name ctx.locals with
        | lvl, typ ->
            typ, C_Local(ctx.level - lvl - 1)
        | exception Not_found ->
            match Hashtbl.find top name with
            | V_Axiom typ | V_Def(_, typ) -> typ, C_TopVar name
            | exception Not_found         -> failwith ("unbound variable " ^ name)
        end
    | E_Ann(expr', typ) ->
        let _, ctyp = check_typ top ctx typ in
        let typv = eval top ctx.values ctyp in
        let cexpr' = check top ctx typv expr' in
        typv, cexpr'

    | E_Type ulevel ->
        (* V_Type(ulevel + 1), C_Type ulevel *)
        V_Type ulevel, C_Type ulevel

    | E_TyFun((name, a), b) ->
        let ul_a, ca = check_typ top ctx a in
        let va = eval top ctx.values ca in
        let ul_b, cb = check_typ top (add_local name va ctx) b in
        V_Type(max ul_a ul_b), C_TyFun(ca, cb)
    | E_Fun((_, None), _) ->
        failwith "cannot infer type of function without parameter annotation"
    | E_Fun((name, Some param_ty), body) ->
        let _, c_param_ty = check_typ top ctx param_ty in
        let v_param_ty = eval top ctx.values c_param_ty in
        let ctx' = add_local name v_param_ty ctx in
        let v_ret_ty, c_body = infer top ctx' body in
        let c_ret_ty, _ = quote_typ top ctx'.level ctx'.typs v_ret_ty in
        ( V_TyFun(v_param_ty, fun v -> eval top (v :: ctx.values) c_ret_ty)
        , C_Fun c_body )
    | E_App(func, arg) ->
        begin match infer top ctx func with
        | V_TyFun(a, b), c_func ->
            let c_arg = check top ctx a arg in
            b (eval top ctx.values c_arg), C_App(c_func, c_arg)
        | _ ->
            failwith "type error: application: not a function"
        end

    | E_TyPair((name, fst_ty), snd_ty) ->
        let ul_fst, c_fst_ty = check_typ top ctx fst_ty in
        let v_fst_ty = eval top ctx.values c_fst_ty in
        let ul_snd, c_snd_ty = check_typ top (add_local name v_fst_ty ctx) snd_ty in
        V_Type(max ul_fst ul_snd), C_TyPair(c_fst_ty, c_snd_ty)
    | E_Pair(fst, snd) ->
        let fst_ty, c_fst = infer top ctx fst in
        let snd_ty, c_snd = infer top ctx snd in
        V_TyPair(fst_ty, fun _ -> snd_ty), C_Pair(c_fst, c_snd)
    | E_Proj(pair, field) ->
        begin match infer top ctx pair with
        | V_TyPair(fst_ty, snd_ty), c_pair ->
            begin match field with
            | `Fst -> fst_ty, C_Proj(c_pair, field)
            | `Snd ->
                let v_fst = value_proj (eval top ctx.values c_pair) `Fst in
                snd_ty v_fst, C_Proj(c_pair, field)
            end
        | _ ->
            failwith "type error: projection: not a pair"
        end

    | E_TyEq(lhs, rhs) ->
        let lhs_ty, c_lhs = infer top ctx lhs in
        let rhs_ty, c_rhs = infer top ctx rhs in
        let c_lhs_ty, ul_lhs = quote_typ top ctx.level ctx.typs lhs_ty in
        let c_rhs_ty, ul_rhs = quote_typ top ctx.level ctx.typs rhs_ty in
        V_Type(max ul_lhs ul_rhs), C_TyEq((c_lhs, c_lhs_ty), (c_rhs, c_rhs_ty))
    | E_Coe(origin, eq) ->
        begin match infer top ctx eq with
        | V_TyEq((lhs, V_Type ul_lhs), (rhs, V_Type ul_rhs)), c_eq ->
            let c_origin = check top ctx lhs origin in
            let c_lhs, _ = quote_typ top ctx.level ctx.typs lhs in
            let c_rhs, _ = quote_typ top ctx.level ctx.typs rhs in
            rhs, C_Coe { origin = c_origin
                       ; eq     = Lazy.from_val c_eq
                       ; lhs    = c_lhs
                       ; rhs    = c_rhs }
        | _ ->
            failwith "type error: coercion: not a type equality"
        end

and check top ctx typ expr =
    match typ, expr.shape with
    | V_TyFun(param_ty, ret_ty), E_Fun((name, param_ann), body) ->
        begin match param_ann with
        | Some ann ->
            let _, c_ann = check_typ top ctx ann in
            let param_ty_nf , _ = quote_typ top ctx.level ctx.typs param_ty in
            let param_ann_nf, _ = quote_typ top ctx.level ctx.typs (eval top ctx.values c_ann) in
            if param_ty_nf <> param_ann_nf then
                failwith "type error: parameter annotation mismatch"
        | None ->
            ()
        end;
        let ret_ty' = ret_ty @@ V_Ne(N_Level ctx.level) in
        let c_body = check top (add_local name param_ty ctx) ret_ty' body in
        C_Fun c_body
    | V_TyPair(fst_ty, snd_ty), E_Pair(fst, snd) ->
        let c_fst = check top ctx fst_ty fst in
        let v_fst = eval top ctx.values c_fst in
        let c_snd = check top ctx (snd_ty v_fst) snd in
        C_Pair(c_fst, c_snd)
    | _ ->
        let typ', c_expr = infer top ctx expr in
        let typ_nf , _ = quote_typ top ctx.level ctx.typs typ in
        let typ_nf', _ = quote_typ top ctx.level ctx.typs typ' in
        if typ_nf <> typ_nf' then
            failwith "type error: type mismatch";
        c_expr

and check_typ top ctx expr =
    match infer top ctx expr with
    | V_Type ulevel, c_expr -> ulevel, c_expr
    | _                     -> failwith "type error: type expected"



let process_top_level top tl =
    match tl with
    | AxiomDecl(name, typ) ->
        begin match Hashtbl.find_opt top name with
        | Some _ -> failwith ("re-declaring variable " ^ name)
        | None   -> ()
        end;
        let _, c_typ = check_typ top empty_ctx typ in
        Hashtbl.add top name (V_Axiom(eval top [] c_typ));
        C_AxiomDecl(name, c_typ)
    | Definition(name, def) ->
        let typ, c_def =
            match Hashtbl.find_opt top name with
            | Some(V_Axiom typ) -> (typ, check top empty_ctx typ def)
            | Some(V_Def _)     -> failwith ("re-defining variable " ^ name)
            | None              -> infer top empty_ctx def
        in
        Hashtbl.add top name (V_Def(eval top [] c_def, typ));
        C_Definition(name, c_def, fst @@ quote_typ top 0 [] typ)


let rec process_program global = function
    | []          -> []
    | top :: tops ->
        let c_top = process_top_level global top in
        c_top :: process_program global tops



open struct
    let forall param_ty ret_ty = V_TyFun(param_ty, ret_ty)
    let (@->)  param_ty ret_ty = V_TyFun(param_ty, Fun.const ret_ty)

    let exists fst_ty snd_ty = V_TyPair(fst_ty, snd_ty)
    let (<*>)  fst_ty snd_ty = V_TyPair(fst_ty, Fun.const snd_ty)
end

let prelude = [
    ( "eq-refl"
    , forall (V_Type 0) @@ fun typ ->
        forall typ @@ fun elem ->
        V_TyEq((elem, typ), (elem, typ)) );
    ( "eq-symm"
    , forall (V_Type 0) @@ fun typ1 ->
        forall (V_Type 0) @@ fun typ2 ->
        forall typ1 @@ fun x1 ->
        forall typ2 @@ fun x2 ->
        V_TyEq((x1, typ1), (x2, typ2))
        @-> V_TyEq((x2, typ2), (x1, typ1)) );
    ( "eq-comm"
    , forall (V_Type 0) @@ fun typ1 ->
        forall (V_Type 0) @@ fun typ2 ->
        forall (V_Type 0) @@ fun typ3 ->
        forall typ1 @@ fun x1 ->
        forall typ2 @@ fun x2 ->
        forall typ3 @@ fun x3 ->
        V_TyEq((x1, typ1), (x2, typ2))
        @-> V_TyEq((x2, typ2), (x3, typ3))
        @-> V_TyEq((x1, typ1), (x3, typ3)) );

    ( "funext"
    , forall (V_Type 0) @@ fun param_ty1 ->
        forall (V_Type 0) @@ fun param_ty2 ->
        forall (param_ty1 @-> V_Type 0) @@ fun ret_ty1 ->
        forall (param_ty2 @-> V_Type 0) @@ fun ret_ty2 ->
        forall (forall param_ty1 (value_apply ret_ty1)) @@ fun func1 ->
        forall (forall param_ty2 (value_apply ret_ty2)) @@ fun func2 ->
        ( forall param_ty1 @@ fun param1 ->
            forall param_ty2 @@ fun param2 ->
            V_TyEq((param1, param_ty1), (param2, param_ty2))
            @-> V_TyEq( (value_apply func1 param1, value_apply ret_ty1 param1)
                      , (value_apply func2 param2, value_apply ret_ty2 param2) ) )
        @-> V_TyEq( (func1, forall param_ty1 (value_apply ret_ty1))
                  , (func2, forall param_ty2 (value_apply ret_ty2)) )
    );
    ( "fun-arg-injective"
    , forall (V_Type 0) @@ fun param_ty1 ->
        forall (V_Type 0) @@ fun param_ty2 ->
        forall (param_ty1 @-> V_Type 0) @@ fun ret_ty1 ->
        forall (param_ty2 @-> V_Type 0) @@ fun ret_ty2 ->
        V_TyEq( (forall param_ty1 (value_apply ret_ty1), V_Type 0)
              , (forall param_ty2 (value_apply ret_ty2), V_Type 0) )
        @-> V_TyEq((param_ty1, V_Type 0), (param_ty2, V_Type 0)) );
    ( "fun-ret-injective"
    , forall (V_Type 0) @@ fun param_ty1 ->
        forall (V_Type 0) @@ fun param_ty2 ->
        forall (param_ty1 @-> V_Type 0) @@ fun ret_ty1 ->
        forall (param_ty2 @-> V_Type 0) @@ fun ret_ty2 ->
        V_TyEq( (forall param_ty1 (value_apply ret_ty1), V_Type 0)
              , (forall param_ty2 (value_apply ret_ty2), V_Type 0) )
        @-> (
            forall param_ty1 @@ fun param1 ->
            forall param_ty2 @@ fun param2 ->
            V_TyEq((param1, param_ty1), (param2, param_ty2))
            @-> V_TyEq( (value_apply ret_ty1 param1, V_Type 0)
                      , (value_apply ret_ty2 param2, V_Type 0))
        ) );

    ( "pairext"
    , forall (V_Type 0) @@ fun fst_ty1 ->
        forall (V_Type 0) @@ fun fst_ty2 ->
        forall (fst_ty1 @-> V_Type 0) @@ fun snd_ty1 ->
        forall (fst_ty2 @-> V_Type 0) @@ fun snd_ty2 ->
        forall (exists fst_ty1 (value_apply snd_ty1)) @@ fun pair1 ->
        forall (exists fst_ty2 (value_apply snd_ty2)) @@ fun pair2 ->
        let fst1 = value_proj pair1 `Fst in
        let fst2 = value_proj pair2 `Fst in
        V_TyEq((fst1, fst_ty1), (fst2, fst_ty2))
        @-> V_TyEq( (value_proj pair1 `Snd, value_apply snd_ty1 fst1)
                  , (value_proj pair2 `Snd, value_apply snd_ty2 fst2) )
        @-> V_TyEq( (pair1, exists fst_ty1 (value_apply snd_ty1))
                  , (pair2, exists fst_ty2 (value_apply snd_ty2)) ) );
    ( "pair-fst-injective"
    , forall (V_Type 0) @@ fun fst_ty1 ->
        forall (V_Type 0) @@ fun fst_ty2 ->
        forall (fst_ty1 @-> V_Type 0) @@ fun snd_ty1 ->
        forall (fst_ty2 @-> V_Type 0) @@ fun snd_ty2 ->
        V_TyEq( (exists fst_ty1 (value_apply snd_ty1), V_Type 0)
              , (exists fst_ty2 (value_apply snd_ty2), V_Type 0) )
        @-> V_TyEq((fst_ty1, V_Type 0), (fst_ty2, V_Type 0)) );
    ( "pair-snd-injective"
    , forall (V_Type 0) @@ fun fst_ty1 ->
        forall (V_Type 0) @@ fun fst_ty2 ->
        forall (fst_ty1 @-> V_Type 0) @@ fun snd_ty1 ->
        forall (fst_ty2 @-> V_Type 0) @@ fun snd_ty2 ->
        V_TyEq( (exists fst_ty1 (value_apply snd_ty1), V_Type 0)
              , (exists fst_ty2 (value_apply snd_ty2), V_Type 0) )
        @-> (
            forall fst_ty1 @@ fun fst1 ->
            forall fst_ty2 @@ fun fst2 ->
            V_TyEq((fst1, fst_ty1), (fst2, fst_ty2))
            @-> V_TyEq( (value_apply snd_ty1 fst1, V_Type 0)
                      , (value_apply snd_ty2 fst2, V_Type 0))
        ) );

    ( "coe-coherence"
    , forall (V_Type 0) @@ fun typ1 ->
        forall (V_Type 0) @@ fun typ2 ->
        forall typ1 @@ fun lhs ->
        forall (V_TyEq((typ1, V_Type 0), (typ2, V_Type 0))) @@ fun eq ->
        V_TyEq( (lhs, typ1)
              , (value_coe lhs (Lazy.from_val eq) typ1 typ2, typ2) ) )
]
