
open Syntax


type value =
    | V_Ne of neutral

    | V_Type  of int

    | V_TyFun of value * (value -> value)
    | V_Fun   of (value -> value)

    | V_TyPair of value * (value -> value)
    | V_Pair   of value * value

    | V_TyEq  of (value * value) * (value * value)

and neutral =
    | N_Axiom of string
    | N_Level of int
    | N_App   of neutral * value
    | N_Proj  of neutral * [`Fst | `Snd]
    | N_Coe   of
          { origin : value
          ; eq     : value Lazy.t
          ; lhs    : value
          ; rhs    : value }


type top_level_value =
    | V_Axiom of value
    | V_Def   of value * value



let app_axiom a args =
    V_Ne(List.fold_left (fun f arg -> N_App(f, arg)) (N_Axiom a) args)


let rec eval top env core =
    match core with
    | C_TopVar v ->
        begin match Hashtbl.find top v with
        | V_Axiom _     -> V_Ne(N_Axiom v)
        | V_Def(def, _) -> def
        end
    | C_Local i  -> List.nth env i

    | C_Type level -> V_Type level

    | C_TyFun(param_ty, ret_ty) -> V_TyFun( eval top env param_ty
                                          , fun argv -> eval top (argv :: env) ret_ty )
    | C_Fun body                -> V_Fun(fun argv -> eval top (argv :: env) body)
    | C_App(func, arg)          -> value_apply (eval top env func) (eval top env arg)

    | C_TyPair(fst_ty, snd_ty) -> V_TyPair( eval top env fst_ty
                                          , fun fstv -> eval top (fstv :: env) snd_ty )
    | C_Pair(fst, snd)         -> V_Pair(eval top env fst, eval top env snd)
    | C_Proj(pair, selector)   -> value_proj (eval top env pair) selector

    | C_TyEq((lhs, lhs_ty), (rhs, rhs_ty)) ->
        V_TyEq( (eval top env lhs, eval top env lhs_ty)
              , (eval top env rhs, eval top env rhs_ty))
    | C_Coe { origin; eq; lhs; rhs } ->
        value_coe (eval top env origin) (lazy (eval top env (Lazy.force eq)))
            (eval top env lhs) (eval top env rhs)

and value_apply func_v arg_v =
    match func_v with
    | V_Fun func   -> func arg_v
    | V_Ne neutral -> V_Ne(N_App(neutral, arg_v))
    | _            -> failwith "Core.runtime_error"

and value_proj pairv selector =
    match pairv, selector with
    | V_Pair(fstv, _), `Fst -> fstv
    | V_Pair(_, sndv), `Snd -> sndv
    | V_Ne neutral   , _    -> V_Ne(N_Proj(neutral, selector))
    | _                     -> failwith "Core.runtime_error"


and value_coe origin eq lhs rhs =
    match lhs, rhs with
    | V_Type l1, V_Type l2 when l1 = l2 ->
        origin
    | V_TyFun(param_ty1, ret_ty1), V_TyFun(param_ty2, ret_ty2) ->
        let param_eq = lazy(app_axiom "eq-symm" [
                app_axiom "fun-arg-injective"
                    [ param_ty1; param_ty2
                    ; V_Fun(ret_ty1); V_Fun(ret_ty2)
                    ; Lazy.force eq ]])
        in 
        let ret_eq = lazy(app_axiom "fun-ret-injective"
                [ param_ty1; param_ty2
                ; V_Fun(ret_ty1); V_Fun(ret_ty2)
                ; Lazy.force eq ])
        in
        V_Fun(fun param2 ->
            let param1 = value_coe param2 param_eq param_ty2 param_ty1 in
            let ret1 = value_apply origin param1 in
            value_coe ret1
                (lazy(value_apply (value_apply (Lazy.force ret_eq) param1) param2))
                (ret_ty1 param1) (ret_ty2 param2)
        )
    | V_TyPair(fst_ty1, snd_ty1), V_TyPair(fst_ty2, snd_ty2) ->
        let fst_eq = lazy(app_axiom "pair-fst-injective"
                [ fst_ty1; fst_ty2
                ; V_Fun(snd_ty1); V_Fun(snd_ty2)
                ; Lazy.force eq ])
        in
        let snd_eq = lazy(app_axiom "pair-snd-injective"
                [ fst_ty1; fst_ty2
                ; V_Fun(snd_ty1); V_Fun(snd_ty2)
                ; Lazy.force eq ])
        in
        let fst_v1 = value_proj origin `Fst in
        let fst_v2 = value_coe fst_v1 fst_eq fst_ty1 fst_ty2 in
        V_Pair(
            fst_v2,
            value_coe (value_proj origin `Snd)
                (lazy(List.fold_left value_apply (Lazy.force snd_eq)
                                [ fst_v1; fst_v2
                                ; app_axiom "coe-coherence"
                                        [fst_ty1; fst_ty2; fst_v1; Lazy.force fst_eq]]))
                (snd_ty1 fst_v1) (snd_ty2 fst_v2)
        )
    | _ ->
        V_Ne(N_Coe { origin; eq; lhs; rhs })




let rec quote_value axioms level env typ v =
    match typ, v with
    | V_Type _, _ ->
        fst (quote_typ axioms level env v)
    | V_TyFun(a, b), _ ->
        let var = V_Ne(N_Level level) in
        C_Fun(quote_value axioms (level + 1) (a :: env) (b var) (value_apply v var))
    | V_TyPair(a, b), _ ->
        let fstv = value_proj v `Fst in
        let sndv = value_proj v `Snd in
        C_Pair( quote_value axioms level env a fstv
              , quote_value axioms level env (b fstv) sndv)
    | (V_TyEq _ | V_Ne _), V_Ne neutral ->
        fst (quote_neutral axioms level env neutral)
    | _ ->
        failwith "Core.Normalization.runtime_error"

and quote_typ axioms level env v =
    match v with
    | V_Type ulevel ->
        C_Type ulevel, ulevel + 1
    | V_TyFun(a, b) ->
        let ca, ul_a = quote_typ axioms level env a in
        let cb, ul_b = quote_typ axioms (level + 1) (a :: env) (b @@ V_Ne(N_Level level)) in 
        C_TyFun(ca, cb), max ul_a ul_b
    | V_TyPair(a, b) ->
        let ca, ul_a = quote_typ axioms level env a in
        let cb, ul_b = quote_typ axioms (level + 1) (a :: env) (b @@ V_Ne(N_Level level)) in
        C_TyPair(ca, cb), max ul_a ul_b
    | V_TyEq((lhs, lhs_ty), (rhs, rhs_ty)) ->
        let c_lhs = quote_value axioms level env lhs_ty lhs in
        let c_rhs = quote_value axioms level env rhs_ty rhs in
        let c_lhs_ty, ul_lhs = quote_typ axioms level env lhs_ty in
        let c_rhs_ty, ul_rhs = quote_typ axioms level env rhs_ty in
        C_TyEq((c_lhs, c_lhs_ty), (c_rhs, c_rhs_ty)), max ul_lhs ul_rhs
    | V_Ne neutral ->
        begin match quote_neutral axioms level env neutral with
        | c, V_Type ul -> c, ul
        | _            -> failwith "Core.Normalization.runtime_error"
        end
    | _ ->
        failwith "Core.Normalization.runtime_error"

and quote_neutral axioms level env neutral =
    match neutral with
    | N_Level lvl ->
        let idx = level - lvl - 1 in
        C_Local idx, List.nth env idx
    | N_Axiom a ->
        let (V_Axiom typ | V_Def(_, typ)) = Hashtbl.find axioms a in
        C_TopVar a, typ
    | N_App(ne_f, v_arg) ->
        begin match quote_neutral axioms level env ne_f with
        | f, V_TyFun(a, b) -> C_App(f, quote_value axioms level env a v_arg), b v_arg
        | _                -> failwith "Core.Normalization.runtime_error"
        end
    | N_Proj(ne_pair, field) ->
        begin match quote_neutral axioms level env ne_pair, field with
        | (pair, V_TyPair(a, _)), `Fst -> C_Proj(pair, field), a
        | (pair, V_TyPair(a, b)), `Snd -> C_Proj(pair, field), b (V_Ne(N_Proj(ne_pair, `Fst)))
        | _                            -> failwith "Core.Normalization.runtime_error"
        end
    | N_Coe { origin; eq; lhs; rhs } ->
        let c_lhs, ul_lhs = quote_typ axioms level env lhs in
        let c_rhs, ul_rhs = quote_typ axioms level env rhs in
        let c_eq = lazy(quote_value axioms level env
                (V_TyEq((lhs, V_Type ul_lhs), (rhs, V_Type ul_rhs)))
                (Lazy.force eq))
        in
        let c_origin = quote_value axioms level env lhs origin in
        C_Coe { origin = c_origin; eq = c_eq; lhs = c_lhs; rhs = c_rhs }, rhs
