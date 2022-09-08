
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
          { target : value
          ; eq     : value Lazy.t
          ; lhs    : value
          ; rhs    : value }


type top_level_value =
    | V_Axiom of value
    | V_Def   of value * value



let app_axiom axiom args =
    V_Ne(List.fold_left (fun f arg -> N_App(f, arg)) (N_Axiom axiom) args)


let rec eval globals env core =
    match core with
    | C_TopVar v ->
        begin match Hashtbl.find globals v with
        | V_Axiom _     -> V_Ne(N_Axiom v)
        | V_Def(def, _) -> def
        end

    | C_Local i  -> List.nth env i

    | C_Type ulevel -> V_Type ulevel

    | C_TyFun(param_typ, ret_typ) ->
        V_TyFun( eval globals env param_typ
               , fun argv -> eval globals (argv :: env) ret_typ )

    | C_Fun body ->
        V_Fun(fun argv -> eval globals (argv :: env) body)

    | C_App(func, arg) ->
        value_apply (eval globals env func) (eval globals env arg)

    | C_TyPair(fst_typ, snd_typ) ->
        V_TyPair( eval globals env fst_typ
                , fun fst_v -> eval globals (fst_v :: env) snd_typ )
    | C_Pair(fst, snd) ->
        V_Pair(eval globals env fst, eval globals env snd)

    | C_Proj(pair, selector) ->
        value_proj (eval globals env pair) selector

    | C_TyEq((lhs, lhs_typ), (rhs, rhs_typ)) ->
        V_TyEq( (eval globals env lhs, eval globals env lhs_typ)
              , (eval globals env rhs, eval globals env rhs_typ))

    | C_Coe { target; eq; lhs; rhs } ->
        value_coe (eval globals env target) (lazy (eval globals env (Lazy.force eq)))
            (eval globals env lhs) (eval globals env rhs)

and value_apply func_v arg_v =
    match func_v with
    | V_Fun func   -> func arg_v
    | V_Ne neutral -> V_Ne(N_App(neutral, arg_v))
    | _            -> failwith "Core.runtime_error"

and value_proj pair_v field =
    match pair_v, field with
    | V_Pair(fstv, _), `Fst -> fstv
    | V_Pair(_, sndv), `Snd -> sndv
    | V_Ne neutral   , _    -> V_Ne(N_Proj(neutral, field))
    | _                     -> failwith "Core.runtime_error"


and value_coe target eq lhs rhs =
    match lhs, rhs with
    | V_Type ul1, V_Type ul2 when ul1 = ul2 ->
        target

    | V_TyFun(param_typ1, ret_typ1), V_TyFun(param_typ2, ret_typ2) ->
        let param_eq = lazy(app_axiom "eq-symm" [
                app_axiom "fun-param-injective"
                    [ param_typ1; param_typ2
                    ; V_Fun(ret_typ1); V_Fun(ret_typ2)
                    ; Lazy.force eq ]])
        in 
        let ret_eq = lazy(app_axiom "fun-ret-injective"
                [ param_typ1; param_typ2
                ; V_Fun(ret_typ1); V_Fun(ret_typ2)
                ; Lazy.force eq ])
        in
        V_Fun(fun param2 ->
            let param1 = value_coe param2 param_eq param_typ2 param_typ1 in
            let ret1 = value_apply target param1 in
            value_coe ret1
                (lazy(value_apply (value_apply (Lazy.force ret_eq) param1) param2))
                (ret_typ1 param1) (ret_typ2 param2))

    | V_TyPair(fst_typ1, snd_typ1), V_TyPair(fst_typ2, snd_typ2) ->
        let fst_eq = lazy(app_axiom "pair-fst-injective"
                [ fst_typ1; fst_typ2
                ; V_Fun(snd_typ1); V_Fun(snd_typ2)
                ; Lazy.force eq ])
        in
        let snd_eq = lazy(app_axiom "pair-snd-injective"
                [ fst_typ1; fst_typ2
                ; V_Fun(snd_typ1); V_Fun(snd_typ2)
                ; Lazy.force eq ])
        in
        let fst1 = value_proj target `Fst in
        let fst2 = value_coe fst1 fst_eq fst_typ1 fst_typ2 in
        V_Pair(
            fst2,
            value_coe (value_proj target `Snd)
                (lazy(List.fold_left value_apply (Lazy.force snd_eq)
                                [ fst1; fst2
                                ; app_axiom "coe-coherence"
                                        [fst_typ1; fst_typ2; fst1; Lazy.force fst_eq]]))
                (snd_typ1 fst1) (snd_typ2 fst2)
        )
    | _ ->
        V_Ne(N_Coe { target; eq; lhs; rhs })




let rec quote_value globals level env typ v =
    match typ, v with
    | V_Type _, _ ->
        fst (quote_typ globals level env v)
    | V_TyFun(a, b), _ ->
        let var = V_Ne(N_Level level) in
        C_Fun(quote_value globals (level + 1) (a :: env) (b var) (value_apply v var))
    | V_TyPair(a, b), _ ->
        let fstv = value_proj v `Fst in
        let sndv = value_proj v `Snd in
        C_Pair( quote_value globals level env a fstv
              , quote_value globals level env (b fstv) sndv)
    | (V_TyEq _ | V_Ne _), V_Ne neutral ->
        fst (quote_neutral globals level env neutral)
    | _ ->
        failwith "Core.Normalization.runtime_error"

and quote_typ globals level env v =
    match v with
    | V_Type ulevel ->
        C_Type ulevel, ulevel + 1
    | V_TyFun(a, b) ->
        let ca, ul_a = quote_typ globals level env a in
        let cb, ul_b = quote_typ globals (level + 1) (a :: env) (b @@ V_Ne(N_Level level)) in 
        C_TyFun(ca, cb), max ul_a ul_b
    | V_TyPair(a, b) ->
        let ca, ul_a = quote_typ globals level env a in
        let cb, ul_b = quote_typ globals (level + 1) (a :: env) (b @@ V_Ne(N_Level level)) in
        C_TyPair(ca, cb), max ul_a ul_b
    | V_TyEq((lhs, lhs_ty), (rhs, rhs_ty)) ->
        let c_lhs = quote_value globals level env lhs_ty lhs in
        let c_rhs = quote_value globals level env rhs_ty rhs in
        let c_lhs_ty, ul_lhs = quote_typ globals level env lhs_ty in
        let c_rhs_ty, ul_rhs = quote_typ globals level env rhs_ty in
        C_TyEq((c_lhs, c_lhs_ty), (c_rhs, c_rhs_ty)), max ul_lhs ul_rhs
    | V_Ne neutral ->
        begin match quote_neutral globals level env neutral with
        | c, V_Type ul -> c, ul
        | _            -> failwith "Core.Normalization.runtime_error"
        end
    | _ ->
        failwith "Core.Normalization.runtime_error"

and quote_neutral globals level env neutral =
    match neutral with
    | N_Level lvl ->
        let idx = level - lvl - 1 in
        C_Local idx, List.nth env idx
    | N_Axiom a ->
        let (V_Axiom typ | V_Def(_, typ)) = Hashtbl.find globals a in
        C_TopVar a, typ
    | N_App(ne_f, v_arg) ->
        begin match quote_neutral globals level env ne_f with
        | f, V_TyFun(a, b) -> C_App(f, quote_value globals level env a v_arg), b v_arg
        | _                -> failwith "Core.Normalization.runtime_error"
        end
    | N_Proj(ne_pair, field) ->
        begin match quote_neutral globals level env ne_pair, field with
        | (pair, V_TyPair(a, _)), `Fst -> C_Proj(pair, field), a
        | (pair, V_TyPair(a, b)), `Snd -> C_Proj(pair, field), b (V_Ne(N_Proj(ne_pair, `Fst)))
        | _                            -> failwith "Core.Normalization.runtime_error"
        end
    | N_Coe { target; eq; lhs; rhs } ->
        let c_lhs, ul_lhs = quote_typ globals level env lhs in
        let c_rhs, ul_rhs = quote_typ globals level env rhs in
        let c_eq = lazy(quote_value globals level env
                (V_TyEq((lhs, V_Type ul_lhs), (rhs, V_Type ul_rhs)))
                (Lazy.force eq))
        in
        let c_target = quote_value globals level env lhs target in
        C_Coe { target = c_target; eq = c_eq; lhs = c_lhs; rhs = c_rhs }, rhs
