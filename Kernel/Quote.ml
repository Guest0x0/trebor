
open Syntax
open Value
open Eval



let rec value_to_core g level env typ value =
    match typ, value with
    | Type _, typv ->
        snd (typ_to_core g level env typv)

    | TyFun(name, a, b), vf ->
        let var = stuck_local level in
        Core.Fun(name, value_to_core g (level + 1) ((name, a) :: env) (b var) (apply vf var))

    | TyPair(_, a, b), vp ->
        let fst = project vp `Fst in
        let snd = project vp `Snd in
        Core.Pair(value_to_core g level env a fst, value_to_core g level env (b fst) snd)

    | (TyEq _ | Stuck _), Stuck(head, elim) ->
        snd (elim_to_core g level env head elim)

    | _ ->
        raise RuntimeError



and head_to_core g level env head =
    match head with
    | TopVar(shift, name) ->
        let (AxiomDecl typ | Definition(typ, _)) = Hashtbl.find g name in
        if shift = 0
        then typ, Core.TopVar name
        else typ, Core.Shift(shift, Core.TopVar name)
    | Local lvl ->
        let idx = level - lvl - 1 in
        snd (List.nth env idx), Core.Local idx
    | Coe { ulevel; coerced; lhs; rhs; eq } ->
        ( rhs
        , Core.Coe { ulevel
                   ; coerced = value_to_core g level env lhs coerced
                   ; lhs     = value_to_core g level env (Type ulevel) lhs
                   ; rhs     = value_to_core g level env (Type ulevel) rhs
                   ; eq      = lazy(value_to_core g level env
                             (TyEq((lhs, Type ulevel), (rhs, Type ulevel)))
                             (Lazy.force eq)) } )


and elim_to_core g level env head elim =
    match elim with
    | EmptyElim ->
        head_to_core g level env head
    | App(elim', arg) ->
        begin match elim_to_core g level env head elim' with
        | TyFun(_, a, b), func -> b arg, Core.App(func, value_to_core g level env a arg)
        | _                    -> raise RuntimeError
        end
    | Proj(elim', field) ->
        begin match elim_to_core g level env head elim' with
        | TyPair(_, a, b), pair ->
            begin match field with
            | `Fst -> a, Core.Proj(pair, field)
            | `Snd ->
                let fst = Stuck(head, Proj(elim', `Fst)) in
                b fst, Core.Proj(pair, field)
            end
        | _ ->
            raise RuntimeError
        end


and typ_to_core g level env typv =
    match typv with
    | Type ulevel ->
        ( ulevel + 1, Core.Type ulevel )
    | TyFun(name, a, b) ->
        let ul_a, a_core = typ_to_core g level env a in
        let ul_b, b_core = typ_to_core g (level + 1) ((name, a) :: env) (b @@ stuck_local level) in
        ( max ul_a ul_b, Core.TyFun(name, a_core, b_core) )
    | TyPair(name, a, b) ->
        let ul_a, a_core = typ_to_core g level env a in
        let ul_b, b_core = typ_to_core g (level + 1) ((name, a) :: env) (b @@ stuck_local level) in
        ( max ul_a ul_b, Core.TyPair(name, a_core, b_core) )
    | TyEq((lhs, lhs_typ), (rhs, rhs_typ)) ->
        let ul_lhs, lhs_typC = typ_to_core g level env lhs_typ in
        let ul_rhs, rhs_typC = typ_to_core g level env rhs_typ in
        ( max ul_lhs ul_rhs
        , Core.TyEq( (value_to_core g level env lhs_typ lhs, lhs_typC)
                   , (value_to_core g level env rhs_typ rhs, rhs_typC) ) )
    | Stuck(head, elim) ->
        begin match elim_to_core g level env head elim with
        | Type ulevel, core -> ulevel, core
        | _                 -> raise RuntimeError
        end
    | _ ->
        raise RuntimeError


let env_to_core_ctx g env =
    let rec loop = function
        | [] ->
            (0, [])
        | (name, typ) :: env' ->
            let level, core_ctx' = loop env' in
            let _, typC = typ_to_core g level env' typ in
            (level + 1, (name, typC) :: core_ctx')
    in
    snd (loop env)
