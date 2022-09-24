
open Syntax
open Value
open Eval



let rec value_to_core g level typ value =
    match force g typ, force g value with
    | _, Stuck(_, head, elim) ->
        neutral_to_core g level head elim

    | Type _, _ ->
        snd (typ_to_core g level value)

    | TyFun(name, _, a, b), vf ->
        let var = stuck_local level a in
        Core.Fun(name, value_to_core g (level + 1) (b var) (apply g vf var))

    | TyPair(_, a, b), vp ->
        let fst = project g vp `Fst in
        let snd = project g vp `Snd in
        Core.Pair(value_to_core g level a fst, value_to_core g level (b fst) snd)

    | _ ->
        raise RuntimeError


and neutral_to_core g level head elim =
    match elim with
    | EmptyElim ->
        begin match head with
        | TopVar(0, name) -> Core.TopVar name
        | TopVar(s, name) -> Core.Shift(s, Core.TopVar name)
        | Local lvl       -> Core.Local(level - lvl - 1)
        | Coe { ulevel; coerced; lhs; rhs; eq } ->
            Core.Coe { ulevel
                     ; coerced = value_to_core g level lhs coerced
                     ; lhs     = value_to_core g level (Type ulevel) lhs
                     ; rhs     = value_to_core g level (Type ulevel) rhs
                     ; eq      = lazy(value_to_core g level
                               (TyEq((lhs, Type ulevel), (rhs, Type ulevel)))
                               (Lazy.force eq)) }
        | Meta(name, meta) ->
            Core.Meta(name, meta)
        end
    | App(elim', arg_typ, arg) ->
        Core.App(neutral_to_core g level head elim', value_to_core g level arg_typ arg)
    | Proj(elim', field) ->
        Core.Proj(neutral_to_core g level head elim', field)


and typ_to_core g level value =
    match force g value with
    | Type ulevel ->
        (ulevel + 1, Core.Type ulevel)
    | TyFun(name, kind, a, b) ->
        let ul_a, a_core = typ_to_core g level a in
        let ul_b, b_core = typ_to_core g (level + 1) (b @@ stuck_local level a) in
        max ul_a ul_b, Core.TyFun(name, kind, a_core, b_core)
    | TyPair(name, a, b) ->
        let ul_a, a_core = typ_to_core g level a in
        let ul_b, b_core = typ_to_core g (level + 1) (b @@ stuck_local level a) in
        max ul_a ul_b, Core.TyPair(name, a_core, b_core)
    | TyEq((lhs, lhs_typ), (rhs, rhs_typ)) ->
        let ul_lhs, lhs_typC = typ_to_core g level lhs_typ in
        let ul_rhs, rhs_typC = typ_to_core g level rhs_typ in
        ( max ul_lhs ul_rhs
        , Core.TyEq( (value_to_core g level lhs_typ lhs, lhs_typC)
                   , (value_to_core g level rhs_typ rhs, rhs_typC) ) )
    | Stuck(Type ulevel, head, elim) ->
        ulevel, neutral_to_core g level head elim

    | _ ->
        raise RuntimeError


let meta_info_to_core g = function
    | Free typ           -> Core.Free(snd @@ typ_to_core g 0 typ)
    | Solved(typ, value) -> Core.Solved(snd @@ typ_to_core g 0 typ, value_to_core g 0 typ value)


let env_to_core g env =
    let rec loop = function
        | [] ->
            (0, [])
        | (name, typ, kind) :: env' ->
            let level, core_env' = loop env' in
            let _, typC = typ_to_core g level typ in
            (level + 1, (name, typC, kind) :: core_env')
    in
    snd (loop env)
