
open Syntax
open Value
open Eval



let rec value_to_core g level env typ value =
    match force g typ, force g value with
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
        let (AxiomDecl typ | Definition(typ, _)) = g#find_global name in
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
    | Meta(name, meta) ->
        begin match g#find_meta meta with
        | Free typ  -> typ, Core.Meta(name, meta)
        | Solved _  -> raise RuntimeError
        end


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
    match force g typv with
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



module Simple = struct
    let rec value_to_core level = function
        | Stuck(head, elim) -> elim_to_core level (head_to_core level head) elim
        | Type ulevel       -> Core.Type ulevel

        | TyFun(name, a, b) ->
            Core.TyFun( name
                      , value_to_core level a
                      , value_to_core (level + 1) (b @@ stuck_local level) )
        | Fun(name, f) ->
            Core.Fun(name, value_to_core (level + 1) (f @@ stuck_local level))

        | TyPair(name, a, b) ->
            Core.TyPair( name
                       , value_to_core level a
                       , value_to_core (level + 1) (b @@ stuck_local level) )
        | Pair(fst, snd) ->
            Core.Pair(value_to_core level fst, value_to_core level snd)

        | TyEq((lhs, lhs_typ), (rhs, rhs_typ)) ->
            Core.TyEq( (value_to_core level lhs, value_to_core level lhs_typ)
                     , (value_to_core level rhs, value_to_core level rhs_typ) )

    and head_to_core level = function
        | TopVar(0, name) -> Core.TopVar name
        | TopVar(s, name) -> Core.Shift(s, Core.TopVar name)
        | Local lvl       -> Core.Local(level - lvl - 1)
        | Coe { ulevel; coerced; lhs; rhs; eq } ->
            Core.Coe { ulevel
                     ; coerced = value_to_core level coerced
                     ; lhs     = value_to_core level lhs
                     ; rhs     = value_to_core level rhs
                     ; eq      = lazy(value_to_core level @@ Lazy.force eq) }

        | Meta(name, meta) -> Core.Meta(name, meta)

    and elim_to_core level headC = function
        | EmptyElim       -> headC
        | App(elim', arg) -> Core.App(elim_to_core level headC elim', value_to_core level arg)
        | Proj(elim', f)  -> Core.Proj(elim_to_core level headC elim', f)
end
