
open Syntax
open Value
open Eval


let rec value_to_core g level value =
    match force g value with
    | Stuck(head, elim) ->
        elim_to_core g level (head_to_core g level head) elim
    | Type ulevel ->
        Core.Type ulevel

    | TyFun(name, kind, a, b) ->
        let a_core = value_to_core g level a in
        let b_core = value_to_core g (level + 1) (b @@ stuck_local level) in
        Core.TyFun(name, kind, a_core, b_core)
    | Fun(name, f) ->
        Core.Fun(name, value_to_core g (level + 1) (f @@ stuck_local level))

    | TyPair(name, a, b) ->
        let a_core = value_to_core g level a in
        let b_core = value_to_core g (level + 1) (b @@ stuck_local level) in
        Core.TyPair(name, a_core, b_core)
    | Pair(fst, snd) ->
        Core.Pair(value_to_core g level fst, value_to_core g level snd)

    | TyEq((lhs, lhs_typ), (rhs, rhs_typ)) ->
        TyEq( (value_to_core g level lhs, value_to_core g level lhs_typ)
            , (value_to_core g level rhs, value_to_core g level rhs_typ) )

and head_to_core g level = function
    | Local lvl       -> Core.Local(level - lvl - 1)
    | TopVar(0, name) -> Core.TopVar name
    | TopVar(s, name) -> Core.Shift(s, Core.TopVar name)
    | Coe coe         -> Core.Coe { ulevel  = coe.ulevel
                                  ; coerced = value_to_core g level coe.coerced
                                  ; lhs     = value_to_core g level coe.lhs
                                  ; rhs     = value_to_core g level coe.rhs
                                  ; eq      = lazy(value_to_core g level (Lazy.force coe.eq)) }
    | Meta m          -> Core.Meta m

and elim_to_core g level headC = function
    | EmptyElim          -> headC
    | App(elim', argv)   -> Core.App( elim_to_core g level headC elim'
                                    , value_to_core g level argv )
    | Proj(elim', field) -> Core.Proj(elim_to_core g level headC elim', field)




let meta_info_to_core g = function
    | Free typ           -> Core.Free(value_to_core g 0 typ)
    | Solved(typ, value) -> Core.Solved(value_to_core g 0 typ, value_to_core g 0 value)


let env_to_core g env =
    let rec loop = function
        | [] ->
            (0, [])
        | (bd, name, typ) :: env' ->
            let level, envC' = loop env' in
            let typC = value_to_core g level typ in
            level + 1, (bd, name, typC) :: envC'
    in
    snd (loop env)




let infer_head g level env = function
    | Local lvl ->
        let idx = level - lvl - 1 in
        let (_, _, typ) = List.nth env idx in
        typ, Core.Local idx
    | TopVar(s, name) ->
        let (AxiomDecl typ | Definition(typ, _)) = g#find_global name in
        typ s, if s = 0 then Core.TopVar name else Core.Shift(s, Core.TopVar name)
    | Coe { ulevel; coerced; lhs; rhs; eq } ->
        rhs, Core.Coe { ulevel
                      ; coerced = value_to_core g level coerced
                      ; lhs     = value_to_core g level lhs
                      ; rhs     = value_to_core g level rhs
                      ; eq      = lazy(value_to_core g level (Lazy.force eq)) }
    | Meta m ->
        let (Free typ | Solved(typ, _)) = g#find_meta m in
        typ, Core.Meta m

let rec infer_neutral g level env head elim =
    match elim with
    | EmptyElim ->
        infer_head g level env head
    | App(elim', argv) ->
        let typ, core = infer_neutral g level env head elim' in
        begin match force g typ with
        | TyFun(_, _, _, b) -> b argv, Core.App(core, value_to_core g level argv)
        | _                 -> raise RuntimeError
        end
    | Proj(elim', field) ->
        let typ, core = infer_neutral g level env head elim' in
        begin match force g typ, field with
        | TyPair(_, a, _), Fst -> (a                                , Core.Proj(core, field))
        | TyPair(_, _, b), Snd -> (b (Stuck(head, Proj(elim', Fst))), Core.Proj(core, field))
        | _                    -> raise RuntimeError
        end


let rec infer_ulevel g level env typ =
    match force g typ with
    | Type ulevel ->
        ulevel + 1, Core.Type ulevel
    | TyFun(name, kind, a, b) ->
        let var = stuck_local level in
        let a_ul, aC = infer_ulevel g level env a in
        let b_ul, bC = infer_ulevel g (level + 1) ((Bound, name, a) :: env) (b var) in
        max a_ul b_ul, Core.TyFun(name, kind, aC, bC)
    | TyPair(name, a, b) ->
        let var = stuck_local level in
        let a_ul, aC = infer_ulevel g level env a in
        let b_ul, bC = infer_ulevel g (level + 1) ((Bound, name, a) :: env) (b var) in
        max a_ul b_ul, Core.TyPair(name, aC, bC)
    | TyEq((lhs, lhs_typ), (rhs, rhs_typ)) ->
        let lhs_ul, lhs_typC = infer_ulevel g level env lhs_typ in
        let rhs_ul, rhs_typC = infer_ulevel g level env rhs_typ in
        ( max lhs_ul rhs_ul
        , Core.TyEq( (value_to_core g level lhs, lhs_typC)
                   , (value_to_core g level rhs, rhs_typC) ) )
    | Stuck(head, elim) ->
        let typ, core = infer_neutral g level env head elim in
        begin match force g typ with
        | Type ulevel -> ulevel, core
        | _           -> raise RuntimeError
        end
    | _ ->
        raise RuntimeError
