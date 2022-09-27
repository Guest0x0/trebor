
open Syntax
open Value
open Eval


type renaming =
    { dom       : int
    ; cod       : Value.env
    ; cod_level : int
    ; map       : (int * (value * value)) list }

let empty_renaming = { dom = 0; cod = []; cod_level = 0; map = [] }

let add_boundvar name typ ren =
    { dom       = ren.dom + 1
    ; cod       = (name, typ, `Bound) :: ren.cod
    ; cod_level = ren.cod_level + 1
    ; map       = (ren.dom, (typ, stuck_local ren.cod_level typ)) :: ren.map }

exception UnificationFailure


let elim_to_renaming g level elim =
    let rec loop = function
        | EmptyElim ->
            ([], 0, [])
        | App(elim', typ, arg) ->
            let (cod, cod_level, map) = loop elim' in
            ( ("", typ, `Bound) :: cod
            , cod_level + 1
            , add_value arg (stuck_local cod_level typ) map )
        | Proj(_, _) ->
            raise RuntimeError

    and add_value value dst map =
        match value with
        | Stuck(typ, Local lvl, EmptyElim) when not (List.mem_assoc lvl map) ->
            (lvl, (typ, dst)) :: map
        | Pair(fst, snd) ->
            let map = add_value fst (project g dst `Fst) map in
            add_value snd (project g dst `Snd) map
        | _ ->
            raise UnificationFailure

    in
    let cod, cod_level, map = loop elim in
    { dom = level; cod; cod_level; map }




let rec make_fun n body =
    if n = 0
    then body
    else make_fun (n - 1) (Core.Fun("", body))


let env_to_elim level env =
    let args =
        env
        |> List.mapi (fun idx (_, typ, kind) -> typ, kind, stuck_local (level - idx - 1) typ)
        |> List.filter_map (fun (typ, kind, arg) -> if kind = `Bound then Some(typ, arg) else None)
    in
    List.fold_right (fun (typ, arg) elim -> App(elim, typ, arg)) args EmptyElim


let rec restrict_env ~filter g env =
    let add_entry (name, typ, kind) (ren, level, env') =
        if filter level kind
        then
            ( add_boundvar name typ ren
            , level + 1
            , (name, rename_typ g (-1) ren typ, kind) :: env' )
        else
            ( { ren with dom = ren.dom + 1 }
            , level + 1
            , env' )
    in
    let ren, _, env' = List.fold_right add_entry env (empty_renaming, 0, []) in
    (ren, env')


and rename_value g m ren typ value =
    match force g typ, force g value with
    | Type _, value ->
        rename_typ g m ren value

    | _, Stuck(_, Meta(_, m'), _) when m' = m ->
        raise UnificationFailure

    | _, Stuck(typ, (Meta(_, m') as head), elim) ->
        let elim_ren = elim_to_renaming g ren.dom elim in
        let filter lvl _ =
            match List.assoc lvl elim_ren.map with
            | _, Stuck(_, Local lvl', _) -> List.mem_assoc lvl' ren.map
            | _                          -> false
        in
        let restrict_ren, restricted_envC = restrict_env ~filter g elim_ren.cod in
        if restrict_ren.cod_level = elim_ren.cod_level
        then rename_neutral g m ren head elim
        else
            let new_meta_typ =
                Eval.eval g 0 []
                @@ List.fold_left
                    (fun ret_typ (_, arg_typ, _) -> Core.TyFun("", Explicit, arg_typ, ret_typ))
                    (rename_typ g m restrict_ren typ) restricted_envC
            in
            let new_meta = g#fresh_meta new_meta_typ in
            let solution =
                Eval.eval g 0 []
                @@ make_fun elim_ren.cod_level
                @@ rename_neutral g m restrict_ren (Meta("", new_meta))
                @@ env_to_elim restrict_ren.cod_level restrict_ren.cod
            in
            g#solve_meta m' solution;
            rename_value g m ren typ (Eval.eliminate g solution elim)

    | _, Stuck(_, head, elim) ->
        rename_neutral g m ren head elim

    | TyFun(name, _, a, b), _ ->
        let var = stuck_local ren.dom a in
        Core.Fun(name, rename_value g m (add_boundvar name a ren) (b var) (apply g value var))

    | TyPair(_, a, b), _ ->
        let fst = project g value `Fst in
        let snd = project g value `Snd in
        Core.Pair(rename_value g m ren a fst, rename_value g m ren (b fst) snd)

    | _, value ->
        raise RuntimeError


and rename_neutral g m ren head = function
    | EmptyElim ->
        begin match head with
        | Local lvl ->
            begin match List.assoc lvl ren.map with
            | typ, value           -> Quote.value_to_core g ren.cod_level typ value
            | exception Not_found -> raise UnificationFailure
            end
        | Coe coe ->
            let universe = Type coe.ulevel in
            Core.Coe { ulevel  = coe.ulevel
                     ; coerced = rename_value g m ren coe.lhs coe.coerced
                     ; lhs     = rename_value g m ren universe coe.lhs
                     ; rhs     = rename_value g m ren universe coe.rhs
                     ; eq      = lazy(rename_value g m ren
                               (TyEq( (coe.lhs, universe), (coe.rhs, universe) ))
                               (Lazy.force coe.eq)) }
        | Meta(_, m') when m = m' ->
            raise UnificationFailure
        | head ->
            Quote.neutral_to_core g ren.dom head EmptyElim
        end
    | App(elim', arg_typ, arg) ->
        Core.App(rename_neutral g m ren head elim', rename_value g m ren arg_typ arg)
    | Proj(elim', field) ->
        Core.Proj(rename_neutral g m ren head elim', field)


and rename_typ g m ren value =
    match Eval.force g value with
    | Type ulevel ->
        Core.Type ulevel

    | TyFun(name, kind, a, b) ->
        Core.TyFun( name, kind
                  , rename_typ g m ren a
                  , rename_typ g m (add_boundvar name a ren) (b @@ stuck_local ren.dom a))
    | TyPair(name, a, b) ->
        Core.TyPair( name
                   , rename_typ g m ren a
                   , rename_typ g m (add_boundvar name a ren) (b @@ stuck_local ren.dom a))

    | TyEq((lhs, lhs_typ), (rhs, rhs_typ)) ->
        Core.TyEq( (rename_value g m ren lhs_typ lhs, rename_typ g m ren lhs_typ)
                 , (rename_value g m ren rhs_typ rhs, rename_typ g m ren rhs_typ) )

    | Stuck(_, head, elim) ->
        rename_neutral g m ren head elim

    | _ ->
        raise RuntimeError



let close_value g level typ value =
    let body = Quote.value_to_core g level typ value in
    Eval.eval g 0 [] @@ make_fun level body




let env_to_tyfun g (env : Value.env) ret_typ =
    let ren, env' = restrict_env ~filter:(fun _ kind -> kind = `Bound) g env in
    Eval.eval g 0 []
    @@ List.fold_left
        (fun ret_typ (name, arg_typ, _) -> Core.TyFun(name, Explicit, arg_typ, ret_typ))
        (rename_typ g (-1) ren ret_typ) env'



let decompose_pair g meta elim =
    let rec loop elim =
        match elim with
        | EmptyElim ->
            begin match g#find_meta meta with
            | Free typ -> typ, 0, [], meta, elim
            | _        -> raise RuntimeError
            end
        | App(elim', arg_typ, arg) ->
            let typ, level, env, meta', elim' = loop elim' in
            begin match typ with
            | TyFun(_, _, a, b) ->
                b arg, level + 1, ("", a, `Bound) :: env, meta', App(elim', a, arg)
            | _  ->
                raise RuntimeError
            end
        | Proj(elim', field) ->
            let typ, level, env, meta', elim' = loop elim' in
            begin match typ with
            | TyPair(_, fst_typ, snd_typ) ->
                let fst_meta = g#fresh_meta (env_to_tyfun g env fst_typ) in
                let fstV = Stuck(fst_typ, Meta("", fst_meta), env_to_elim level env) in
                let snd_typ = snd_typ fstV in
                let snd_meta = g#fresh_meta (env_to_tyfun g env snd_typ) in
                let sndV = Stuck(snd_typ, Meta("", snd_meta), env_to_elim level env) in
                g#solve_meta meta' (close_value g level typ @@ Pair(fstV, sndV));
                begin match field with
                | `Fst -> (fst_typ, level, env, fst_meta, elim')
                | `Snd -> (snd_typ, level, env, snd_meta, elim')
                end
            | _ ->
                raise RuntimeError
            end
    in
    let _, _, _, meta', elim' = loop elim in
    meta', elim'





let rec unify_value g level typ v1 v2 =
    match force g typ, force g v1, force g v2 with
    | Type _, typv1, typv2 ->
        unify_typ_aux `Equal g level typv1 typv2

    | TyFun(name, _, a, b), f1, f2 ->
        let var = stuck_local level a in
        unify_value g (level + 1) (b var) (apply g f1 var) (apply g f2 var)

    | TyPair(_, a, b), p1, p2 ->
        let fst1 = project g p1 `Fst in
        let fst2 = project g p2 `Fst in
        unify_value g level a fst1 fst2;
        unify_value g level (b fst1) (project g p1 `Snd) (project g p2 `Snd)

    | typ, Stuck(_, Meta(_, meta), elim), v
    | typ, v, Stuck(_, Meta(_, meta), elim) ->
        let meta, elim = decompose_pair g meta elim in
        let ren = elim_to_renaming g level elim in
        let body = rename_value g meta ren typ v in
        g#solve_meta meta (Eval.eval g 0 [] @@ make_fun ren.cod_level body)

    | TyEq _, _, _ ->
        ()

    | Stuck _, Stuck(_, head1, elim1), Stuck(_, head2, elim2) ->
        unify_head g level head1 head2;
        unify_elim g level elim1 elim2

    | _ ->
        raise RuntimeError


and unify_head g level head1 head2 =
    match head1, head2 with
    | TopVar(shift1, name1), TopVar(shift2, name2) when shift1 = shift2 && name1 = name2 ->
        ()
    | Local lvl1, Local lvl2 when lvl1 = lvl2 ->
        ()
    | Coe coe1, Coe coe2 when coe1.ulevel = coe2.ulevel ->
        unify_value g level (Type coe1.ulevel) coe1.lhs coe2.lhs;
        unify_value g level (Type coe1.ulevel) coe1.rhs coe2.rhs;
        unify_value g level coe1.lhs coe1.coerced coe2.coerced
    | _ ->
        raise UnificationFailure


and unify_elim g level elim1 elim2 =
    match elim1, elim2 with
    | EmptyElim, EmptyElim ->
        ()
    | App(elim1', arg_typ, arg1), App(elim2', _, arg2) ->
        unify_elim g level elim1' elim2';
        unify_value g level arg_typ arg1 arg2
    | Proj(elim1', field1), Proj(elim2', field2) when field1 = field2 ->
        unify_elim g level elim1' elim2'
    | _ ->
        raise UnificationFailure



and unify_typ_aux (mode : [`Subtyp | `Equal]) g level sub sup =
    match force g sub, force g sup with
    | Type ulevel1, Type ulevel2 ->
        begin match mode with
        | `Subtyp when ulevel1 <= ulevel2 -> ()
        | `Equal  when ulevel1 =  ulevel2 -> ()
        | _                               -> raise UnificationFailure
        end

    | TyFun(name, kind1, a1, b1), TyFun(_, kind2, a2, b2) when kind1 = kind2 ->
        unify_typ_aux mode g level a2 a1;
        let var = stuck_local level a2 in
        unify_typ_aux mode g (level + 1) (b1 var) (b2 var)

    | TyPair(name, a1, b1), TyPair(_, a2, b2) ->
        unify_typ_aux mode g level a1 a2;
        let var = stuck_local level a1 in
        unify_typ_aux mode g (level + 1) (b1 var) (b2 var)

    | TyEq((lhs1, lhs_typ1), (rhs1, rhs_typ1))
    , TyEq((lhs2, lhs_typ2), (rhs2, rhs_typ2)) ->
        unify_typ_aux mode g level lhs_typ1 lhs_typ2;
        unify_typ_aux mode g level rhs_typ1 rhs_typ2;
        unify_value g level lhs_typ1 lhs1 lhs2;
        unify_value g level rhs_typ1 rhs1 rhs2

    | Stuck(_, Meta(_, meta), elim), v
    | v, Stuck(_, Meta(_, meta), elim) ->
        let meta, elim = decompose_pair g meta elim in
        let ren = elim_to_renaming g level elim in
        let sol = make_fun ren.cod_level (rename_typ g meta ren v) in
        g#solve_meta meta (Eval.eval g 0 [] sol)

    | Stuck(_, head1, elim1), Stuck(_, head2, elim2) ->
        unify_head g level head1 head2;
        unify_elim g level elim1 elim2

    | _ ->
        raise UnificationFailure



let unify_typ g = unify_typ_aux `Equal  g
let subtyp    g = unify_typ_aux `Subtyp g



let refine_to_function g level env typ =
    match Eval.force g typ with
    | TyFun(_, Explicit, a, b) ->
        (a, b)
    | Stuck(Type ulevel, Meta _, _) ->
        let arg_meta = g#fresh_meta (env_to_tyfun g env @@ Type ulevel) in
        let elim = env_to_elim level env in
        let a = Stuck(Type ulevel, Meta("", arg_meta), elim) in
        let env' = ("", a, `Bound) :: env in
        let ret_meta = g#fresh_meta (env_to_tyfun g env' @@ Type ulevel) in
        let b v = Stuck(Type ulevel, Meta("", ret_meta), App(elim, a, v)) in
        subtyp g level typ (TyFun("", Explicit, a, b));
        (a, b)
    | _ ->
        raise UnificationFailure


let refine_to_pair g level env typ =
    match Eval.force g typ with
    | TyPair(_, a, b) ->
        (a, b)
    | Stuck(Type ulevel, Meta _, _) ->
        let fst_meta = g#fresh_meta (env_to_tyfun g env @@ Type ulevel) in
        let elim = env_to_elim level env in
        let fst_typ = Stuck(Type ulevel, Meta("", fst_meta), elim) in
        let env' = ("", fst_typ, `Bound) :: env in
        let snd_meta = g#fresh_meta (env_to_tyfun g env' @@ Type ulevel) in
        let snd_typ v = Stuck(Type ulevel, Meta("", snd_meta), App(elim, fst_typ, v)) in
        subtyp g level typ (TyPair("", fst_typ, snd_typ));
        (fst_typ, snd_typ)
    | _ ->
        raise UnificationFailure
