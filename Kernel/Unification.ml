
open Syntax
open Value
open Eval



let rec make_fun n body =
    if n = 0
    then body
    else make_fun (n - 1) (Core.Fun("", body))

let close_value g level value =
    Quote.value_to_core g level value
    |> make_fun level
    |> eval g 0 []


let env_to_elim level env =
    let args =
        env
        |> List.mapi (fun idx (kind, typ, _) -> kind, stuck_local (level - idx - 1))
        |> List.filter_map (function (Bound, arg) -> Some arg | _ -> None)
    in
    List.fold_right (fun arg elim -> App(elim, arg)) args EmptyElim





type renaming =
    { dom : int
    ; cod : int
    ; map : (int * value) list }

let empty_renaming = { dom = 0; cod = 0; map = [] }

let add_boundvar ren =
    { dom = ren.dom + 1
    ; cod = ren.cod + 1
    ; map = (ren.dom, stuck_local ren.cod) :: ren.map }

exception UnificationFailure



let rec invert_value g value dst ren =
    match force g value with
    | Stuck(Local lvl, EmptyElim) when not (List.mem_assoc lvl ren.map) ->
        { ren with map = (lvl, dst) :: ren.map }
    | Pair(fst, snd) ->
        let ren = invert_value g fst (project dst Fst) ren in
        invert_value g snd (project dst Snd) ren
    | _ ->
        raise UnificationFailure

let rec elim_to_renaming g level = function
    | EmptyElim ->
        { empty_renaming with dom = level }
    | App(elim', arg) ->
        let ren = elim_to_renaming g level elim' in
        invert_value g arg (stuck_local ren.cod) { ren with cod = ren.cod + 1 }
    | Proj(_, _) ->
        raise RuntimeError




let rec value_should_be_pruned g ren value =
    match force g value with
    | Stuck(Local lvl, EmptyElim) -> not (List.mem_assoc lvl ren.map)
    | Pair(fst, snd)              -> value_should_be_pruned g ren fst
                                     || value_should_be_pruned g ren snd
    | _                           -> raise UnificationFailure


let rec rename_value g m ren value =
    match force g value with
    | Stuck(Meta m', _) when m' = m ->
        raise UnificationFailure

    | Stuck(Meta m', elim) ->
        let (m', elim') = prune_meta g m' (value_should_be_pruned g ren) elim in
        rename_elim g m ren (Core.Meta m') elim'

    | Stuck(head, elim) ->
        rename_elim g m ren (rename_head g m ren head) elim

    | Type ulevel ->
        Core.Type ulevel

    | TyFun(name, kind, a, b) ->
        Core.TyFun( name, kind
                  , rename_value g m ren a
                  , rename_value g m (add_boundvar ren) (b @@ stuck_local ren.dom))

    | Fun(name, f) ->
        Core.Fun(name, rename_value g m (add_boundvar ren) (f @@ stuck_local ren.dom))

    | TyPair(name, a, b) ->
        Core.TyPair( name
                   , rename_value g m ren a
                   , rename_value g m (add_boundvar ren) (b @@ stuck_local ren.dom))

    | Pair(fst, snd) ->
        Core.Pair(rename_value g m ren fst, rename_value g m ren snd)

    | TyEq((lhs, lhs_typ), (rhs, rhs_typ)) ->
        Core.TyEq( (rename_value g m ren lhs, rename_value g m ren lhs_typ)
                 , (rename_value g m ren rhs, rename_value g m ren rhs_typ) )



and rename_head g m ren = function
    | Local lvl ->
        begin match List.assoc lvl ren.map with
        | value               -> Quote.value_to_core g ren.cod value
        | exception Not_found -> raise UnificationFailure
        end
    | Coe { ulevel; coerced; lhs; rhs; eq } ->
        Core.Coe { ulevel
                 ; coerced = rename_value g m ren coerced
                 ; lhs     = rename_value g m ren lhs
                 ; rhs     = rename_value g m ren rhs
                 ; eq      = lazy(rename_value g m ren @@ Lazy.force eq) }
    | head ->
        Quote.head_to_core g ren.dom head


and rename_elim g m ren headC = function
    | EmptyElim ->
        headC
    | App(elim', arg) ->
        Core.App(rename_elim g m ren headC elim', rename_value g m ren arg)
    | Proj(elim', field) ->
        Core.Proj(rename_elim g m ren headC elim', field)


and prune_meta g m f elim =
    let open struct
        type state =
            { result_typ    : typ
            ; env           : Core.env
            ; pruned_elim   : elimination
            ; new_meta_elim : elimination
            ; pruning_ren   : renaming }
    end in
    let rec loop typ elim =
        match elim with
        | EmptyElim ->
            { result_typ    = typ
            ; env           = []
            ; pruned_elim   = EmptyElim
            ; new_meta_elim = EmptyElim
            ; pruning_ren   = empty_renaming }
        | App(elim', argv) ->
            let state = loop typ elim' in
            begin match force g state.result_typ with
            | TyFun(name, _, a, b) ->
                if f argv
                then
                    { result_typ    = b (stuck_local state.pruning_ren.dom)
                    ; env           =
                          (Bound, name, rename_value g (-1) state.pruning_ren a) :: state.env
                    ; pruned_elim   = state.pruned_elim
                    ; new_meta_elim = state.new_meta_elim
                    ; pruning_ren   = { state.pruning_ren with dom = state.pruning_ren.dom + 1 } }
                else
                    { result_typ    = b (stuck_local state.pruning_ren.dom)
                    ; env           = state.env
                    ; pruned_elim   = App(state.pruned_elim, argv)
                    ; new_meta_elim = App( state.new_meta_elim
                                         , Stuck(Local state.pruning_ren.dom, EmptyElim) )
                    ; pruning_ren   = add_boundvar state.pruning_ren }
            | _ ->
                raise RuntimeError
            end
        | _ ->
            raise RuntimeError
    in
    let (Free typ | Solved(typ, _)) = g#find_meta m in
    let state = loop typ elim in
    if state.pruning_ren.dom = state.pruning_ren.cod
    then (m, elim)
    else
        let new_meta_typ =
            List.fold_left
                (fun ret_typ (_, name, typ) -> Core.TyFun(name, Explicit, typ, ret_typ))
                (rename_value g (-1) state.pruning_ren state.result_typ) state.env
            |> Eval.eval g 0 []
        in
        let new_meta = g#fresh_meta new_meta_typ in
        let solution =
            close_value g state.pruning_ren.dom
            @@ Stuck(Meta new_meta, state.new_meta_elim)
        in
        g#solve_meta m solution;
        (new_meta, state.pruned_elim)




let rec discard_defined_vars g env =
    match env with
    | [] ->
        ([], empty_renaming)
    | (kind, name, typ) :: env' ->
        let env', ren = discard_defined_vars g env' in
        match kind with
        | Bound   -> ( (kind, name, rename_value g (-1) ren typ) :: env', add_boundvar ren )
        | Defined -> (env', { ren with dom = ren.dom + 1 })


let env_to_tyfun g (env : Value.env) ret_typ =
    let env', ren = discard_defined_vars g env in
    Eval.eval g 0 []
    @@ List.fold_left
        (fun ret_typ (_, name, arg_typ) -> Core.TyFun(name, Explicit, arg_typ, ret_typ))
        (rename_value g (-1) ren ret_typ) env'




let decompose_pair g meta elim =
    let rec loop elim =
        match elim with
        | EmptyElim ->
            begin match g#find_meta meta with
            | Free typ -> typ, 0, [], meta, elim
            | _        -> raise RuntimeError
            end
        | App(elim', arg) ->
            let typ, level, env, meta', elim' = loop elim' in
            begin match Eval.force g typ with
            | TyFun(name, _, a, b) ->
                ( b (stuck_local level)
                , level + 1
                , (Bound, name, a) :: env
                , meta'
                , App(elim', arg) )
            | _  ->
                raise RuntimeError
            end
        | Proj(elim', field) ->
            let typ, level, env, meta', elim' = loop elim' in
            begin match typ with
            | TyPair(_, fst_typ, snd_typ) ->
                let fst_meta = g#fresh_meta (env_to_tyfun g env fst_typ) in
                let fstV = Stuck(Meta fst_meta, env_to_elim level env) in
                let snd_typ = snd_typ fstV in
                let snd_meta = g#fresh_meta (env_to_tyfun g env snd_typ) in
                let sndV = Stuck(Meta snd_meta, env_to_elim level env) in
                g#solve_meta meta' (close_value g level @@ Pair(fstV, sndV));
                begin match field with
                | Fst -> (fst_typ, level, env, fst_meta, elim')
                | Snd -> (snd_typ, level, env, snd_meta, elim')
                end
            | _ ->
                raise UnificationFailure
            end
    in
    let _, _, _, meta', elim' = loop elim in
    meta', elim'





let rec unify_value g level env typ v1 v2 =
    match force g typ, force g v1, force g v2 with
    | TyFun(name, _, a, b), f1, f2 ->
        let var = stuck_local level in
        unify_value g (level + 1) ((Bound, name, a) :: env) (b var)
            (apply f1 var) (apply f2 var)

    | TyPair(_, a, b), p1, p2 ->
        let fst1 = project p1 Fst in
        let fst2 = project p2 Fst in
        unify_value g level env a fst1 fst2;
        unify_value g level env (b fst1) (project p1 Snd) (project p2 Snd)

    | _, Stuck(Meta m1, elim1), Stuck(Meta m2, elim2) when m1 = m2 ->
        let (Free typ | Solved(typ, _)) = g#find_meta m1 in
        ignore (unify_elim g level env (Meta m1) typ elim1 elim2)

    | _, Stuck(Meta meta, elim), v
    | _, v, Stuck(Meta meta, elim) ->
        let meta, elim = decompose_pair g meta elim in
        let ren = elim_to_renaming g level elim in
        let body = rename_value g meta ren v in
        g#solve_meta meta (Eval.eval g 0 [] @@ make_fun ren.cod body)

    | TyEq _, _, _ ->
        ()

    | Type _, typv1, typv2 ->
        unify_typ_aux `Equal g level env typv1 typv2

    | Stuck _, Stuck(head1, elim1), Stuck(head2, elim2) ->
        let typ = unify_head g level env head1 head2 in
        ignore (unify_elim g level env head1 typ elim1 elim2)

    | _ ->
        raise RuntimeError


and unify_head g level env head1 head2 =
    match head1, head2 with
    | TopVar(shift1, name1), TopVar(shift2, name2) when shift1 = shift2 && name1 = name2 ->
        let (AxiomDecl typ | Definition(typ, _)) = g#find_global name1 in
        typ shift1
    | Local lvl1, Local lvl2 when lvl1 = lvl2 ->
        let (_, _, typ) = List.nth env (level - lvl1 - 1) in
        typ
    | Coe coe1, Coe coe2 when coe1.ulevel = coe2.ulevel ->
        unify_value g level env (Type coe1.ulevel) coe1.lhs coe2.lhs;
        unify_value g level env (Type coe1.ulevel) coe1.rhs coe2.rhs;
        unify_value g level env coe1.lhs coe1.coerced coe2.coerced;
        coe1.rhs
    | _ ->
        raise UnificationFailure


and unify_elim g level env head head_typ elim1 elim2 =
    match elim1, elim2 with
    | EmptyElim, EmptyElim ->
        head_typ
    | App(elim1', arg1), App(elim2', arg2) ->
        begin match force g @@ unify_elim g level env head head_typ elim1' elim2' with
        | TyFun(_, _, a, b) -> unify_value g level env a arg1 arg2; b arg1
        | _                 -> raise RuntimeError
        end
    | Proj(elim1', field1), Proj(elim2', field2) when field1 = field2 ->
        begin match force g @@ unify_elim g level env head head_typ elim1' elim2', field1 with
        | TyPair(_, a, _), Fst -> a
        | TyPair(_, _, b), Snd -> b (Stuck(head, Proj(elim1', Fst)))
        | _                    -> raise RuntimeError
        end
    | _ ->
        raise UnificationFailure



and unify_typ_aux (mode : [`Subtyp | `Equal]) g level env sub sup =
    match force g sub, force g sup with
    | Type ulevel1, Type ulevel2 ->
        begin match mode with
        | `Subtyp when ulevel1 <= ulevel2 -> ()
        | `Equal  when ulevel1 =  ulevel2 -> ()
        | _                               -> raise UnificationFailure
        end

    | TyFun(name, kind1, a1, b1), TyFun(_, kind2, a2, b2) when kind1 = kind2 ->
        unify_typ_aux mode g level env a2 a1;
        let var = stuck_local level in
        unify_typ_aux mode g (level + 1) ((Bound, name, a2) :: env) (b1 var) (b2 var)

    | TyPair(name, a1, b1), TyPair(_, a2, b2) ->
        unify_typ_aux mode g level env a1 a2;
        let var = stuck_local level in
        unify_typ_aux mode g (level + 1) ((Bound, name, a1) :: env) (b1 var) (b2 var)

    | TyEq((lhs1, lhs_typ1), (rhs1, rhs_typ1))
    , TyEq((lhs2, lhs_typ2), (rhs2, rhs_typ2)) ->
        unify_typ_aux mode g level env lhs_typ1 lhs_typ2;
        unify_typ_aux mode g level env rhs_typ1 rhs_typ2;
        unify_value g level env lhs_typ1 lhs1 lhs2;
        unify_value g level env rhs_typ1 rhs1 rhs2

    | Stuck(Meta m1, elim1), Stuck(Meta m2, elim2) when m1 = m2 ->
        let (Free typ | Solved(typ, _)) = g#find_meta m1 in
        ignore (unify_elim g level env (Meta m1) typ elim1 elim2)

    | Stuck(Meta meta, elim), v
    | v, Stuck(Meta meta, elim) ->
        let meta, elim = decompose_pair g meta elim in
        let ren = elim_to_renaming g level elim in
        let body = rename_value g meta ren v in
        g#solve_meta meta (Eval.eval g 0 [] @@ make_fun ren.cod body)

    | Stuck(head1, elim1), Stuck(head2, elim2) ->
        let typ = unify_head g level env head1 head2 in
        ignore (unify_elim g level env head1 typ elim1 elim2)

    | _ ->
        raise UnificationFailure



let unify_typ g = unify_typ_aux `Equal  g
let subtyp    g = unify_typ_aux `Subtyp g



let refine_to_function g level env typ =
    match Eval.force g typ with
    | TyFun(_, Explicit, a, b) ->
        (a, b)
    (*
    | Stuck(Meta _, _) ->
        let arg_meta = g#fresh_meta (env_to_tyfun g env @@ Type ulevel) in
        let elim = env_to_elim level env in
        let a = Stuck(Type ulevel, Meta("", arg_meta), elim) in
        let env' = ("", a, `Bound) :: env in
        let ret_meta = g#fresh_meta (env_to_tyfun g env' @@ Type ulevel) in
        let b v = Stuck(Type ulevel, Meta("", ret_meta), App(elim, a, v)) in
        subtyp g level typ (TyFun("", Explicit, a, b));
        (a, b)
   *)
    | _ ->
        raise UnificationFailure


let refine_to_pair g level env typ =
    match Eval.force g typ with
    | TyPair(_, a, b) ->
        (a, b)
    (*
    | Stuck(Type ulevel, Meta _, _) ->
        let fst_meta = g#fresh_meta (env_to_tyfun g env @@ Type ulevel) in
        let elim = env_to_elim level env in
        let fst_typ = Stuck(Type ulevel, Meta("", fst_meta), elim) in
        let env' = ("", fst_typ, `Bound) :: env in
        let snd_meta = g#fresh_meta (env_to_tyfun g env' @@ Type ulevel) in
        let snd_typ v = Stuck(Type ulevel, Meta("", snd_meta), App(elim, fst_typ, v)) in
        subtyp g level typ (TyPair("", fst_typ, snd_typ));
        (fst_typ, snd_typ)
   *)
    | _ ->
        raise UnificationFailure
