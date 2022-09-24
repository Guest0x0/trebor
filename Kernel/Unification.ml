
open Syntax
open Value
open Eval


type renaming =
    { dom : int
    ; cod : int
    ; map : (int * neutral) list }

let empty_renaming = { dom = 0; cod = 0; map = [] }

let add_boundvar ren =
    { dom = ren.dom + 1
    ; cod = ren.cod + 1
    ; map = (ren.dom, (Local ren.cod, EmptyElim)) :: ren.map }

exception CannotSolveYet
exception UnificationFailure


let elim_to_renaming level elim =
    let rec loop = function
        | EmptyElim ->
            (0, [])
        | App(elim', _, arg) ->
            let (cod, map) = loop elim' in
            (cod + 1, add_value arg (Local cod, EmptyElim) map)
        | Proj(_, _) ->
            raise RuntimeError

    and add_value value ((head, elim) as dst) map =
        match value with
        | Stuck(_, Local lvl, EmptyElim) when not (List.mem_assoc lvl map) ->
            (lvl, dst) :: map
        | Pair(fst, snd) ->
            let map = add_value fst (head, Proj(elim, `Fst)) map in
            add_value snd (head, Proj(elim, `Snd)) map
        | _ ->
            raise CannotSolveYet

    in
    let cod, map = loop elim in
    { dom = level; cod; map }



let rec rename_value g m ren typ value =
    match force g typ, force g value with
    | Type _, value ->
        rename_typ g m ren value

    | TyFun(name, _, a, b), _ ->
        let var = stuck_local ren.dom a in
        Core.Fun(name, rename_value g m (add_boundvar ren) (b var) (apply value var))

    | TyPair(_, a, b), _ ->
        let fst = project value `Fst in
        let snd = project value `Snd in
        Core.Pair(rename_value g m ren a fst, rename_value g m ren (b fst) snd)

    | (TyEq _ | Stuck _), Stuck(_, head, elim) ->
        rename_neutral g m ren head elim

    | _ ->
        raise RuntimeError


and rename_neutral g m ren head = function
    | EmptyElim ->
        begin match head with
        | Local lvl ->
            begin match List.assoc lvl ren.map with
            | (head, elim)        -> Quote.neutral_to_core g ren.cod head elim
            | exception Not_found -> raise CannotSolveYet
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
                  , rename_typ g m (add_boundvar ren) (b @@ stuck_local ren.dom a))
    | TyPair(name, a, b) ->
        Core.TyPair( name
                   , rename_typ g m ren a
                   , rename_typ g m (add_boundvar ren) (b @@ stuck_local ren.dom a))

    | TyEq((lhs, lhs_typ), (rhs, rhs_typ)) ->
        Core.TyEq( (rename_value g m ren lhs_typ lhs, rename_typ g m ren lhs_typ)
                 , (rename_value g m ren rhs_typ rhs, rename_typ g m ren rhs_typ) )

    | Stuck(_, head, elim) ->
        rename_neutral g m ren head elim

    | _ ->
        raise RuntimeError




let rec make_fun n body =
    if n = 0
    then body
    else make_fun (n - 1) (Core.Fun("", body))


let close_value g level typ value =
    let body = Quote.value_to_core g level typ value in
    Eval.eval g 0 [] @@ make_fun level body



let env_to_typ g level (env : Value.env) ret_typ =
    let add_entry (name, typ, kind) (ren, level, params) =
        match kind with
        | `Bound   -> ( add_boundvar ren
                      , level + 1
                      , (name, rename_typ g (-1) ren typ) :: params )
        | `Defined -> ( { ren with dom = ren.dom + 1 }
                      , level + 1
                      , params )
    in
    let ren, _, params = List.fold_right add_entry env (empty_renaming, 0, []) in
    let ret_typC = rename_typ g (-1) ren ret_typ in
    List.fold_left
        (fun body (name, param_typ) -> Core.TyFun(name, Explicit, param_typ, body))
        ret_typC params
    |> Eval.eval g 0 []


let env_to_elim level env =
    let args =
        env
        |> List.mapi (fun idx (_, typ, kind) -> typ, kind, stuck_local (level - idx - 1) typ)
        |> List.filter_map (fun (typ, kind, arg) -> if kind = `Bound then Some(typ, arg) else None)
    in
    List.fold_right (fun (typ, arg) elim -> App(elim, typ, arg)) args EmptyElim


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
                let fst_meta = g#fresh_meta (env_to_typ g level env fst_typ) in
                let fstV = Stuck(fst_typ, Meta("", fst_meta), env_to_elim level env) in
                let snd_typ = snd_typ fstV in
                let snd_meta = g#fresh_meta (env_to_typ g level env snd_typ) in
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





type equation =
    { level : int
    ; mode  : [`Value of value | `Type]
    ; lhs   : value
    ; rhs   : value }


class context = object(self)
    inherit Context.context

    val mutable equations = []


    method subtyp level v1 v2 =
        try self#unify_typ_aux `Subtyp level v1 v2
        with CannotSolveYet -> ()

    method unify_typ level v1 v2 =
        try self#unify_typ_aux `Equal level v1 v2
        with CannotSolveYet -> ()


    method solve_all =
        let rec make_progress not_yet =
            match equations with
            | [] ->
                equations <- not_yet;
                raise CannotSolveYet
            | eq :: eqs' ->
                let count0 = self#solved_count in
                equations <- eqs';
                let (finished, delta) = self#try_equation eq in
                if finished || self#solved_count > count0
                then equations <- List.rev_append not_yet @@ List.rev_append delta eqs'
                else make_progress (List.rev_append delta not_yet)
        in
        while equations <> [] do
            make_progress []
        done

    method private try_equation eq =
        let eqs0 = equations in
        equations <- [];
        try 
            begin match eq.mode with
            | `Value typ -> self#unify_value eq.level typ eq.lhs eq.rhs
            | `Type      -> self#unify_typ_aux `Equal eq.level eq.lhs eq.rhs
            end;
            let delta = equations in
            equations <- eqs0;
            (true, delta)
        with CannotSolveYet ->
            let delta = equations in
            equations <- eqs0;
            (false, delta)


    method dump_equations = equations


    method refine_to_function level env typ =
        match Eval.force self typ with
        | TyFun(_, Explicit, a, b) ->
            (a, b)
        | Stuck(Type ulevel, Meta _, _) ->
            let arg_meta = self#fresh_meta (env_to_typ self level env @@ Type ulevel) in
            let elim = env_to_elim level env in
            let a = Stuck(Type ulevel, Meta("", arg_meta), elim) in
            let env' = ("", a, `Bound) :: env in
            let ret_meta = self#fresh_meta (env_to_typ self (level + 1) env' @@ Type ulevel) in
            let b v = Stuck(Type ulevel, Meta("", ret_meta), App(elim, a, v)) in
            self#subtyp level typ (TyFun("", Explicit, a, b));
            (a, b)
        | _ ->
            raise UnificationFailure


    method refine_to_pair level env typ =
        match Eval.force self typ with
        | TyPair(_, a, b) ->
            (a, b)
        | Stuck(Type ulevel, Meta _, _) ->
            let fst_meta = self#fresh_meta (env_to_typ self level env @@ Type ulevel) in
            let elim = env_to_elim level env in
            let fst_typ = Stuck(Type ulevel, Meta("", fst_meta), elim) in
            let env' = ("", fst_typ, `Bound) :: env in
            let snd_meta = self#fresh_meta (env_to_typ self (level + 1) env' @@ Type ulevel) in
            let snd_typ v = Stuck(Type ulevel, Meta("", snd_meta), App(elim, fst_typ, v)) in
            self#subtyp level typ (TyPair("", fst_typ, snd_typ));
            (fst_typ, snd_typ)
        | _ ->
            raise UnificationFailure



    method private unify_value level typ v1 v2 =
        let v1 = force self v1 in
        let v2 = force self v2 in
        match force self typ, v1, v2 with
        | Type _, typv1, typv2 ->
            self#unify_typ_aux `Equal level typv1 typv2

        | TyFun(name, _, a, b), f1, f2 ->
            let var = stuck_local level a in
            self#unify_value (level + 1) (b var) (apply f1 var) (apply f2 var)

        | TyPair(_, a, b), p1, p2 ->
            let fst1 = project p1 `Fst in
            let fst2 = project p2 `Fst in
            self#unify_value level a fst1 fst2;
            self#unify_value level (b fst1) (project p1 `Snd) (project p2 `Snd)

        | TyEq _, _, _ ->
            ()

        | _, Stuck(_, Meta _, _), Stuck(_, Meta _, _) ->
            equations <- { level; mode = `Value typ; lhs = v1; rhs = v2 } :: equations;
            raise CannotSolveYet

        | _, Stuck(_, Meta(_, meta), elim), v
        | _, v, Stuck(_, Meta(_, meta), elim) ->
            begin try
                let meta, elim = decompose_pair self meta elim in
                let ren = elim_to_renaming level elim in
                let body = rename_value self meta ren typ v in
                let sol = make_fun ren.cod body in
                self#solve_meta meta (Eval.eval self 0 [] sol)
            with CannotSolveYet ->
                equations <- { level; mode = `Value typ; lhs = v1; rhs = v2 } :: equations;
                raise CannotSolveYet
            end

        | Stuck _, Stuck(_, head1, elim1), Stuck(_, head2, elim2) ->
            self#unify_head level head1 head2;
            self#unify_elim level elim1 elim2

        | _ ->
            raise RuntimeError


    method private unify_head level head1 head2 =
        match head1, head2 with
        | TopVar(shift1, name1), TopVar(shift2, name2) when shift1 = shift2 && name1 = name2 ->
            ()
        | Local lvl1, Local lvl2 when lvl1 = lvl2 ->
            ()
        | Coe coe1, Coe coe2 when coe1.ulevel = coe2.ulevel ->
            self#unify_value level (Type coe1.ulevel) coe1.lhs coe2.lhs;
            self#unify_value level (Type coe1.ulevel) coe1.rhs coe2.rhs;
            self#unify_value level coe1.lhs coe1.coerced coe2.coerced
        | _ ->
            raise UnificationFailure


    method private unify_elim level elim1 elim2 =
        match elim1, elim2 with
        | EmptyElim, EmptyElim ->
            ()
        | App(elim1', arg_typ, arg1), App(elim2', _, arg2) ->
            self#unify_elim level elim1' elim2';
            self#unify_value level arg_typ arg1 arg2
        | Proj(elim1', field1), Proj(elim2', field2) when field1 = field2 ->
            self#unify_elim level elim1' elim2'
        | _ ->
            raise UnificationFailure



    method private unify_typ_aux (mode : [`Subtyp | `Equal]) level sub sup =
        let sub = force self sub in
        let sup = force self sup in
        match sub, sup with
        | Type ulevel1, Type ulevel2 ->
            begin match mode with
            | `Subtyp when ulevel1 <= ulevel2 -> ()
            | `Equal  when ulevel1 =  ulevel2 -> ()
            | _                               -> raise UnificationFailure
            end

        | TyFun(name, kind1, a1, b1), TyFun(_, kind2, a2, b2) when kind1 = kind2 ->
            self#unify_typ_aux mode level a2 a1;
            let var = stuck_local level a2 in
            self#unify_typ_aux mode (level + 1) (b1 var) (b2 var)

        | TyPair(name, a1, b1), TyPair(_, a2, b2) ->
            self#unify_typ_aux mode level a1 a2;
            let var = stuck_local level a1 in
            self#unify_typ_aux mode (level + 1) (b1 var) (b2 var)

        | TyEq((lhs1, lhs_typ1), (rhs1, rhs_typ1))
        , TyEq((lhs2, lhs_typ2), (rhs2, rhs_typ2)) ->
            self#unify_typ_aux mode level lhs_typ1 lhs_typ2;
            self#unify_typ_aux mode level rhs_typ1 rhs_typ2;
            self#unify_value level lhs_typ1 lhs1 lhs2;
            self#unify_value level rhs_typ1 rhs1 rhs2

        | Stuck(_, Meta _, _), Stuck(_, Meta _, _) ->
            equations <- { level; mode = `Type; lhs = sub; rhs = sup } :: equations;
            raise CannotSolveYet

        | Stuck(_, Meta(_, meta), elim), v
        | v, Stuck(_, Meta(_, meta), elim) ->
            begin try
                let meta, elim = decompose_pair self meta elim in
                let ren = elim_to_renaming level elim in
                let sol = make_fun ren.cod (rename_typ  self meta ren v) in
                self#solve_meta meta (Eval.eval self 0 [] sol)
            with CannotSolveYet ->
                equations <- { level; mode = `Type; lhs = sub; rhs = sup } :: equations;
                raise CannotSolveYet
            end

        | Stuck(_, head1, elim1), Stuck(_, head2, elim2) ->
            self#unify_head level head1 head2;
            self#unify_elim level elim1 elim2

        | _ ->
            raise UnificationFailure
end
