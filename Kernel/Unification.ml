
open Syntax
open Value
open Eval



let abstract_env env ret_typ =
    List.fold_left
        (fun typ (_, param_typ, kind) ->
                    match kind with
                    | `Defined -> typ
                    | `Bound   -> Value.TyFun("", param_typ, Fun.const typ))
        ret_typ env

let apply_env f env =
    let args =
        env
        |> List.mapi (fun lvl (_, _, kind) -> kind, Value.stuck_local lvl)
        |> List.filter_map (fun (kind, arg) -> if kind = `Bound then Some arg else None)
    in
    List.fold_left Eval.apply f args


let rec make_fun n body =
    if n = 0
    then body
    else make_fun (n - 1) (Core.Fun("", body))

let rec abstract_elim elim body =
    match elim with
    | EmptyElim     -> body
    | App(elim', _) -> abstract_elim elim' (Fun("", Fun.const body))
    | Proj _        -> raise RuntimeError


let rec decompose_pair g meta elim =
    match elim with
    | EmptyElim ->
        begin match g#find_meta meta with
        | Free typ -> typ, meta, elim
        | _        -> raise RuntimeError
        end
    | App(elim', arg) ->
        let typ, meta', elim' = decompose_pair g meta elim' in
        begin match typ with
        | TyFun(_, a, b) -> b arg, meta', App(elim', arg)
        | _              -> raise RuntimeError
        end
    | Proj(elim', field) ->
        let typ, meta', elim' = decompose_pair g meta elim' in
        begin match typ with
        | TyPair(_, fst_typ, snd_typ) ->
            let fst_meta = g#fresh_meta (abstract_elim elim' fst_typ) in
            let fstV = Stuck(Meta("", fst_meta), elim') in
            let snd_typ = snd_typ fstV in
            let snd_meta = g#fresh_meta (abstract_elim elim' snd_typ) in
            let sndV = Stuck(Meta("", snd_meta), elim') in
            g#solve_meta meta' (abstract_elim elim' @@ Pair(fstV, sndV));
            begin match field with
            | `Fst -> (fst_typ, fst_meta, elim')
            | `Snd -> (snd_typ, snd_meta, elim')
            end
        | _ ->
            raise RuntimeError
        end



type renaming =
    { dom : int
    ; cod : int
    ; map : (int * value) list }

let add_boundvar ren =
    { dom = ren.dom + 1
    ; cod = ren.cod + 1
    ; map = (ren.dom, stuck_local ren.cod) :: ren.map }



exception CannotSolveYet
exception UnificationFailure

let elim_to_renaming level elim =
    let rec loop = function
        | EmptyElim ->
            (0, [])
        | App(elim', arg) ->
            let (cod, map) = loop elim' in
            (cod + 1, add_value arg (stuck_local cod) map)
        | Proj(_, _) ->
            raise RuntimeError

    and add_value value dst map =
        match value with
        | Stuck(Local lvl, EmptyElim) when not (List.mem_assoc lvl map) ->
            (lvl, dst) :: map
        | Pair(fst, snd) ->
            let map = add_value fst (project dst `Fst) map in
            add_value snd (project dst `Snd) map
        | _ ->
            raise CannotSolveYet

    in
    let cod, map = loop elim in
    { dom = level; cod; map }



let rec rename_value g m ren value =
    match force g value with
    | Stuck(head, elim) ->
        let headC = rename_head g m ren head in
        rename_elim g m ren headC elim
    | Type ulevel ->
        Core.Type ulevel

    | TyFun(name, a, b) ->
        Core.TyFun(name, rename_value g m ren a, rename_func g m ren b)
    | Fun(name, f) ->
        Core.Fun(name, rename_func g m ren f)

    | TyPair(name, a, b) ->
        Core.TyPair(name, rename_value g m ren a, rename_func g m ren b)
    | Pair(fst, snd) ->
        Pair(rename_value g m ren fst, rename_value g m ren snd)

    | TyEq((lhs, lhs_typ), (rhs, rhs_typ)) ->
        Core.TyEq( (rename_value g m ren lhs, rename_value g m ren lhs_typ)
                 , (rename_value g m ren rhs, rename_value g m ren rhs_typ) )


and rename_func g m ren f =
    rename_value g m (add_boundvar ren) (f @@ stuck_local ren.dom)

and rename_head g m ren = function
    | Local lvl ->
        begin match List.assoc lvl ren.map with
        | value               -> Quote.Simple.value_to_core ren.cod value
        | exception Not_found -> raise CannotSolveYet
        end
    | Coe coe ->
        Core.Coe { ulevel  = coe.ulevel
                 ; coerced = rename_value g m ren coe.coerced
                 ; lhs     = rename_value g m ren coe.lhs
                 ; rhs     = rename_value g m ren coe.rhs
                 ; eq      = lazy(rename_value g m ren @@ Lazy.force coe.eq) }
    | Meta(_, m') when m = m' ->
        raise UnificationFailure
    | head ->
        Quote.Simple.head_to_core ren.dom head

and rename_elim g m ren headC = function
    | EmptyElim ->
        headC
    | App(elim', arg) ->
        Core.App(rename_elim g m ren headC elim', rename_value g m ren arg)
    | Proj(elim', field) ->
        Core.Proj(rename_elim g m ren headC elim', field)







class context = object(self)
    inherit Context.context

    val mutable equations = []
    val mutable progressed = false


    method subtyp level (env : Value.env) v1 v2 =
        try self#unify_typ_aux `Subtyp level env v1 v2
        with CannotSolveYet -> ()

    method unify_typ level (env : Value.env) v1 v2 =
        try self#unify_typ_aux `Equal level env v1 v2
        with CannotSolveYet -> ()


    method solve_all =
        let rec make_progress not_yet eqs =
            match eqs with
            | [] ->
                raise CannotSolveYet
            | eq :: eqs' ->
                progressed <- false;
                equations <- [];
                try
                    eq ();
                    equations <- List.rev_append not_yet eqs'
                with CannotSolveYet ->
                    if progressed
                    then equations <- List.rev_append not_yet eqs'
                    else make_progress (List.rev_append equations not_yet) eqs'
        in
        while equations <> [] do
            make_progress [] equations
        done


    method private unify_value level env typ v1 v2 =
        match force self typ, force self v1, force self v2 with
        | Type _, typv1, typv2 ->
            self#unify_typ_aux `Equal level env typv1 typv2

        | TyFun(name, a, b), f1, f2 ->
            let var = stuck_local level in
            self#unify_value (level + 1) ((name, a, `Bound) :: env) (b var)
                (apply f1 var) (apply f2 var)

        | TyPair(_, a, b), p1, p2 ->
            let fst1 = project p1 `Fst in
            let fst2 = project p2 `Fst in
            self#unify_value level env a fst1 fst2;
            self#unify_value level env (b fst1) (project p1 `Snd) (project p2 `Snd)

        | TyEq _, _, _ ->
            ()

        | Stuck _, Stuck(Meta _, _), Stuck(Meta _, _) ->
            equations <- (fun () -> self#unify_value level env typ v1 v2) :: equations;
            raise CannotSolveYet

        | Stuck _, Stuck(Meta(_, meta), elim), v
        | Stuck _, v, Stuck(Meta(_, meta), elim) ->
            begin try
                let _, meta, elim = decompose_pair self meta elim in
                let ren = elim_to_renaming level elim in
                let body = rename_value self meta ren v in
                let sol = make_fun ren.cod body in
                self#solve_meta meta (Eval.eval self [] sol);
                progressed <- true
            with CannotSolveYet ->
                equations <- (fun () -> self#unify_value level env typ v1 v2) :: equations;
                raise CannotSolveYet
            end

        | Stuck _, Stuck(head1, elim1), Stuck(head2, elim2) ->
            let head_typ = self#unify_head level env head1 head2 in
            ignore (self#unify_elim level env head1 head_typ elim1 elim2)

        | _ ->
            raise RuntimeError


    method private unify_head level env head1 head2 =
        match head1, head2 with
        | TopVar(shift1, name1), TopVar(shift2, name2) when shift1 = shift2 && name1 = name2 ->
            let (AxiomDecl typ | Definition(typ, _)) = self#find_global name1 in
            typ
        | Local lvl1, Local lvl2 when lvl1 = lvl2 ->
            let (_, typ, _) = List.nth env (level - lvl1 - 1) in
            typ 
        | Coe coe1, Coe coe2 when coe1.ulevel = coe2.ulevel ->
            self#unify_value level env (Type coe1.ulevel) coe1.lhs coe2.lhs;
            self#unify_value level env (Type coe1.ulevel) coe1.rhs coe2.rhs;
            self#unify_value level env coe1.lhs coe1.coerced coe2.coerced;
            coe1.rhs
        | _ ->
            raise UnificationFailure


    method private unify_elim level env head head_typ elim1 elim2 =
        match elim1, elim2 with
        | EmptyElim, EmptyElim ->
            head_typ
        | App(elim1', arg1), App(elim2', arg2) ->
            begin match self#unify_elim level env head head_typ elim1' elim2' with
            | TyFun(_, a, b) -> self#unify_value level env a arg1 arg2; b arg1
            | _              -> raise RuntimeError
            end
        | Proj(elim1', field1), Proj(elim2', field2) when field1 = field2 ->
            begin match self#unify_elim level env head head_typ elim1' elim2', field1 with
            | TyPair(_, a, b), `Fst -> a
            | TyPair(_, a, b), `Snd -> b @@ Stuck(head, Proj(elim1', `Fst))
            | _                     -> raise RuntimeError
            end
        | _ ->
            raise UnificationFailure



    method private unify_typ_aux (mode : [`Subtyp | `Equal]) level env sub sup =
        match force self sub, force self sup with
        | Type ulevel1, Type ulevel2 ->
            begin match mode with
            | `Subtyp when ulevel1 <= ulevel2 -> ()
            | `Equal  when ulevel1 =  ulevel2 -> ()
            | _                               -> raise UnificationFailure
            end

        | TyFun (name, a1, b1), TyFun (_, a2, b2) ->
            self#unify_typ_aux mode level env a2 a1;
            let var = stuck_local level in
            self#unify_typ_aux mode (level + 1) ((name, a2, `Bound) :: env) (b1 var) (b2 var)

        | TyPair(name, a1, b1), TyPair(_, a2, b2) ->
            self#unify_typ_aux mode level env a1 a2;
            let var = stuck_local level in
            self#unify_typ_aux mode (level + 1) ((name, a1, `Bound) :: env) (b1 var) (b2 var)

        | TyEq((lhs1, lhs_typ1), (rhs1, rhs_typ1))
        , TyEq((lhs2, lhs_typ2), (rhs2, rhs_typ2)) ->
            self#unify_typ_aux mode level env lhs_typ1 lhs_typ2;
            self#unify_typ_aux mode level env rhs_typ1 rhs_typ2;
            self#unify_value level env lhs_typ1 lhs1 lhs2;
            self#unify_value level env rhs_typ1 rhs1 rhs2

        | Stuck(Meta _, _), Stuck(Meta _, _) ->
            equations <- (fun () -> self#unify_typ_aux mode level env sub sup) :: equations;
            raise CannotSolveYet

        | Stuck(Meta(_, meta), elim), v
        | v, Stuck(Meta(_, meta), elim) ->
            begin try
                let _, meta, elim = decompose_pair self meta elim in
                let ren = elim_to_renaming level elim in
                let sol = make_fun ren.cod (rename_value self meta ren v) in
                self#solve_meta meta (Eval.eval self [] sol);
                progressed <- true
            with CannotSolveYet ->
                equations <- (fun () -> self#unify_typ_aux mode level env sub sup) :: equations;
                raise CannotSolveYet
            end

        | Stuck(head1, elim1), Stuck(head2, elim2) ->
            let head_typ = self#unify_head level env head1 head2 in
            ignore (self#unify_elim level env head1 head_typ elim1 elim2)

        | _ ->
            raise UnificationFailure


end
