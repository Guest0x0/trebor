
open Syntax
open Value

exception RuntimeError


let apply vf va =
    match vf with
    | Fun  (_, f) -> f va
    | Stuck(h, e) -> Stuck(h, App(e, va))
    | _           -> raise RuntimeError


let project vpair field =
    match vpair, field with
    | Pair(fst, _), `Fst  -> fst
    | Pair(_, snd), `Snd  -> snd
    | Stuck(h, e) , field -> Stuck(h, Proj(e, field))
    | _                   -> raise RuntimeError


let rec eliminate headv = function
    | EmptyElim          -> headv
    | App(elim', argv)   -> apply (eliminate headv elim') argv
    | Proj(elim', field) -> project (eliminate headv elim') field



exception CannotShiftMeta

let rec shift level value =
    match value with
    | Stuck (head, elim) -> Stuck (shift_head level head, shift_elim level elim)
    | Type  ulevel       -> Type  (ulevel + level)
    | TyFun (name, a, b) -> TyFun (name, shift level a, shift_func level b)
    | Fun   (name, f)    -> Fun   (name, shift_func level f)
    | TyPair(name, a, b) -> TyPair(name, shift level a, shift_func level b)
    | Pair  (fst, snd)   -> Pair  (shift level fst, shift level snd)
    | TyEq((lhs, lhs_typ), (rhs, rhs_typ)) ->
        TyEq((shift level lhs, shift level lhs_typ), (shift level rhs, shift level rhs_typ))

and shift_head level = function
    | Local _ as head      -> head
    | TopVar(level', name) -> TopVar(level + level', name)
    | Coe { ulevel; coerced; lhs; rhs; eq } ->
        Coe { ulevel  = ulevel + level
            ; coerced = shift level coerced
            ; lhs     = shift level lhs
            ; rhs     = shift level rhs
            ; eq      = lazy(shift level (Lazy.force eq)) }
    | Meta _ ->
        raise CannotShiftMeta

and shift_elim level = function
    | EmptyElim as elim  -> elim
    | App (elim', arg)   -> App(shift_elim level elim', shift level arg)
    | Proj(elim', field) -> Proj(shift_elim level elim', field)

and shift_func level f = fun v ->
    v |> shift (- level) |> f |> shift level





let app_axiom axiom ?(shift=0) args =
    Stuck( TopVar(shift, axiom)
         , List.fold_left (fun elim arg -> App(elim, arg)) EmptyElim args)


let rec coerce ulevel coerced lhs rhs eq =
    match lhs, rhs with
    | Type ulevel1, Type ulevel2 when ulevel1 = ulevel2 ->
        coerced

    | TyFun(name1, a1, b1), TyFun(name2, a2, b2) ->
        let a2_eq_a1 = lazy(app_axiom "eq-symm" ~shift:1
                [ Type 0; Type 0; a1; a2
                ; app_axiom "fun-param-injective"
                        [ a1; a2; Fun(name1, b1); Fun(name2, b2)
                        ; Lazy.force eq ] ])
        in
        let b1_eq_b2 x1 x2 x1_eq_x2 = app_axiom "fun-ret-injective"
                [ a1; a2; Fun(name1, b1); Fun(name2, b2); Lazy.force eq
                ; x1; x2; x1_eq_x2 ]
        in
        let f2 x2 =
            let x1 = coerce ulevel x2 a2 a1 a2_eq_a1 in
            let r1 = apply coerced x1 in
            let x2_eq_x1 () = app_axiom "coe-coherent" [ a2; a1; x2; Lazy.force a2_eq_a1 ] in
            coerce ulevel r1 (b1 x1) (b2 x2)
            @@ lazy(b1_eq_b2 x1 x2 @@ app_axiom "eq-symm"
                [ a2; a1; x2; x1; x2_eq_x1 () ])
        in
        Fun(name2, f2)

    | TyPair(name1, a1, b1), TyPair(name2, a2, b2) ->
        let a1_eq_a2 = lazy(app_axiom "pair-fst-injective"
                [ a1; a2; Fun(name1, b1); Fun(name2, b2); Lazy.force eq ])
        in
        let fst1 = project coerced `Fst in
        let fst2 = coerce ulevel fst1 a1 a2 a1_eq_a2 in
        let fst1_eq_fst2 () = app_axiom "coe-coherent" [ a1; a2; fst1; Lazy.force a1_eq_a2 ] in
        let b1_eq_b2 = lazy(app_axiom "pair-snd-injective"
                [ a1; a2; Fun(name1, b1); Fun(name2, b2); Lazy.force eq
                ; fst1; fst2; fst1_eq_fst2 () ])
        in
        let snd1 = project coerced `Snd in
        Pair(fst2, coerce ulevel snd1 (b1 fst1) (b2 fst2) b1_eq_b2)

    (* TODO: handling of absurd equalities (e.g. (A -> B) = (A * B)) *)
    | _ ->
        Stuck(Coe { ulevel; coerced; lhs; rhs; eq }, EmptyElim)



let rec force g value =
    match value with
    | Stuck(Meta(_, m), elim) ->
        begin match g#find_meta m with
        | Solved v -> force g (eliminate v elim)
        | _        -> value
        end
    | _ ->
        value




let abstract_env env ret_typ =
    List.fold_left (fun typ (_, param_typ) -> TyFun("", param_typ, Fun.const typ))
        ret_typ env

let apply_env f level =
    let args = List.init level stuck_local in
    List.fold_left apply f args


let rec eval g env core =
    match core with
    | Core.TopVar name ->
        begin match g#find_global name with
        | AxiomDecl _          -> Stuck(TopVar(0, name), EmptyElim)
        | Definition(_, value) -> value
        end
    | Core.Local idx         -> List.nth env idx
    | Core.Let(_, rhs, body) -> eval g (eval g env rhs :: env) body

    | Core.Type ulevel         -> Type ulevel
    | Core.Shift(level, core') -> shift level (eval g env core')

    | Core.TyFun(name, a, b) -> TyFun(name, eval g env a, fun v -> eval g (v :: env) b)
    | Core.Fun(name, body)   -> Fun(name, fun v -> eval g (v :: env) body)
    | Core.App(func, arg)    -> apply (eval g env func) (eval g env arg)

    | Core.TyPair(name, a, b) -> TyPair(name, eval g env a, fun v -> eval g (v :: env) b)
    | Core.Pair(fst, snd)     -> Pair(eval g env fst, eval g env snd)
    | Core.Proj(pair, field)  -> project (eval g env pair) field

    | Core.TyEq((lhs, lhs_typ), (rhs, rhs_typ)) ->
        TyEq( (eval g env lhs, eval g env lhs_typ)
            , (eval g env rhs, eval g env rhs_typ))
    | Core.Coe { ulevel; coerced; lhs; rhs; eq } ->
        coerce ulevel (eval g env coerced) (eval g env lhs) (eval g env rhs)
            (lazy(eval g env @@ Lazy.force eq))

    | Core.Meta(name, meta) -> Stuck(Meta(name, meta), EmptyElim)
