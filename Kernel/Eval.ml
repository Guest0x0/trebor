
open Syntax
open Value


exception RuntimeError


let apply vf va =
    match vf with
    | Fun  (_, f)                    -> f va
    | Stuck(TyFun(_, _, a, b), h, e) -> Stuck(b va, h, App(e, a, va))
    | _                              -> raise RuntimeError


let project vpair field =
    match vpair, field with
    | Pair(fst, _), `Fst -> fst
    | Pair(_, snd), `Snd -> snd
    | Stuck(TyPair(_, a, b), h, e), field ->
        let fst = Stuck(a, h, Proj(e, `Fst)) in
        begin match field with
        | `Fst -> fst
        | `Snd -> Stuck(b fst, h, Proj(e, `Snd))
        end
    | _ ->
        raise RuntimeError



let app_axiom g axiom ?(shift=0) args =
    match g#find_global axiom with
    | AxiomDecl typ -> List.fold_left apply (Stuck(typ shift, TopVar(shift, axiom), EmptyElim)) args
    | Definition _  -> raise RuntimeError



let rec coerce g ulevel coerced lhs rhs eq =
    match lhs, rhs with
    | Type ulevel1, Type ulevel2 when ulevel1 = ulevel2 ->
        coerced

    | TyFun(name1, kind1, a1, b1), TyFun(name2, kind2, a2, b2) when kind1 = kind2 ->
        let a2_eq_a1 = lazy(app_axiom g "eq-symm" ~shift:1
                [ Type 0; Type 0; a1; a2
                ; app_axiom g "fun-param-injective"
                        [ a1; a2; Fun(name1, b1); Fun(name2, b2)
                        ; Lazy.force eq ] ])
        in
        let b1_eq_b2 x1 x2 x1_eq_x2 = app_axiom g "fun-ret-injective"
                [ a1; a2; Fun(name1, b1); Fun(name2, b2); Lazy.force eq
                ; x1; x2; x1_eq_x2 ]
        in
        let f2 x2 =
            let x1 = coerce g ulevel x2 a2 a1 a2_eq_a1 in
            let r1 = apply coerced x1 in
            let x2_eq_x1 () = app_axiom g "coe-coherent" [ a2; a1; x2; Lazy.force a2_eq_a1 ] in
            coerce g ulevel r1 (b1 x1) (b2 x2)
            @@ lazy(b1_eq_b2 x1 x2 @@ app_axiom g "eq-symm"
                [ a2; a1; x2; x1; x2_eq_x1 () ])
        in
        Fun(name2, f2)

    | TyPair(name1, a1, b1), TyPair(name2, a2, b2) ->
        let a1_eq_a2 = lazy(app_axiom g "pair-fst-injective"
                [ a1; a2; Fun(name1, b1); Fun(name2, b2); Lazy.force eq ])
        in
        let fst1 = project coerced `Fst in
        let fst2 = coerce g ulevel fst1 a1 a2 a1_eq_a2 in
        let fst1_eq_fst2 () = app_axiom g "coe-coherent" [ a1; a2; fst1; Lazy.force a1_eq_a2 ] in
        let b1_eq_b2 = lazy(app_axiom g "pair-snd-injective"
                [ a1; a2; Fun(name1, b1); Fun(name2, b2); Lazy.force eq
                ; fst1; fst2; fst1_eq_fst2 () ])
        in
        let snd1 = project coerced `Snd in
        Pair(fst2, coerce g ulevel snd1 (b1 fst1) (b2 fst2) b1_eq_b2)

    (* TODO: handling of absurd equalities (e.g. (A -> B) = (A * B)) *)
    | _ ->
        Stuck(rhs, Coe { ulevel; coerced; lhs; rhs; eq }, EmptyElim)



let rec eliminate headv = function
    | EmptyElim           -> headv
    | App(elim', _, argv) -> apply (eliminate headv elim') argv
    | Proj(elim', field)  -> project (eliminate headv elim') field

let rec force g value =
    match value with
    | Stuck(_, Meta(_, m), elim) ->
        begin match g#find_meta m with
        | Solved(_, v) -> force g (eliminate v elim)
        | _            -> value
        end
    | _ ->
        value



let rec eval g shift env core =
    match core with
    | Core.TopVar name ->
        begin match g#find_global name with
        | AxiomDecl typ        -> Stuck(typ shift, TopVar(0, name), EmptyElim)
        | Definition(_, value) -> value shift
        end
    | Core.Local idx         -> List.nth env idx
    | Core.Let(_, rhs, body) -> eval g shift (eval g shift env rhs :: env) body

    | Core.Type ulevel          -> Type (ulevel + shift)
    | Core.Shift(shift', core') -> eval g (shift + shift') env core'

    | Core.TyFun(name, kind, a, b) -> TyFun( name, kind
                                           , eval g shift env a
                                           , fun v -> eval g shift (v :: env) b)
    | Core.Fun(name, body) -> Fun(name, fun v -> eval g shift (v :: env) body)
    | Core.App(func, arg)  -> apply (eval g shift env func) (eval g shift env arg)

    | Core.TyPair(name, a, b) -> TyPair( name
                                       , eval g shift env a
                                       , fun v -> eval g shift (v :: env) b )
    | Core.Pair(fst, snd)     -> Pair(eval g shift env fst, eval g shift env snd)
    | Core.Proj(pair, field)  -> project (eval g shift env pair) field

    | Core.TyEq((lhs, lhs_typ), (rhs, rhs_typ)) ->
        TyEq( (eval g shift env lhs, eval g shift env lhs_typ)
            , (eval g shift env rhs, eval g shift env rhs_typ))
    | Core.Coe { ulevel; coerced; lhs; rhs; eq } ->
        coerce g ulevel (eval g shift env coerced) (eval g shift env lhs) (eval g shift env rhs)
            (lazy(eval g shift env @@ Lazy.force eq))

    | Core.Meta(name, meta) ->
        if shift <> 0 then
            raise RuntimeError;
        begin match g#find_meta meta with
        | Free typ     -> Stuck(typ, Meta(name, meta), EmptyElim)
        | Solved(_, v) -> v
        end


let eval_poly g env core =
    let value0 = eval g 0 env core in
    let values = ref [] in
    let poly s =
        if s = 0
        then value0
        else
            match List.assoc s !values with
            | value ->
                value
            | exception Not_found -> 
                let value = eval g s env core in
                values := (s, value) :: !values;
                value
    in
    poly
