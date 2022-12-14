
open Kernel

let parse_lexbuf lexbuf = Parser.program Lexer.token lexbuf
let parse_string ?filename src =
    let lexbuf = Lexing.from_string src in
    Option.iter (fun filename -> Lexing.set_filename lexbuf filename) filename;
    parse_lexbuf lexbuf


let expr_of_string src =
    let lexbuf = Lexing.from_string src in
    Parser.single_expr Lexer.token lexbuf

let core_of_string g ctx src =
    try snd @@ Elaborate.check_typ g ctx (expr_of_string src) with
      exn ->
        Format.printf "@[<v2>error on processing expected result:@ %a@]@ "
            (Pretty.pp_exception true) exn;
        Format.print_flush ();
        raise exn




let rec term_equal tm1 tm2 =
    let open Syntax.Core in
    match tm1, tm2 with
    | TopVar name1       , TopVar name2        -> name1 = name2
    | Local  idx1        , Local  idx2         -> idx1 = idx2
    | Let(_, rhs1, body1), Let(_, rhs2, body2) -> term_equal rhs1 rhs2 && term_equal body1 body2

    | Type ulevel1       , Type ulevel2        -> ulevel1 = ulevel2
    | Shift(level1, tm1'), Shift(level2, tm2') -> level1 = level2 && term_equal tm1' tm2'

    | TyFun(_, k1, a1, b1), TyFun(_, k2, a2, b2) -> k1 = k2 && term_equal a1 a2 && term_equal b1 b2
    | Fun(_, body1)       , Fun(_, body2)        -> term_equal body1 body2
    | App(f1, a1)         , App(f2, a2)          -> term_equal f1 f2 && term_equal a1 a2

    | TyPair(_, a1, b1), TyPair(_, a2, b2) -> term_equal a1 a2 && term_equal b1 b2
    | Pair(fst1, snd1) , Pair(fst2, snd2)  -> term_equal fst1 fst2 && term_equal snd1 snd2
    | Proj(p1, field1) , Proj(p2, field2)  -> field1 = field2 && term_equal p1 p2

    | TyEq( (lhs1, lhs_typ1), (rhs1, rhs_typ1) )
    , TyEq( (lhs2, lhs_typ2), (rhs2, rhs_typ2) ) ->
        term_equal lhs1 lhs2
        && term_equal lhs_typ1 lhs_typ2
        && term_equal rhs1 rhs2
        && term_equal rhs_typ1 rhs_typ2
    | Coe coe1, Coe coe2 ->
        term_equal coe1.coerced coe2.coerced
        && term_equal coe1.lhs coe2.lhs
        && term_equal coe1.rhs coe2.rhs

    | _ ->
        false


let error_equal globals err1 err2 =
    let open Syntax.Error in
    let rec env_equal env1 env2 =
        match env1, env2 with
        | [], [] ->
            true
        | (_, name1, typ1) :: env1', (_, name2, typ2) :: env2' ->
            name1 = name2 && term_equal typ1 typ2 && env_equal env1' env2'
        | _ ->
            false
    in
    let open Syntax in
    match err1, err2 with
    | UnboundVar name1, UnboundVar name2 -> name1 = name2
    | CannotInfer ctx1, CannotInfer ctx2 -> ctx1 = ctx2
    | WrongType(env1, typ1, err_ctx1)
    , WrongType(env2, typ2, err_ctx2) ->
        env_equal env1 env2
        && term_equal typ1 typ2
        && err_ctx1 = err_ctx2
    | TypeMismatch(env1, expected1, actual1, err_ctx1)
    , TypeMismatch(env2, expected2, actual2, err_ctx2) ->
        env_equal env1 env2
        && term_equal expected1 expected2
        && term_equal actual1 actual2
        && err_ctx1 = err_ctx2
    | RedeclareVar var1 , RedeclareVar var2  -> var1 = var2
    | RedefineVar  var1 , RedefineVar  var2  -> var1 = var2
    | CanOnlyShiftGlobal, CanOnlyShiftGlobal -> true
    | UnsolvedMeta(ms1, _), UnsolvedMeta(ms2, _) ->
        List.for_all2
            (fun (m1, info1) (m2, info2) ->
                            m1 = m2 &&
                            match info1, info2 with
                            | Core.Free typ1, Core.Free typ2 ->
                                term_equal typ1 typ2
                            | Core.Solved(typ1, val1), Core.Solved(typ2, val2) ->
                                term_equal typ1 typ2 && term_equal val1 val2
                            | _ ->
                                false)
            ms1 ms2

    | _ ->
        false


let wrong_type ctx typ err_ctx =
    let g = new Context.context in
    let env = List.rev_map (fun (name, src) -> (Syntax.Bound, name, expr_of_string src)) ctx in
    let elab_ctx, envC = Elaborate.check_env g env in
    Syntax.Error.WrongType(envC, core_of_string g elab_ctx typ, err_ctx)

let type_mismatch ctx expected actual err_ctx =
    let g = new Context.context in
    let env = List.rev_map (fun (name, src) -> (Syntax.Bound, name, expr_of_string src)) ctx in
    let elab_ctx, envC = Elaborate.check_env g env in
    Syntax.Error.TypeMismatch( envC
                             , core_of_string g elab_ctx expected
                             , core_of_string g elab_ctx actual
                             , err_ctx )


let tests = ref []

let verbose = true

let register_test name expectation src =
    tests := (name, expectation, src) :: !tests

let run_test (name, expectation, src) =
    let open Format in
    let g = new Context.context in
    let result =
        try
            Prelude.load g;
            Ok(Elaborate.check_program g (parse_string ~filename:name src))
        with exn -> Error exn
    in
    let pp_result fmt = function
        | Ok _      -> fprintf fmt "actual result: well typed"
        | Error exn -> fprintf fmt "@[<v2>actual result:@ %a@]" (Pretty.pp_exception verbose) exn
    in
    let pp_expectation fmt = function
        | None     -> fprintf fmt "expected result: well typed"
        | Some err -> fprintf fmt "@[<v2>expected result:@ %a@]" (Pretty.pp_error verbose) err
    in
    match result, expectation with
    | Ok _, None ->
        printf "test %s passed@ " name; true
    | Error(Syntax.Error.Error(_, err)), Some err' when error_equal g err err' ->
        printf "test %s passed@ " name; true
    | _ ->
        printf "test %s failed:@ %a@ %a@ " name pp_expectation expectation pp_result result;
        false

let run_tests () =
    let open Format in
    let tests =
        if Array.length Sys.argv > 1
        then List.filter (fun (name, _, _) -> Array.mem name Sys.argv) !tests
        else !tests
    in
    printf "@[<v>";
    let passed_cnt = List.fold_right
            (fun test passed_cnt ->
                        if run_test test
                        then passed_cnt + 1
                        else passed_cnt)
            tests 0
    in
    let total_cnt = List.length tests in
    printf "summary: %d of %d tests passed@ @]" passed_cnt total_cnt;
    if passed_cnt < total_cnt then
        failwith "test failed"
;;


register_test "basic.global" None "
let A : Type 0

let x : Type 0
let x = A
" ;;

register_test "basic.local" None "
let f : forall (A : Type 0) -> A -> A
let f = fun A a -> a
" ;;

register_test "basic.let" None "
let program = fun (A : Type) (f : A -> A -> A) ->
    let ff = fun (x : A) -> f x x in
    fun (x : A) -> ff (ff (ff x))
" ;;


register_test "basic.annotation" None "
let f = fun (A : Type 0) -> (fun a -> a) : (A -> A)
" ;;

register_test "basic.function.type" None "
let Pi2 : forall (A : Type 0) (B : A -> Type 0) (C : forall (a : A) -> B a -> Type 0) -> Type 0
let Pi2 = fun A B C -> forall (a : A) (b : B a) -> C a b
" ;;

register_test "basic.function.application" None "
let apply : forall (A : Type 0) (B : A -> Type 0) -> (forall (a : A) -> B a) -> forall (a : A) -> B a
let apply = fun A B f a -> f a

let rev_apply : forall (A : Type 0) (B : A -> Type 0) -> forall (a : A) -> (forall (a : A) -> B a) -> B a
let rev_apply = fun A B a f -> f a
" ;;


register_test "basic.pair.type" None "
let Sigma2 : forall (A : Type 0) (B : A -> Type 0) (C : forall (a : A) -> B a -> Type 0) -> Type 0
let Sigma2 = fun A B C -> exists (a : A) (b : B a) -> C a b
" ;;

register_test "basic.pair.infer" None "
let type-of-pair = forall (A B : Type 0) -> A -> B -> exists (a : A) -> B
let pair = fun (A B : Type 0) (a : A) (b : B) -> (a, b)

let pair' = pair : type-of-pair
" ;;

register_test "basic.pair.check" None "
let pair : forall (A : Type 0) (B : A -> Type 0) -> forall (a : A) -> B a -> exists (a : A) -> B a
let pair = fun A B fst snd -> (fst, snd)
" ;;

register_test "basic.pair.projection" None "
let fst : forall (A : Type 0) (B : A -> Type 0) -> (exists (a : A) -> B a) -> A
let fst = fun A B p -> p.1

let snd : forall (A : Type 0) (B : A -> Type 0) (p : exists (a : A) -> B a) -> B (fst A B p)
let snd = fun A B p -> p.2
" ;;


register_test "basic.equality.type" None "
let eq : forall (A B : Type 0) (a : A) (b : B) -> Type 0
let eq = fun A B a b -> a = b
" ;;

register_test "basic.equality.coercion" None "
let coe : forall (A B : Type 0) -> A = B -> A -> B
let coe = fun A B eq a -> a :> eq
" ;;


register_test "defeq.refl" None "
let my-refl : forall (A : Type) (a : A) -> a = a
let my-refl = fun A a -> @eq-refl A a
" ;;

register_test "defeq.global" None "
let g = fun (A : Type) (a : A) -> a

let g-def : g = (fun (A : Type) (a : A) -> a)
let g-def = ~eq-refl g
" ;;

register_test "defeq.let" None "
let eq : forall (A B : Type) (f : A -> A -> A) (x : A) ->
    (let ff = fun (x : A) -> f x x in ff (ff (ff x)))
    = f (f (f x x) (f x x)) (f (f x x) (f x x))
let eq = fun A B f x -> ~eq-refl (let ff = fun (x : A) -> f x x in ff (ff (ff x)))
" ;;


register_test "defeq.fun.beta" None "
let beta-id : forall (A : Type) (a : A) -> (fun (x : A) -> x) a = a
let beta-id = fun A a -> ~eq-refl a
" ;;

register_test "defeq.fun.beta.under-binder" None "
let danger : forall (A : Type 0) ->
    (fun (x : A) -> (fun (y : A) (x : A) -> y) x)
    = (fun (x : A) (y : A) -> x)
let danger = fun A -> ~eq-refl (fun (x : A) (y : A) -> x)
" ;;

register_test "defeq.fun.beta.under-binder-counter" (Some(
        type_mismatch ["A", "Type 0"]
            "(fun (x : A) (y : A) -> x) = (fun (x : A) (y : A) -> y)"
            "(fun (x : A) (y : A) -> x) = (fun (x : A) (y : A) -> x)"
            "global definition"
)) "
let bad : forall (A : Type 0) ->
    (fun (x : A) -> (fun (y : A) (x : A) -> y) x)
    = (fun (x : A) (y : A) -> y)
let bad = fun A -> ~eq-refl (fun (x : A) (y : A) -> x)
" ;;


register_test "defeq.fun.eta" None "
let fun-eta : forall (A : Type 0) (B : A -> Type 0) ->
    forall (f : forall (a : A) -> B a) -> f = (fun (a : A) -> f a)
let fun-eta = fun A B f -> ~eq-refl f
" ;;



register_test "defeq.pair.beta" None "
let eq-fst : forall (A : Type) (B : A -> Type) (a : A) (b : B a) -> (a, b).1 = a
let eq-fst = fun A B a b -> ~eq-refl a

let eq-snd : forall (A : Type) (B : A -> Type) (a : A) (b : B a) -> (a, b).2 = b
let eq-snd = fun A B a b -> ~eq-refl b
" ;;

register_test "defeq.pair.eta" None "
let pair-eta : forall (A : Type 0) (B : A -> Type 0) ->
    forall (p : exists (a : A) -> B a) -> p = (p.1, p.2) : (exists (a : A) -> B a)
let pair-eta = fun A B p -> ~eq-refl p
" ;;




register_test "defeq.equality.UIP" None "
let UIP : forall (A : Type 0) (B : Type 0) (a : A) (b : B) ->
    forall (p : a = b) (q : a = b) -> p = q
let UIP = fun A B a b p q -> eq-refl p
" ;;


register_test "defeq.coe.type" None "
let eq : forall (p : Type = Type) (A : Type) -> A :> p = A
let eq = fun p A -> ~eq-refl A
" ;;

register_test "defeq.coe.fun" None "
let goal : forall (A1 A2 : Type 0) (B1 : A1 -> Type 0) (B2 : A2 -> Type 0) ->
    forall (eq : (forall (a : A1) -> B1 a) = (forall (a : A2) -> B2 a)) ->
    forall (f : forall (a : A1) -> B1 a) ->
        f :> eq = (fun (a2 : A2) ->
            let eqA = ~eq-symm (fun-param-injective eq) in
            let a1  = a2 :> eqA in 
            let eqB = fun-ret-injective eq (eq-symm (coe-coherent a2 eqA)) in
            f a1 :> eqB)
let goal = fun A1 A2 B1 B2 eq f -> eq-refl (f :> eq)
" ;;

register_test "defeq.coe.pair" None "
let goal : forall (A1 A2 : Type 0) (B1 : A1 -> Type 0) (B2 : A2 -> Type 0) ->
    forall (eq : (exists (a : A1) -> B1 a) = (exists (a : A2) -> B2 a)) ->
    forall (pair : exists (a : A1) -> B1 a) ->
        pair :> eq = (
            let eqA = pair-fst-injective eq in
            let a1 = pair.1 in
            let a2 = a1 :> eqA in
            let eqB = pair-snd-injective eq (coe-coherent a1 eqA) in
            (a2, pair.2 :> eqB) : (exists (a : A2) -> B2 a)
        )
let goal = fun A1 A2 B1 B2 eq pair -> eq-refl (pair :> eq)
" ;;




register_test "error.scope" (Some(UnboundVar "A")) "
let bad = fun (x : A) -> x
"  ;;

register_test "error.cannot-infer" (Some(CannotInfer "function without parameter annotation")) "
let bad = fun x -> x
" ;;

register_test "error.wrong-type.function" (Some(wrong_type ["A", "Type 0"] "Type 0" "function")) "
let bad = fun (A : Type 0) -> A A
" ;;

register_test "error.wrong-type.pair" (Some(wrong_type ["A", "Type 0"] "Type 0" "pair")) "
let bad = fun (A : Type 0) -> A.1
" ;;

register_test "error.wrong-type.equality" (Some(wrong_type ["A", "Type 0"] "Type 0" "equality")) "
let bad = fun (A : Type 0) -> A :> A
" ;;

register_test "error.wrong-type.type" (Some(wrong_type ["A", "Type 0"; "x", "A"] "A" "type")) "
let bad = fun (A : Type 0) (x : A) (y : x) -> y
" ;;


register_test "error.type-mismatch.annotation"
    (Some(type_mismatch ["A", "Type 0"; "B", "Type 0"] "A" "Type 0" "type annotation")) "
let bad = fun (A B : Type 0) -> B : A
" ;;

register_test "error.type-mismatch.application"
    (Some(type_mismatch ["A", "Type 0"; "f", "A -> A"] "A" "A -> A" "function application")) "
let bad = fun (A : Type 0) (f : A -> A) -> f f
" ;;

register_test "error.type-mismatch.coercion"
    (Some(type_mismatch ["A", "Type 0"; "B", "Type 0"; "eq", "A = B"; "b", "B"] "A" "B" "coerced value")) "
let bad = fun (A B : Type 0) (eq : A = B) (b : B) -> b :> eq
" ;;

register_test "error.type-mismatch.global"
    (Some(type_mismatch ["A", "Type 0"] "A" "forall (a : A) -> A" "global definition")) "
let bad : forall (A : Type 0) -> A
let bad = fun A (a : A) -> a
" ;;


register_test "universe.subtyp" None "
let A : Type 2
let A = Type 0

let Pi : forall (A : Type 0) -> Type 2
let Pi = fun (A : Type 1) -> Type 0

let Sigma : exists (A : Type 2) ->  Type 2
let Sigma = (Type 0, Type 0)

let Eq : (Type 0 : Type 2) = (Type 0 : Type 2)
let Eq = ~2 eq-refl (Type 0)
" ;;


register_test "universe.poly.basic" None "
let type-of-id : Type 1
let type-of-id = forall (A : Type) -> A -> A

let id : type-of-id
let id = fun A a -> a

let id-id = ~id type-of-id id
" ;;

register_test "universe.poly.relevant-arg" None "
let f = fun (A : Type 2) (f : Type 1 -> A) -> f (Type 0)
let eq : ~f (Type 2) (fun x -> x) = Type 1
let eq = ~3 eq-refl (Type 1)
" ;;

register_test "universe.poly.irrelevant-arg" None "
let f = fun (A : Type 2) (f : Type 1 -> A) -> f (Type 0)
let eq : ~f (Type 2) (fun x -> Type 1) = Type 1
let eq = ~3 eq-refl (Type 1)
" ;;

register_test "universe.poly.shift-applied-to-meta" None "
let ID = forall {A : Type} -> A -> A

let id : ID
let id = fun a -> a

let test = ~id id
" ;;

register_test "universe.poly.can-only-shift-global" (Some CanOnlyShiftGlobal) "
let test = fun (f : Type -> Type) -> ~f Type
" ;;


register_test "elab.hole.basic" None "
let id = fun (A : Type) (a : A) -> a
let test = id _ Type
" ;;

register_test "elab.hole.type-from-term" None "
let eq : forall (A : Type) (a : A) -> a = _
let eq = @eq-refl
" ;;

register_test "elab.hole.term-from-type" None "
let my-refl : forall (A : Type) (a : A) -> a = a
let my-refl = fun A a -> @eq-refl _ _
" ;;


register_test "unify.function" None "
let apply = fun (A B : Type 1) (f : A -> B) (x : A) -> f x
let id = fun (A : Type) (a : A) -> a

let test =
    let f = _ : (Type -> Type) in
    fun (A : Type) (a : A) -> id (apply Type Type f A) a
" ;;

register_test "unify.let-defined-meta" None "
let id = fun (A : Type) (a : A) -> a

let test = fun (A : Type) ->
    let T = _ : Type in
    fun (a : A) -> id T a
" ;;

register_test "unify.meta-under-let" None "
let id = fun (A : Type) (a : A) -> a

let test = fun (A : Type) ->
    let B : Type = A in
    fun (a : B) -> id _ a
" ;;

register_test "unify.meta-is-pair.arg-pair" None "
let id = fun (A : Type) (a : A) -> a

let test = fun (A : Type) ->
    let p = _ : (Type * Type) in
    fun (a : A) -> (id p.1 a, id p.2 a)
" ;;

register_test "unify.meta-is-pair.pair-arg" None "
let id = fun (A : Type) (a : A) -> a

let test =
    let p = _ : ((Type -> Type) * (Type -> Type)) in
    fun (A : Type) (a : A) -> (id (p.1 A) a, id (p.2 A) a)
" ;;

register_test "unify.meta-is-pair.pair-arg-pair" None "
let id = fun (A : Type) (a : A) -> a

let test =
    let p = _ : ((Type -> Type) * (Type -> Type * Type)) in
    fun (A : Type) (a : A) -> (id (p.1 A) a, id (p.2 A).1 a, id (p.2 A).2 a)
" ;;

register_test "unify.meta-is-pair.arg-pair-arg" None "
let id = fun (A : Type) (a : A) -> a

let test = fun (A : Type) ->
    let p = _ : (Type * (Type -> Type)) in
    fun (B : Type) (a : A) (b : B) -> (id p.1 a, id (p.2 B) (a, b))
" ;;



register_test "unify.pair-applied-to-meta.1" None "
let id = fun (A : Type) (a : A) -> a

let test =
    let p = _ : (Type * Type -> Type) in
    fun (A B : Type) (a : A) -> id (p (A, B)) a
" ;;

register_test "unify.pair-applied-to-meta.2" None "
let id = fun (A : Type) (a : A) -> a

let test =
    let p = _ : (Type * Type -> Type) in
    fun (A B : Type) (b : B) -> id (p (A, B)) b
" ;;

register_test "unify.pair-applied-to-meta.3" None "
let id = fun (A : Type) (a : A) -> a

let test = fun (A : Type) ->
    let p = _ : (A * (A -> Type) -> Type) in
    fun (B : A -> Type) (a : A) (b : B a) -> id (p (a, B)) b
" ;;



register_test "implicit.basic.app" None "
let id = fun {A : Type} (a : A) -> a

let test = fun (A : Type) (a : A) -> id a
" ;;

register_test "implicit.basic.proj.1" None "
let id = fun (A : Type) (a : A) -> a
let diagonal = fun {A : Type} -> (A, A)

let test = fun (A : Type) (a : A) -> id diagonal.1 a
" ;;

register_test "implicit.basic.proj.2" None "
let id = fun (A : Type) (a : A) -> a
let diagonal = fun {A : Type} -> (A, A)

let test = fun (A : Type) (a : A) -> id diagonal.2 a
" ;;


register_test "implicit.annotation" None "
let id : forall {A : Type} -> A -> A
let id = fun {A} a -> a
" ;;

register_test "implicit.insertion.basic" None "
let Nat : Type
let zero : Nat

let need_id = fun (id : forall {A : Type} -> A -> A) -> id zero
let test = need_id (fun a -> a)
" ;;

register_test "implicit.insertion.reinsert" None "
let swap = fun {A : Type} {B : Type} (p : A * B) -> (p.2, p.1)

let A : Type
let B : Type

let need_swap_with_A = fun (f : forall {B : Type} -> A * B -> B * A) -> Type
let test = need_swap_with_A swap
" ;;


register_test "implicit.explicitfy" None "
let id = fun {A : Type} (a : A) -> a

let id1 : forall (A : Type) -> A -> A
let id1 = @id

let A : Type
let a : A

let test1 = @id _ a
let test2 = @id A a
" ;;




register_test "implicit.lazy.infer" None "
let A : Type
let B : A -> Type

let f : forall {a : A} -> B a
let g : forall {a : A} -> B a

let eq : Type
let eq = (f = g)
" ;;


register_test "implicit.lazy.checked-with-meta" None "
let List : Type 1 -> Type 1
let Nil  : forall {A : Type 1} -> List A
let Cons : forall {A : Type 1} -> A -> List A -> List A

let id = fun {A : Type} (a : A) -> a

let list-of-id = Cons id Nil

let test : List (forall {A : Type} -> A -> A)
let test = list-of-id
" ;;


register_test "implicit.manual-elim" None "
let List : Type 1 -> Type 1
let Nil  : forall {A : Type 1} -> List A
let Cons : forall {A : Type 1} -> A -> List A -> List A

let id = fun {A : Type} (a : A) -> a

let test : forall (A : Type) -> List (A -> A)
let test = fun A -> Cons @{id} Nil
" ;;



register_test "examples.type-formers-resp-eq" None "
let fun-type-resp-eq : forall (A1 A2 : Type 0) (B1 : A1 -> Type 0) (B2 : A2 -> Type 0) ->
    A1 = A2 -> B1 = B2 -> (forall (a1 : A1) -> B1 a1) = (forall (a2 : A2) -> B2 a2)
let fun-type-resp-eq = fun A1 A2 B1 B2 eqA eqB ->
    ~apply-resp-eq
        (eq-refl (fun (family : exists (A : Type) -> A -> Type) ->
                    forall (a : family.1) -> family.2 a))
        (@ ~pairext
            (Type 0) (Type 0)
            (fun A -> A -> Type 0) (fun A -> A -> Type 0)
            (A1, B1) (A2, B2)
            eqA eqB)


let pair-type-resp-eq : forall (A1 A2 : Type 0) (B1 : A1 -> Type 0) (B2 : A2 -> Type 0) ->
    A1 = A2 -> B1 = B2 -> (exists (a1 : A1) -> B1 a1) = (exists (a2 : A2) -> B2 a2)
let pair-type-resp-eq = fun A1 A2 B1 B2 eqA eqB ->
    ~apply-resp-eq
        (eq-refl (fun (family : exists (A : Type) -> A -> Type) ->
                    exists (a : family.1) -> family.2 a))
        (@ ~pairext
            (Type 0) (Type 0)
            (fun A -> A -> Type 0) (fun A -> A -> Type 0)
            (A1, B1) (A2, B2)
            eqA eqB)
" ;;


register_test "examples.self-application" None "
let omega : forall (A : Type 0) -> A = (A -> A) -> A -> A
let omega = fun A eq x -> (x :> eq) x

let type-of-bad = forall (A : Type 0) -> A = (A -> A) -> A

let bad : type-of-bad
let bad = fun A eq ->
    omega A eq (omega A eq :> ~eq-symm eq)
" ;;



let _ = run_tests ()
