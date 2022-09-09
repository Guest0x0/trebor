
open Core
open Syntax

let parse_lexbuf lexbuf = Parser.program Lexer.token lexbuf
let parse_string ?filename src =
    let lexbuf = Lexing.from_string src in
    Option.iter (fun filename -> Lexing.set_filename lexbuf filename) filename;
    parse_lexbuf lexbuf


let expr_of_string src =
    let lexbuf = Lexing.from_string src in
    Parser.expr Lexer.token lexbuf

let core_of_string globals ctx src =
    let _, core = Typecheck.check_typ globals ctx (expr_of_string src) in
    core



let error_equal globals err1 err2 =
    let open Normalization in
    match err1, err2 with
    | UnboundVar name1, UnboundVar name2 -> name1 = name2
    | CannotInfer ctx1, CannotInfer ctx2 -> ctx1 = ctx2
    | WrongType(ctx1, typ1, err_ctx1)
    , WrongType(ctx2, typ2, err_ctx2) ->
        let level = List.length ctx1 in
        let v_ctx1 = eval_context globals ctx1 in
        let v_ctx2 = eval_context globals ctx2 in
        let values = List.mapi (fun idx _ -> V_Ne(N_Level(level - idx - 1))) ctx1 in
        context_equal globals v_ctx1 v_ctx2
        && typ_equal globals (List.length v_ctx1) v_ctx1
            (eval globals values typ1) (eval globals values typ2)
        && err_ctx1 = err_ctx2
    | TypeMismatch(ctx1, expected1, actual1, err_ctx1)
    , TypeMismatch(ctx2, expected2, actual2, err_ctx2) ->
        let level = List.length ctx1 in
        let v_ctx1 = eval_context globals ctx1 in
        let v_ctx2 = eval_context globals ctx2 in
        let values = List.mapi (fun idx _ -> V_Ne(N_Level(level - idx - 1))) ctx1 in
        context_equal globals v_ctx1 v_ctx2
        && typ_equal globals (List.length v_ctx1) v_ctx1
            (eval globals values expected1) (eval globals values expected2)
        && typ_equal globals (List.length v_ctx1) v_ctx1
            (eval globals values actual1) (eval globals values actual2)
        && err_ctx1 = err_ctx2
    | _ ->
        false


let wrong_type ctx typ err_ctx =
    let globals = Hashtbl.create 0 in
    let ctx = List.rev_map (fun (name, src) -> (name, expr_of_string src)) ctx in
    let c_ctx, v_ctx = Typecheck.check_context globals ctx in
    WrongType(c_ctx, core_of_string globals v_ctx typ, err_ctx)

let type_mismatch ctx expected actual err_ctx =
    let globals = Hashtbl.create 0 in
    let ctx = List.rev_map (fun (name, src) -> (name, expr_of_string src)) ctx in
    let c_ctx, v_ctx = Typecheck.check_context globals ctx in
    TypeMismatch( c_ctx
                , core_of_string globals v_ctx expected
                , core_of_string globals v_ctx actual
                , err_ctx )


let tests = ref []

let register_test name expectation src =
    tests := (name, expectation, src) :: !tests

let run_test (name, expectation, src) =
    let open Format in
    let globals = Prelude.make_globals 37 in
    let result =
        try Ok(Typecheck.check_program globals (parse_string ~filename:name src)) with
          exn -> Error exn
    in
    let pp_result fmt = function
        | Ok _      -> fprintf fmt "actual result: well typed"
        | Error exn -> fprintf fmt "@[<v2>actual result:@ %a@]" Pretty.pp_exception exn
    in
    let pp_expectation fmt = function
        | None     -> fprintf fmt "expected result: well typed"
        | Some err -> fprintf fmt "@[<v2>expected result:@ %a@]" Pretty.pp_error err
    in
    match result, expectation with
    | Ok _, None ->
        printf "test %s passed@ " name; true
    | Error(TypeError(_, err)), Some err' when error_equal globals err err' ->
        printf "test %s passed@ " name; true
    | _ ->
        printf "test %s failed:@ %a@ %a@ " name pp_expectation expectation pp_result result;
        false

let run_tests () =
    let open Format in
    printf "@[<v>";
    let passed_cnt = List.fold_right
            (fun test passed_cnt ->
                        if run_test test
                        then passed_cnt + 1
                        else passed_cnt)
            !tests 0
    in
    let total_cnt = List.length !tests in
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
let my-refl : forall (A : Type 0) (a : A) -> a = a
let my-refl = fun A a -> eq-refl A a
" ;;

register_test "defeq.beta" None "
let beta-id : forall (A : Type 0) (a : A) -> (fun (x : A) -> x) a = a
let beta-id = fun A a -> eq-refl A a
" ;;

register_test "defeq.under-binder" None "
let danger : forall (A : Type 0) ->
    (fun (x : A) -> (fun (y : A) (x : A) -> y) x)
    = (fun (x : A) (y : A) -> x)
let danger = fun A -> eq-refl (A -> A -> A) (fun (x : A) (y : A) -> x)
" ;;

register_test "defeq.under-binder-counter" (Some(
        type_mismatch ["A", "Type 0"]
            "(fun (x : A) -> (fun (y : A) (x : A) -> y) x) = (fun (x : A) (y : A) -> y)"
            "(fun (x : A) -> (fun (y : A) (x : A) -> y) x) = (fun (x : A) (y : A) -> x)"
            "global definition"
)) "
let bad : forall (A : Type 0) ->
    (fun (x : A) -> (fun (y : A) (x : A) -> y) x)
    = (fun (x : A) (y : A) -> y)
let bad = fun A -> eq-refl (A -> A -> A) (fun (x : A) (y : A) -> x)
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



register_test "examples.eta.fun" None "
let fun-eta : forall (A : Type 0) (B : A -> Type 0) ->
    forall (f : forall (a : A) -> B a) -> f = (fun (a : A) -> f a)
let fun-eta = fun A B f -> eq-refl (forall (a : A) -> B a) f
" ;;

register_test "examples.eta.pair" None "
let pair-eta : forall (A : Type 0) (B : A -> Type 0) ->
    forall (p : exists (a : A) -> B a) -> p = (p.1, p.2) : (exists (a : A) -> B a)
let pair-eta = fun A B p -> eq-refl (exists (a : A) -> B a) p
" ;;


register_test "examples.UIP" None "
let UIP : forall (A : Type 0) (B : Type 0) (a : A) (b : B) ->
    forall (p : a = b) (q : a = b) -> p = q
let UIP = fun A B a b p q -> eq-refl (a = b) p
" ;;


register_test "examples.type-formers-resp-eq" None "
let ap : forall (A B : Type 0) (a1 a2 : A) (f : A -> B) -> a1 = a2 -> f a1 = f a2
let ap = fun A B a1 a2 f eq ->
    apply-resp-eq A A (fun a -> B) (fun a -> B) f f (eq-refl (A -> B) f) a1 a2 eq


let fun-type-resp-eq : forall (A1 A2 : Type 0) (B1 : A1 -> Type 0) (B2 : A2 -> Type 0) ->
    A1 = A2 -> B1 = B2 -> (forall (a1 : A1) -> B1 a1) = (forall (a2 : A2) -> B2 a2)
let fun-type-resp-eq = fun A1 A2 B1 B2 eqA eqB ->
    ap (exists (A : Type 0) -> A -> Type 0) (Type 0)
        (A1, B1) (A2, B2)
        (fun family -> forall (a : family.1) -> family.2 a)
        (pairext
            (Type 0) (Type 0)
            (fun A -> A -> Type 0) (fun A -> A -> Type 0)
            (A1, B1) (A2, B2)
            eqA eqB)


let pair-type-resp-eq : forall (A1 A2 : Type 0) (B1 : A1 -> Type 0) (B2 : A2 -> Type 0) ->
    A1 = A2 -> B1 = B2 -> (exists (a1 : A1) -> B1 a1) = (exists (a2 : A2) -> B2 a2)
let pair-type-resp-eq = fun A1 A2 B1 B2 eqA eqB ->
    ap (exists (A : Type 0) -> A -> Type 0) (Type 0)
        (A1, B1) (A2, B2)
        (fun family -> exists (a : family.1) -> family.2 a)
        (pairext
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
    omega A eq (omega A eq :> eq-symm (Type 0) (Type 0) A (A -> A) eq)
" ;;



let _ = run_tests ()
