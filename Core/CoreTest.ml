
open Core

let parse_lexbuf lexbuf = Parser.program Lexer.token lexbuf
let parse_string src    = parse_lexbuf (Lexing.from_string src)


let globals = Prelude.make_globals 37


let run program =
    try ignore @@ Typecheck.process_program globals program with
      exn -> Format.printf "%a@ " Pretty.pp_exception exn


let _ = Format.printf "@[<v>"
let _ = run @@ parse_string "
let fun-eta : forall (A : Type 0) (B : A -> Type 0) ->
    forall (f : forall (a : A) -> B a) -> f = (fun (a : A) -> f a)
let fun-eta = fun A B f -> eq-refl (forall (a : A) -> B a) f

let pair-eta : forall (A : Type 0) (B : A -> Type 0) ->
    forall (p : exists (a : A) -> B a) -> p = (p.1, p.2) : (exists (a : A) -> B a)
let pair-eta = fun A B p -> eq-refl (exists (a : A) -> B a) p

let UIP : forall (A : Type 0) (B : Type 0) (a : A) (b : B) ->
    forall (p : a = b) (q : a = b) -> p = q
let UIP = fun A B a b p q -> eq-refl (a = b) p



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


let omega : forall (A : Type 0) -> A = (A -> A) -> A -> A
let omega = fun A eq x -> (x :> eq) x

let type-of-bad = forall (A : Type 0) -> A = (A -> A) -> A

let bad : type-of-bad
let bad = fun A eq ->
    omega A eq (omega A eq :> eq-symm (Type 0) (Type 0) A (A -> A) eq)

let normalize-bad = fun (P : type-of-bad -> Type 0) (f : type-of-bad -> P bad) -> f bad
"
let _ = Format.printf "@]"
