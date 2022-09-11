
let prelude_src = "
let eq-refl  : forall (A : Type 0) (a : A) -> a = a
let eq-symm  : forall (A B : Type 0) (a : A) (b : B) -> a = b -> b = a
let eq-trans : forall (A B C : Type 0) (a : A) (b : B) (c : C) -> a = b -> b = c -> a = c


let coe-coherent : forall (A B : Type 0) (a : A) (eq : A = B) -> a = a :> eq

let fun-param-injective : forall (A1 A2 : Type 0) (B1 : A1 -> Type 0) (B2 : A2 -> Type 0) ->
    (forall (a1 : A1) -> B1 a1) = (forall (a2 : A2) -> B2 a2) -> A1 = A2

let fun-ret-injective : forall (A1 A2 : Type 0) (B1 : A1 -> Type 0) (B2 : A2 -> Type 0) ->
    (forall (a1 : A1) -> B1 a1) = (forall (a2 : A2) -> B2 a2) ->
        forall (a1 : A1) (a2 : A2) -> a1 = a2 -> B1 a1 = B2 a2


let pair-fst-injective : forall (A1 A2 : Type 0) (B1 : A1 -> Type 0) (B2 : A2 -> Type 0) ->
    (exists (a1 : A1) -> B1 a1) = (exists (a2 : A2) -> B2 a2) -> A1 = A2

let pair-snd-injective : forall (A1 A2 : Type 0) (B1 : A1 -> Type 0) (B2 : A2 -> Type 0) ->
    (exists (a1 : A1) -> B1 a1) = (exists (a2 : A2) -> B2 a2) ->
        forall (a1 : A1) (a2 : A2) -> a1 = a2 -> B1 a1 = B2 a2


let funext : forall (A1 A2 : Type 0) (B1 : A1 -> Type 0) (B2 : A2 -> Type 0) ->
    forall (f1 : forall (a1 : A1) -> B1 a1) (f2 : forall (a2 : A2) -> B2 a2) ->
        (forall (a1 : A1) (a2 : A2) -> a1 = a2 -> f1 a1 = f2 a2) -> f1 = f2

let apply-resp-eq : forall (A1 A2 : Type 0) (B1 : A1 -> Type 0) (B2 : A2 -> Type 0) ->
    forall (f1 : forall (a1 : A1) -> B1 a1) (f2 : forall (a2 : A2) -> B2 a2) ->
        f1 = f2 -> forall (a1 : A1) (a2 : A2) -> a1 = a2 -> f1 a1 = f2 a2


let pairext : forall (A1 A2 : Type 0) (B1 : A1 -> Type 0) (B2 : A2 -> Type 0) ->
    forall (p1 : exists (a1 : A1) -> B1 a1) (p2 : exists (a2 : A2) -> B2 a2) ->
        p1.1 = p2.1 -> p1.2 = p2.2 -> p1 = p2

let fst-resp-eq : forall (A1 A2 : Type 0) (B1 : A1 -> Type 0) (B2 : A2 -> Type 0) ->
    forall (p1 : exists (a1 : A1) -> B1 a1) (p2 : exists (a2 : A2) -> B2 a2) ->
        p1 = p2 -> p1.1 = p2.1

let snd-resp-eq : forall (A1 A2 : Type 0) (B1 : A1 -> Type 0) (B2 : A2 -> Type 0) ->
    forall (p1 : exists (a1 : A1) -> B1 a1) (p2 : exists (a2 : A2) -> B2 a2) ->
        p1 = p2 -> p1.2 = p2.2
"


let prelude_program = Parser.program Lexer.token (Lexing.from_string prelude_src)

let make_globals size =
    let globals = Hashtbl.create (size + List.length prelude_program) in
    List.iter (fun top -> ignore @@ Typecheck.check_top_level globals top) prelude_program;
    globals
