
open Core

let parse_lexbuf lexbuf = Parser.program Lexer.token lexbuf
let parse_string src    = parse_lexbuf (Lexing.from_string src)


let global = Hashtbl.create 37
let _ = Hashtbl.add_seq global
        (List.to_seq Typecheck.prelude
         |> Seq.map (fun (name, typ) -> (name, Normalization.V_Axiom typ)))


let _ = Typecheck.process_program global @@ parse_string "
let eta : forall (A : Type 0) (B : A -> Type 0) (f : forall (a : A) -> B a) ->
    f = (fun (a : A) -> f a)
let eta = fun A B f -> eq-refl (forall (a : A) -> B a) f

let omega : forall (A : Type 0) -> A = (A -> A) -> A -> A
let omega = fun A eq x -> (x :> eq) x

let type-of-bad = forall (A : Type 0) -> A = (A -> A) -> A

let bad : type-of-bad
let bad = fun A eq ->
    omega A eq (omega A eq :> eq-symm (Type 0) (Type 0) A (A -> A) eq)

let normalize-bad = fun (P : type-of-bad -> Type 0) (f : type-of-bad -> P bad) -> f bad
"
