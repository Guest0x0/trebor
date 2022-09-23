
open Syntax
open Value

exception RuntimeError


val apply   : value -> value -> value
val project : value -> [`Fst | `Snd] -> value

val coerce  : #Context.context -> int -> value -> value -> value -> value Lazy.t -> value

val eliminate : value -> elimination -> value

val force : #Context.context -> value -> value

val eval : #Context.context -> int -> value list -> Core.expr -> value

val eval_poly : #Context.context -> value list -> Core.expr -> (int -> value)
