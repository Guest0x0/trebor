
open Syntax
open Value

exception RuntimeError


val apply     : #Context.context -> value -> value -> value
val project   : #Context.context -> value -> [`Fst | `Snd] -> value
val eliminate : #Context.context -> value -> elimination -> value
val force     : #Context.context -> value -> value

val coerce  : #Context.context -> int -> value -> value -> value -> value Lazy.t -> value

val eval : #Context.context -> int -> value list -> Core.expr -> value

val eval_poly : #Context.context -> value list -> Core.expr -> (int -> value)
