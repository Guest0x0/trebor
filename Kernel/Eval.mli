
open Syntax
open Value

exception RuntimeError
exception CannotShiftMeta


val apply   : value -> value -> value
val project : value -> [`Fst | `Snd] -> value
val shift   : int -> value -> value

val coerce  : #Context.context -> int -> value -> value -> value -> value Lazy.t -> value

val eliminate : value -> elimination -> value

val force : #Context.context -> value -> value

val eval : #Context.context -> value list -> Core.expr -> value
