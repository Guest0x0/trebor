
open Syntax
open Value


exception UnificationFailure


type renaming

val close_value  : #Context.context -> int -> value -> value
val env_to_elim  : int -> Value.env -> elimination
val env_to_tyfun : #Context.context -> Value.env -> value -> value



val subtyp      : #Context.context -> int -> env -> value -> value -> unit
val unify_typ   : #Context.context -> int -> env -> value -> value -> unit 
val unify_value : #Context.context -> int -> env -> value -> value -> value -> unit

val refine_to_function : #Context.context -> int -> env -> value -> value * (value -> value)
val refine_to_pair     : #Context.context -> int -> env -> value -> value * (value -> value)
