
open Syntax
open Value


val value_to_core : #Context.context -> int -> Value.env -> value -> value -> Core.expr
val typ_to_core   : #Context.context -> int -> Value.env -> value -> int * Core.expr

val env_to_core : #Context.context -> Value.env -> Core.env

module Simple : sig
    val value_to_core : int -> value -> Core.expr
    val head_to_core  : int -> head  -> Core.expr
end
