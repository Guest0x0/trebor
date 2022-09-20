
open Syntax
open Value


val value_to_core   : #Context.context -> int -> value -> value -> Core.expr
val neutral_to_core : #Context.context -> int -> head -> elimination -> Core.expr
val typ_to_core     : #Context.context -> int -> value -> int * Core.expr

val meta_info_to_core : #Context.context -> meta_info -> Core.meta_info

val env_to_core : #Context.context -> Value.env -> Core.env
