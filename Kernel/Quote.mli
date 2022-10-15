
open Syntax
open Value


val value_to_core : #Context.context -> int -> value -> Core.expr
val head_to_core  : #Context.context -> int -> head  -> Core.expr
val elim_to_core  : #Context.context -> int -> Core.expr -> elimination -> Core.expr

val meta_info_to_core : #Context.context -> meta_info -> Core.meta_info

val env_to_core : #Context.context -> Value.env -> Core.env



val infer_neutral : #Context.context -> int -> env -> head -> elimination -> typ * Core.expr
val infer_ulevel  : #Context.context -> int -> env -> value               -> int * Core.expr
