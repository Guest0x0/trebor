
open Syntax

type context

val empty_ctx : context


val infer : #Context.context -> context -> Surface.expr -> Value.value * Core.expr
val check : string -> #Context.context -> context -> Value.value -> Surface.expr -> Core.expr

val check_typ : #Context.context -> context -> Surface.expr -> int * Core.expr

val check_env : #Context.context -> Surface.env -> context * Core.env

val check_top_level : #Context.context -> span * Surface.top_level -> Core.top_level
val check_program   : #Context.context -> Surface.program -> Core.top_level list
