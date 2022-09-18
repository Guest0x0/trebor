
open Syntax

type context

val empty_ctx : context


val infer : #Unification.context -> context -> Surface.expr -> Value.value * Core.expr
val check : string -> #Unification.context -> context -> Value.value -> Surface.expr -> Core.expr

val check_typ : #Unification.context -> context -> Surface.expr -> int * Core.expr

val check_env : #Unification.context -> Surface.env -> context * Core.env

val check_top_level : #Unification.context -> span * Surface.top_level -> Core.top_level
val check_program   : #Unification.context -> Surface.program -> Core.top_level list
