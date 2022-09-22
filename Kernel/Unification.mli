
open Syntax
open Value


exception CannotSolveYet
exception UnificationFailure


val close_value : #Context.context -> int -> value -> value -> value
val env_to_typ  : #Context.context -> int -> Value.env -> value -> value
val env_to_elim : int -> Value.env -> elimination

class context : object
    inherit Context.context

    method subtyp    : int -> value -> value -> unit
    method unify_typ : int -> value -> value -> unit 

    method refine_to_function : int -> env -> value -> value * (value -> value)
    method refine_to_pair     : int -> env -> value -> value * (value -> value)
    method insert_implicit    : int -> env -> Core.expr -> value -> Core.expr * value

    method solve_all : unit
end
