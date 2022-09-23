
open Syntax
open Value


exception CannotSolveYet
exception UnificationFailure


val close_value : #Context.context -> int -> value -> value -> value
val env_to_typ  : #Context.context -> int -> Value.env -> value -> value
val env_to_elim : int -> Value.env -> elimination



type equation =
    { level : int
    ; mode  : [`Value of value | `Type]
    ; lhs   : value
    ; rhs   : value }

class context : object
    inherit Context.context

    method solve_all : unit
    method dump_equations : equation list

    method subtyp    : int -> value -> value -> unit
    method unify_typ : int -> value -> value -> unit 

    method refine_to_function : int -> env -> value -> value * (value -> value)
    method refine_to_pair     : int -> env -> value -> value * (value -> value)
end
