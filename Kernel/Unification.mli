
open Syntax
open Value


exception CannotSolveYet
exception UnificationFailure


val close_value : #Context.context -> int -> value -> value -> value
val env_to_typ  : #Context.context -> int -> Value.env -> value -> value
val env_to_elim : #Context.context -> int -> Value.env -> elimination

class context : object
    inherit Context.context

    method subtyp    : int -> value -> value -> unit
    method unify_typ : int -> value -> value -> unit 

    method solve_all : unit
end
