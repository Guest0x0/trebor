
open Syntax
open Value


exception CannotSolveYet
exception UnificationFailure

class context : object
    inherit Context.context

    method subtyp    : int -> Value.env -> value -> value -> unit
    method unify_typ : int -> Value.env -> value -> value -> unit 

    method solve_all : unit
end
