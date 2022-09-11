


type core =
    | C_TopVar of string
    | C_Local  of int
    | C_Let    of (string * core) * core

    | C_Type  of int
    | C_Shift of int * core

    | C_TyFun of (string * core) * core
    | C_Fun   of string * core
    | C_App   of core * core

    | C_TyPair of (string * core) * core
    | C_Pair   of core * core
    | C_Proj   of core * [`Fst | `Snd]

    | C_TyEq of (core * core) * (core * core)
    | C_Coe  of
          { target : core
          ; eq     : core Lazy.t
          ; lhs    : core
          ; rhs    : core }

type core_top_level =
    | C_AxiomDecl  of string * core
    | C_Definition of string * core * core



type span =
    { lhs : Lexing.position
    ; rhs : Lexing.position }

let dummy_span = { lhs = Lexing.dummy_pos; rhs = Lexing.dummy_pos }


type expr =
    { shape : expr_shape
    ; span  : span }

and expr_shape =
    | E_Var    of string
    | E_Ann    of expr * expr
    | E_Let    of (string * expr option * expr) * expr

    | E_Type   of int
    | E_Shift  of int * expr

    | E_TyFun  of (string * expr) * expr
    | E_Fun    of (string * expr option) * expr
    | E_App    of expr * expr

    | E_TyPair of (string * expr) * expr
    | E_Pair   of expr * expr
    | E_Proj   of expr * [`Fst | `Snd]

    | E_TyEq   of expr * expr
    | E_Coe    of expr * expr


type top_level =
    | AxiomDecl  of string * expr
    | Definition of string * expr



type error =
    | UnboundVar   of string
    | CannotInfer  of string
    | WrongType    of (string * core) list * core * string
    | TypeMismatch of (string * core) list * core * core * string

exception TypeError of span * error
