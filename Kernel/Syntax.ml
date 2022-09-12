

type span =
    { lhs : Lexing.position
    ; rhs : Lexing.position }


type expr =
    { shape : expr_shape
    ; span  : span }

and expr_shape =
    | Var    of string
    | Ann    of expr * expr
    | Let    of (string * expr option * expr) * expr

    | Type   of int
    | Shift  of int * expr

    | TyFun  of string * expr * expr
    | Fun    of string * expr option * expr
    | App    of expr * expr

    | TyPair of string * expr * expr
    | Pair   of expr * expr
    | Proj   of expr * [`Fst | `Snd]

    | TyEq   of expr * expr
    | Coe    of expr * expr


type top_level =
    | AxiomDecl  of string * expr
    | Definition of string * expr


type program = (span * top_level) list



type error =
    | SyntaxError  of string
    | UnboundVar   of string
    | CannotInfer  of string
    | WrongType    of (string * Core.term) list * Core.term * string
    | TypeMismatch of (string * Core.term) list * Core.term * Core.term * string
    | RedeclareVar of string
    | RedefineVar  of string

exception Error of span * error
