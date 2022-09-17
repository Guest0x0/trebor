
type meta = int

module Value = struct
    type value =
        | Stuck  of head * elimination
        | Type   of int
        | TyFun  of string * value * (value -> value)
        | Fun    of string * (value -> value)
        | TyPair of string * value * (value -> value)
        | Pair   of value * value
        | TyEq   of (value * value) * (value * value)

    and head =
        | Local  of int
        | TopVar of int * string
        | Coe of
              { ulevel : int
              ; coerced : value
              ; lhs     : value
              ; rhs     : value
              ; eq      : value Lazy.t }
        | Meta of int * meta

    and elimination =
        | EmptyElim
        | App   of elimination * value
        | Proj  of elimination * [`Fst | `Snd]


    type meta_info =
        | Free   of string * value
        | Solved of value



    type top_level =
        | AxiomDecl  of value
        | Definition of value * value


    let stuck_local level = Stuck(Local level, EmptyElim) [@@inline]
end


module Core = struct
    type expr =
        | TopVar of string
        | Local  of int
        | Let    of string * expr * expr

        | Type   of int
        | Shift  of int * expr

        | TyFun of string * expr * expr
        | Fun   of string * expr
        | App   of expr * expr

        | TyPair of string * expr * expr
        | Pair   of expr * expr
        | Proj   of expr * [`Fst | `Snd]

        | TyEq of (expr * expr) * (expr * expr)
        | Coe  of
              { ulevel  : int
              ; coerced : expr
              ; lhs     : expr
              ; rhs     : expr
              ; eq      : expr Lazy.t }

        | Meta   of string * meta



    type top_level =
        | AxiomDecl  of string * expr
        | Definition of string * expr * expr
end


type span =
    { lhs : Lexing.position
    ; rhs : Lexing.position }


module Surface = struct
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
        | Definition of string * expr option * expr


    type program = (span * top_level) list
end


module Error = struct
    type error =
        | SyntaxError  of string
        | UnboundVar   of string
        | CannotInfer  of string
        | WrongType    of (string * Core.expr) list * Core.expr * string
        | TypeMismatch of (string * Core.expr) list * Core.expr * Core.expr * string
        | RedeclareVar of string
        | RedefineVar  of string

    exception Error of span * error
end
