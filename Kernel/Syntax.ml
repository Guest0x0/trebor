
type meta = int

type function_kind = Explicit | Implicit

module Value = struct
    type value =
        | Stuck  of value * head * elimination
        | Type   of int
        | TyFun  of string * function_kind * value * (value -> value)
        | Fun    of string * (value -> value)
        | TyPair of string * value * (value -> value)
        | Pair   of value * value
        | TyEq   of (value * value) * (value * value)

    and head =
        | Local  of int
        | TopVar of int * string
        | Coe of
              { ulevel  : int
              ; coerced : value
              ; lhs     : value
              ; rhs     : value
              ; eq      : value Lazy.t }
        | Meta of string * meta

    and elimination =
        | EmptyElim
        | App   of elimination * value * value
        | Proj  of elimination * [`Fst | `Snd]


    type neutral = head * elimination


    type meta_info =
        | Free   of value
        | Solved of value * value


    type env = (string * value * [`Bound | `Defined]) list


    type top_level =
        | AxiomDecl  of value
        | Definition of value * value


    let stuck_local level typ = Stuck(typ, Local level, EmptyElim) [@@inline]
end


module Core = struct
    type expr =
        | TopVar of string
        | Local  of int
        | Let    of string * expr * expr

        | Type   of int
        | Shift  of int * expr

        | TyFun of string * function_kind * expr * expr
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


    type meta_info =
        | Free   of expr
        | Solved of expr * expr


    type env = (string * expr * [`Bound | `Defined]) list


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

        | TyFun  of string * function_kind * expr * expr
        | Fun    of string * function_kind * expr option * expr
        | App    of expr * expr

        | TyPair of string * expr * expr
        | Pair   of expr * expr
        | Proj   of expr * [`Fst | `Snd]

        | TyEq   of expr * expr
        | Coe    of expr * expr

        | Hole
        | Explicitfy of expr


    type env = (string * expr * [`Bound | `Defined]) list


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
        | WrongType    of Core.env * Core.expr * string
        | TypeMismatch of Core.env * Core.expr * Core.expr * string
        | RedeclareVar of string
        | RedefineVar  of string
        | UnsolvedMeta of (meta * Core.meta_info) list

    exception Error of span * error
end
