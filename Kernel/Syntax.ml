
type meta = int

type binding_kind  = Bound | Defined

type function_kind = Explicit | Implicit

type field = Fst | Snd


module Value = struct
    type value =
        | Stuck  of head * elimination
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
        | Meta of meta

    and elimination =
        | EmptyElim
        | App   of elimination * value
        | Proj  of elimination * field


    type typ = value

    type env = (binding_kind * string * typ) list

    type meta_info =
        | Free   of typ
        | Solved of typ * value

    type top_level =
        | AxiomDecl  of (int -> value)
        | Definition of (int -> typ) * (int -> value)


    let stuck_local level = Stuck(Local level, EmptyElim) [@@inline]
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
        | Proj   of expr * field

        | TyEq of (expr * expr) * (expr * expr)
        | Coe  of
              { ulevel  : int
              ; coerced : expr
              ; lhs     : expr
              ; rhs     : expr
              ; eq      : expr Lazy.t }

        | Meta   of meta


    type meta_info =
        | Free   of expr
        | Solved of expr * expr


    type env = (binding_kind * string * expr) list


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
        | Var    of int * string
        | Ann    of expr * expr
        | Let    of (string * expr option * expr) * expr

        | Type   of int

        | TyFun  of string * function_kind * expr * expr
        | Fun    of string * function_kind * expr option * expr
        | App    of expr * expr

        | TyPair of string * expr * expr
        | Pair   of expr * expr
        | Proj   of expr * field

        | TyEq   of expr * expr
        | Coe    of expr * expr

        | Hole
        | Explicitfy   of expr
        | ElimImplicit of expr


    type env = (binding_kind * string * expr) list


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
        | CanOnlyShiftGlobal
        | UnsolvedMeta of (meta * Core.meta_info) list * (int * Core.expr * Core.expr) list

    exception Error of span * error
end
