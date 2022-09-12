
type term =
    | TopVar of string
    | Local  of int
    | Let    of string * term * term

    | Type   of int
    | Shift  of int * term

    | TyFun of string * term * term
    | Fun   of string * term
    | App   of term * term

    | TyPair of string * term * term
    | Pair   of term * term
    | Proj   of term * [`Fst | `Snd]

    | TyEq of (term * term) * (term * term)
    | Coe  of
          { ulevel  : int
          ; coerced : term
          ; lhs     : term
          ; rhs     : term
          ; eq      : term Lazy.t }



type top_level =
    | AxiomDecl  of string * term
    | Definition of string * term * term



let rec term_equal tm1 tm2 =
    match tm1, tm2 with
    | TopVar name1       , TopVar name2        -> name1 = name2
    | Local  idx1        , Local  idx2         -> idx1 = idx2
    | Let(_, rhs1, body1), Let(_, rhs2, body2) -> term_equal rhs1 rhs2 && term_equal body1 body2

    | Type ulevel1       , Type ulevel2        -> ulevel1 = ulevel2
    | Shift(level1, tm1'), Shift(level2, tm2') -> level1 = level2 && term_equal tm1' tm2'

    | TyFun(_, a1, b1), TyFun(_, a2, b2) -> term_equal a1 a2 && term_equal b1 b2
    | Fun(_, body1)   , Fun(_, body2)    -> term_equal body1 body2
    | App(f1, a1)     , App(f2, a2)      -> term_equal f1 f2 && term_equal a1 a2

    | TyPair(_, a1, b1), TyPair(_, a2, b2) -> term_equal a1 a2 && term_equal b1 b2
    | Pair(fst1, snd1) , Pair(fst2, snd2)  -> term_equal fst1 fst2 && term_equal snd1 snd2
    | Proj(p1, field1) , Proj(p2, field2)  -> field1 = field2 && term_equal p1 p2

    | TyEq( (lhs1, lhs_typ1), (rhs1, rhs_typ1) )
    , TyEq( (lhs2, lhs_typ2), (rhs2, rhs_typ2) ) ->
        term_equal lhs1 lhs2
        && term_equal lhs_typ1 lhs_typ2
        && term_equal rhs1 rhs2
        && term_equal rhs_typ1 rhs_typ2
    | Coe coe1, Coe coe2 ->
        term_equal coe1.coerced coe2.coerced
        && term_equal coe1.lhs coe2.lhs
        && term_equal coe1.rhs coe2.rhs

    | _ ->
        false
