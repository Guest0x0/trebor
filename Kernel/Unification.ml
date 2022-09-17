
open Syntax
open Value
open Eval



exception UnificationFailure

class context = object(self)
    inherit Context.context

    val mutable equations : (int * (string * value) list * value * value) list = []


    method subtyp    = self#unify_typ_aux `Subtyp
    method unify_typ = self#unify_typ_aux `Equal

    method unify_value level env typ v1 v2 =
        match typ, v1, v2 with
        | Type _, typv1, typv2 ->
            self#unify_typ_aux `Equal level env typv1 typv2

        | TyFun(name, a, b), f1, f2 ->
            let var = stuck_local level in
            self#unify_value (level + 1) ((name, a) :: env) (b var) (apply f1 var) (apply f2 var)

        | TyPair(_, a, b), p1, p2 ->
            let fst1 = project p1 `Fst in
            let fst2 = project p2 `Fst in
            self#unify_value level env a fst1 fst2;
            self#unify_value level env (b fst1) (project p1 `Snd) (project p2 `Snd)

        | TyEq _, _, _ ->
            ()

        | Stuck _, Stuck(head1, elim1), Stuck(head2, elim2) ->
            let head_typ = self#unify_head level env head1 head2 in
            ignore (self#unify_elim level env head1 head_typ elim1 elim2)

        | _ ->
            raise RuntimeError


    method private unify_head level env head1 head2 =
        match head1, head2 with
        | TopVar(shift1, name1), TopVar(shift2, name2) when shift1 = shift2 && name1 = name2 ->
            let (AxiomDecl typ | Definition(typ, _)) = self#find_global name1 in
            typ
        | Local lvl1, Local lvl2 when lvl1 = lvl2 ->
            snd (List.nth env (level - lvl1 - 1))
        | Coe coe1, Coe coe2 when coe1.ulevel = coe2.ulevel ->
            self#unify_value level env (Type coe1.ulevel) coe1.lhs coe2.lhs;
            self#unify_value level env (Type coe1.ulevel) coe1.rhs coe2.rhs;
            self#unify_value level env coe1.lhs coe1.coerced coe2.coerced;
            coe1.rhs
        | _ ->
            raise UnificationFailure


    method private unify_elim level env head head_typ elim1 elim2 =
        match elim1, elim2 with
        | EmptyElim, EmptyElim ->
            head_typ
        | App(elim1', arg1), App(elim2', arg2) ->
            begin match self#unify_elim level env head head_typ elim1' elim2' with
            | TyFun(_, a, b) -> self#unify_value level env a arg1 arg2; b arg1
            | _              -> raise RuntimeError
            end
        | Proj(elim1', field1), Proj(elim2', field2) when field1 = field2 ->
            begin match self#unify_elim level env head head_typ elim1' elim2', field1 with
            | TyPair(_, a, b), `Fst -> a
            | TyPair(_, a, b), `Snd -> b @@ Stuck(head, Proj(elim1', `Fst))
            | _                     -> raise RuntimeError
            end
        | _ ->
            raise UnificationFailure



    method private unify_typ_aux (mode : [`Subtyp | `Equal]) level env sub sup =
        match sub, sup with
        | Type ulevel1, Type ulevel2 ->
            begin match mode with
            | `Subtyp when ulevel1 <= ulevel2 -> ()
            | `Equal  when ulevel1 =  ulevel2 -> ()
            | _                               -> raise UnificationFailure
            end

        | TyFun (name, a1, b1), TyFun (_, a2, b2) ->
            self#unify_typ_aux mode level env a2 a1;
            let var = stuck_local level in
            self#unify_typ_aux mode (level + 1) ((name, a2) :: env) (b1 var) (b2 var)

        | TyPair(name, a1, b1), TyPair(_, a2, b2) ->
            self#unify_typ_aux mode level env a1 a2;
            let var = stuck_local level in
            self#unify_typ_aux mode (level + 1) ((name, a1) :: env) (b1 var) (b2 var)

        | TyEq((lhs1, lhs_typ1), (rhs1, rhs_typ1))
        , TyEq((lhs2, lhs_typ2), (rhs2, rhs_typ2)) ->
            self#unify_typ_aux mode level env lhs_typ1 lhs_typ2;
            self#unify_typ_aux mode level env rhs_typ1 rhs_typ2;
            self#unify_value level env lhs_typ1 lhs1 lhs2;
            self#unify_value level env rhs_typ1 rhs1 rhs2

        | Stuck(head1, elim1), Stuck(head2, elim2) ->
            let head_typ = self#unify_head level env head1 head2 in
            ignore (self#unify_elim level env head1 head_typ elim1 elim2)

        | _ ->
            raise UnificationFailure
end
