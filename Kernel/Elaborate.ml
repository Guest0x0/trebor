
type context =
    { level : int
    ; venv  : Value.value list
    ; tenv  : (string * Value.value) list }


let empty_ctx =
    { level = 0
    ; venv  = []
    ; tenv  = [] }


let add_local name typ ?value ctx =
    let value =
        match value with
        | Some value -> value
        | None       -> Value.stuck_local ctx.level
    in
    { level = ctx.level + 1
    ; venv  = value :: ctx.venv
    ; tenv  = (name, typ) :: ctx.tenv }


let find_local name ctx =
    let rec loop idx = function
        | [] ->
            raise Not_found
        | (name', typ) :: _ when name = name' ->
            idx, typ
        | _ :: rest ->
            loop (idx + 1) rest
    in
    loop 0 ctx.tenv



let wrong_type g ctx span typ expected =
    let ctxC = Value.env_to_core_ctx g ctx.tenv in
    let _, typC = Value.typ_to_core g ctx.level ctx.tenv typ in
    raise @@ Syntax.Error(span, WrongType(ctxC, typC, expected))

let type_mismatch g ctx span expected actual err_ctx =
    let ctxC = Value.env_to_core_ctx g ctx.tenv in
    let _, expectedC = Value.typ_to_core g ctx.level ctx.tenv expected in
    let _, actualC = Value.typ_to_core g ctx.level ctx.tenv actual in
    raise @@ Syntax.Error(span, TypeMismatch(ctxC, expectedC, actualC, err_ctx))


let rec infer g ctx expr =
    match expr.Syntax.shape with
    | Syntax.Var name ->
        begin match find_local name ctx with
        | idx, typ ->
            ( typ
            , Core.Local idx )
        | exception Not_found ->
            match Hashtbl.find g name with
            | Value.(AxiomDecl typ | Definition(typ, _)) ->
                ( typ
                , Core.TopVar name )
            | exception Not_found ->
                raise @@ Syntax.Error(expr.span, UnboundVar name)
        end

    | Syntax.Let((name, ann, rhs), body) ->
        let rhs_typ, c_rhs =
            match ann with
            | Some ann ->
                let _, c_ann = check_typ g ctx ann in
                let rhs_typ = Value.eval g ctx.venv c_ann in
                (rhs_typ, check "type annotation" g ctx rhs_typ rhs)
            | None ->
                infer g ctx rhs
        in
        let ctx' = add_local name rhs_typ ~value:(Value.eval g ctx.venv c_rhs) ctx in
        let res_typ, c_body = infer g ctx' body in
        ( res_typ
        , Core.Let(name, c_rhs, c_body ) )


    | Syntax.Ann(expr, typ) ->
        let _, ctyp = check_typ g ctx typ in
        let typV = Value.eval g ctx.venv ctyp in
        let exprC = check "type annotation" g ctx typV expr in
        ( typV, exprC )

    | Syntax.Type ulevel ->
        ( Type(ulevel + 1)
        , Core.Type ulevel )

    | Syntax.Shift(level , expr') ->
        let typ, core = infer g ctx expr' in
        ( Value.shift level typ
        , Core.Shift(level, core) )

    | Syntax.TyFun(name, a, b) ->
        let ul_a, ca = check_typ g ctx a in
        let va = Value.eval g ctx.venv ca in
        let ul_b, cb = check_typ g (add_local name va ctx) b in
        ( Value.Type(max ul_a ul_b)
        , Core.TyFun(name, ca, cb) )

    | Syntax.Fun(_, None, _) ->
        raise @@ Syntax.Error(expr.span, CannotInfer "function without parameter annotation")

    | Syntax.Fun(name, Some param_typ, body) ->
        let _, param_typC = check_typ g ctx param_typ in
        let param_typV = Value.eval g ctx.venv param_typC in
        let ctx' = add_local name param_typV ctx in
        let ret_typV, bodyC = infer g ctx' body in
        let _, ret_typC = Value.typ_to_core g ctx'.level ctx'.tenv ret_typV in
        ( Value.TyFun(name, param_typV, fun v -> Value.eval g (v :: ctx.venv) ret_typC)
        , Core.Fun(name, bodyC) )

    | Syntax.App(func, arg) ->
        begin match infer g ctx func with
        | Value.TyFun(_, a, b), funcC ->
            let argC = check "function application" g ctx a arg in
            ( b (Value.eval g ctx.venv argC)
            , Core.App(funcC, argC) )
        | typV, _ ->
            wrong_type g ctx expr.span typV "function"
        end

    | Syntax.TyPair(name, fst_typ, snd_typ) ->
        let ul_fst, fst_typC = check_typ g ctx fst_typ in
        let fst_typV  = Value.eval g ctx.venv fst_typC in
        let ul_snd, snd_typC = check_typ g (add_local name fst_typV ctx) snd_typ in
        ( Type(max ul_fst ul_snd)
        , Core.TyPair(name, fst_typC, snd_typC) )

    | Syntax.Pair(fst, snd) ->
        let fst_typ, fstC = infer g ctx fst in
        let snd_typ, sndC = infer g ctx snd in
        ( Value.TyPair("", fst_typ, fun _ -> snd_typ)
        , Core.Pair(fstC, sndC) )

    | Syntax.Proj(pair, field) ->
        begin match infer g ctx pair with
        | TyPair(_, fst_typ, snd_typ), pairC ->
            begin match field with
            | `Fst ->
                ( fst_typ
                , Core.Proj(pairC, field) )
            | `Snd ->
                let fstV = Value.project (Value.eval g ctx.venv pairC) `Fst in
                ( snd_typ fstV
                , Core.Proj(pairC, field) )
            end
        | typV, _ ->
            wrong_type g ctx expr.span typV "pair"
        end

    | Syntax.TyEq(lhs, rhs) ->
        let lhs_typ, lhsC = infer g ctx lhs in
        let rhs_typ, rhsC = infer g ctx rhs in
        let ul_lhs, lhs_typC = Value.typ_to_core g ctx.level ctx.tenv lhs_typ in
        let ul_rhs, rhs_typC = Value.typ_to_core g ctx.level ctx.tenv rhs_typ in
        ( Type(max ul_lhs ul_rhs)
        , Core.TyEq((lhsC, lhs_typC), (rhsC, rhs_typC)) )

    | Syntax.Coe(coerced, eq) ->
        begin match infer g ctx eq with
        | TyEq((lhs, Type ul_lhs), (rhs, Type ul_rhs)), eqC ->
            let coercedC = check "coerced value" g ctx lhs coerced in
            let ul_lhs, lhsC = Value.typ_to_core g ctx.level ctx.tenv lhs in
            let ul_rhs, rhsC = Value.typ_to_core g ctx.level ctx.tenv rhs in
            ( rhs
            , Core.Coe { ulevel  = max ul_lhs ul_rhs
                       ; coerced = coercedC
                       ; lhs     = lhsC
                       ; rhs     = rhsC
                       ; eq      = Lazy.from_val eqC } )
        | typV, _ ->
            wrong_type g ctx expr.span typV "equality"
        end

and check err_ctx g ctx typ expr =
    match typ, expr.shape with
    | _, Syntax.Let((name, ann, rhs), body) ->
        let rhs_typ, rhsC =
            match ann with
            | Some ann ->
                let _, annC = check_typ g ctx ann in
                let rhs_typ = Value.eval g ctx.venv annC in
                (rhs_typ, check "type annotation" g ctx rhs_typ rhs)
            | None ->
                infer g ctx rhs
        in
        let ctx' = add_local name rhs_typ ~value:(Value.eval g ctx.venv rhsC) ctx in
        let bodyC = check err_ctx g ctx' typ body in
        Core.Let(name, rhsC, bodyC)

    | TyFun(_, param_typ, ret_typ), Syntax.Fun(name, ann, body) ->
        let param_typ =
            match ann with
            | Some ann ->
                let _, annC = check_typ g ctx ann in
                let annV = Value.eval g ctx.venv annC in
                begin match Unification.subtyp g ctx.level ctx.tenv param_typ annV with
                | () ->
                    annV
                | exception Unification.UnificationFailure ->
                    type_mismatch g ctx ann.span param_typ annV "function annotation"
                end
            | None ->
                param_typ
        in
        let ret_typ = ret_typ @@ Value.stuck_local ctx.level in
        let bodyC = check err_ctx g (add_local name param_typ ctx) ret_typ body in
        Core.Fun(name, bodyC)

    | TyPair(_, fst_typ, snd_typ), Syntax.Pair(fst, snd) ->
        let fstC = check err_ctx g ctx fst_typ fst in
        let fstV = Value.eval g ctx.venv fstC in
        let sndC = check err_ctx g ctx (snd_typ fstV) snd in
        Core.Pair(fstC, sndC)

    | _ ->
        let actual_typ, exprC = infer g ctx expr in
        begin match Unification.subtyp g ctx.level ctx.tenv actual_typ typ with
        | () ->
            exprC
        | exception Unification.UnificationFailure ->
            type_mismatch g ctx expr.span typ actual_typ err_ctx
        end

and check_typ g ctx expr =
    match infer g ctx expr with
    | Type ulevel, exprC ->
        ulevel, exprC
    | typV, _ ->
        wrong_type g ctx expr.span typV "type"



let rec check_context g ctx =
    match ctx with
    | [] ->
        [], empty_ctx
    | (name, typ) :: ctx' ->
        let ctxC, elab_ctx = check_context g ctx' in
        let _, typC = check_typ g elab_ctx typ in
        ( (name, typC) :: ctxC
        , add_local name (Value.eval g elab_ctx.venv typC) elab_ctx )



let check_top_level g (span, top) =
    match top with
    | Syntax.AxiomDecl(name, typ) ->
        begin match Hashtbl.find_opt g name with
        | Some _ -> raise (Syntax.Error (span, RedeclareVar name))
        | None   -> ()
        end;
        let _, typC = check_typ g empty_ctx typ in
        Hashtbl.add g name (Value.AxiomDecl(Value.eval g [] typC));
        Core.AxiomDecl(name, typC)

    | Syntax.Definition(name, def) ->
        let typ, defC =
            match Hashtbl.find_opt g name with
            | Some(Value.AxiomDecl typ) ->
                (typ, check "global definition" g empty_ctx typ def)
            | Some(Value.Definition _)  ->
                raise (Syntax.Error (span, RedefineVar name))
            | None ->
                infer g empty_ctx def
        in
        Hashtbl.add g name (Value.Definition(typ, Value.eval g [] defC));
        Core.Definition(name, snd (Value.typ_to_core g 0 [] typ), defC)



let rec check_program g = function
    | []          -> []
    | top :: tops ->
        let c_top = check_top_level g top in
        c_top :: check_program g tops
