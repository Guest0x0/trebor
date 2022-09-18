
open Syntax
open Eval

type context =
    { level : int
    ; venv  : Value.value list
    ; tenv  : Value.env }


let empty_ctx =
    { level = 0
    ; venv  = []
    ; tenv  = [] }


let add_local name typ ?value ctx =
    let value, kind =
        match value with
        | Some value -> value, `Defined
        | None       -> Value.stuck_local ctx.level, `Bound
    in
    { level = ctx.level + 1
    ; venv  = value :: ctx.venv
    ; tenv  = (name, typ, kind) :: ctx.tenv }


let find_local name ctx =
    let rec loop idx = function
        | [] ->
            raise Not_found
        | (name', typ, _) :: _ when name = name' ->
            idx, typ
        | _ :: rest ->
            loop (idx + 1) rest
    in
    loop 0 ctx.tenv



let wrong_type g ctx span typ expected =
    let ctxC = Quote.env_to_core g ctx.tenv in
    let _, typC = Quote.typ_to_core g ctx.level ctx.tenv typ in
    raise @@ Error.Error(span, WrongType(ctxC, typC, expected))

let type_mismatch g ctx span expected actual err_ctx =
    let ctxC = Quote.env_to_core g ctx.tenv in
    let _, expectedC = Quote.typ_to_core g ctx.level ctx.tenv expected in
    let _, actualC = Quote.typ_to_core g ctx.level ctx.tenv actual in
    raise @@ Error.Error(span, TypeMismatch(ctxC, expectedC, actualC, err_ctx))



let abstract_ctx g ctx ret_typ =
    let _, expr = Quote.typ_to_core g ctx.level ctx.tenv ret_typ in
    List.fold_left
        (fun typ (_, param_typ, kind) ->
                    match kind with
                    | `Defined -> typ
                    | `Bound   -> fun env -> Value.TyFun("", param_typ, fun v -> typ (v :: env)))
        (fun env -> Eval.eval g env expr) ctx.tenv
    @@ []

let apply_ctxV f ctx =
    let args =
        ctx.tenv
        |> List.mapi (fun lvl (_, _, kind) -> kind, Value.stuck_local lvl)
        |> List.filter_map (fun (kind, arg) -> if kind = `Bound then Some arg else None)
    in
    List.fold_left Eval.apply f args

let apply_ctxC f ctx =
    let args =
        ctx.tenv
        |> List.mapi (fun lvl (_, _, kind) -> kind, Core.Local(ctx.level - lvl - 1))
        |> List.filter_map (fun (kind, arg) -> if kind = `Bound then Some arg else None)
    in
    List.fold_left (fun f a -> Core.App(f, a)) f args


let rec infer g ctx expr =
    match expr.Surface.shape with
    | Surface.Var name ->
        begin match find_local name ctx with
        | idx, typ ->
            ( typ
            , Core.Local idx )
        | exception Not_found ->
            match g#find_global name with
            | Value.(AxiomDecl typ | Definition(typ, _)) ->
                ( typ
                , Core.TopVar name )
            | exception Not_found ->
                raise @@ Error.Error(expr.span, UnboundVar name)
        end

    | Surface.Let((name, ann, rhs), body) ->
        let rhs_typ, c_rhs =
            match ann with
            | Some ann ->
                let _, c_ann = check_typ g ctx ann in
                let rhs_typ = Eval.eval g ctx.venv c_ann in
                (rhs_typ, check "type annotation" g ctx rhs_typ rhs)
            | None ->
                infer g ctx rhs
        in
        let ctx' = add_local name rhs_typ ~value:(Eval.eval g ctx.venv c_rhs) ctx in
        let res_typ, c_body = infer g ctx' body in
        ( res_typ
        , Core.Let(name, c_rhs, c_body ) )


    | Surface.Ann(expr, typ) ->
        let _, ctyp = check_typ g ctx typ in
        let typV = Eval.eval g ctx.venv ctyp in
        let exprC = check "type annotation" g ctx typV expr in
        ( typV, exprC )

    | Surface.Type ulevel ->
        ( Type(ulevel + 1)
        , Core.Type ulevel )

    | Surface.Shift(level , expr') ->
        let typ, core = infer g ctx expr' in
        ( Eval.shift level typ
        , Core.Shift(level, core) )

    | Surface.TyFun(name, a, b) ->
        let ul_a, ca = check_typ g ctx a in
        let va = Eval.eval g ctx.venv ca in
        let ul_b, cb = check_typ g (add_local name va ctx) b in
        ( Value.Type(max ul_a ul_b)
        , Core.TyFun(name, ca, cb) )

    | Surface.Fun(_, None, _) ->
        raise @@ Error.Error(expr.span, CannotInfer "function without parameter annotation")

    | Surface.Fun(name, Some param_typ, body) ->
        let _, param_typC = check_typ g ctx param_typ in
        let param_typV = Eval.eval g ctx.venv param_typC in
        let ctx' = add_local name param_typV ctx in
        let ret_typV, bodyC = infer g ctx' body in
        let _, ret_typC = Quote.typ_to_core g ctx'.level ctx'.tenv ret_typV in
        ( Value.TyFun(name, param_typV, fun v -> Eval.eval g (v :: ctx.venv) ret_typC)
        , Core.Fun(name, bodyC) )

    | Surface.App(func, arg) ->
        begin match infer g ctx func with
        | Value.TyFun(_, a, b), funcC ->
            let argC = check "function application" g ctx a arg in
            ( b (Eval.eval g ctx.venv argC)
            , Core.App(funcC, argC) )
        | typV, _ ->
            wrong_type g ctx expr.span typV "function"
        end

    | Surface.TyPair(name, fst_typ, snd_typ) ->
        let ul_fst, fst_typC = check_typ g ctx fst_typ in
        let fst_typV  = Eval.eval g ctx.venv fst_typC in
        let ul_snd, snd_typC = check_typ g (add_local name fst_typV ctx) snd_typ in
        ( Type(max ul_fst ul_snd)
        , Core.TyPair(name, fst_typC, snd_typC) )

    | Surface.Pair(fst, snd) ->
        let fst_typ, fstC = infer g ctx fst in
        let snd_typ, sndC = infer g ctx snd in
        ( Value.TyPair("", fst_typ, fun _ -> snd_typ)
        , Core.Pair(fstC, sndC) )

    | Surface.Proj(pair, field) ->
        begin match infer g ctx pair with
        | TyPair(_, fst_typ, snd_typ), pairC ->
            begin match field with
            | `Fst ->
                ( fst_typ
                , Core.Proj(pairC, field) )
            | `Snd ->
                let fstV = Eval.project (Eval.eval g ctx.venv pairC) `Fst in
                ( snd_typ fstV
                , Core.Proj(pairC, field) )
            end
        | typV, _ ->
            wrong_type g ctx expr.span typV "pair"
        end

    | Surface.TyEq(lhs, rhs) ->
        let lhs_typ, lhsC = infer g ctx lhs in
        let rhs_typ, rhsC = infer g ctx rhs in
        let ul_lhs, lhs_typC = Quote.typ_to_core g ctx.level ctx.tenv lhs_typ in
        let ul_rhs, rhs_typC = Quote.typ_to_core g ctx.level ctx.tenv rhs_typ in
        ( Type(max ul_lhs ul_rhs)
        , Core.TyEq((lhsC, lhs_typC), (rhsC, rhs_typC)) )

    | Surface.Coe(coerced, eq) ->
        begin match infer g ctx eq with
        | TyEq((lhs, Type ul_lhs), (rhs, Type ul_rhs)), eqC ->
            let coercedC = check "coerced value" g ctx lhs coerced in
            let ul_lhs, lhsC = Quote.typ_to_core g ctx.level ctx.tenv lhs in
            let ul_rhs, rhsC = Quote.typ_to_core g ctx.level ctx.tenv rhs in
            ( rhs
            , Core.Coe { ulevel  = max ul_lhs ul_rhs
                       ; coerced = coercedC
                       ; lhs     = lhsC
                       ; rhs     = rhsC
                       ; eq      = Lazy.from_val eqC } )
        | typV, _ ->
            wrong_type g ctx expr.span typV "equality"
        end

    | Surface.Hole ->
        let typ_meta = g#fresh_meta (abstract_ctx g ctx (Value.Type 0)) in
        let typ = apply_ctxV Value.(Stuck(Meta("", typ_meta), EmptyElim)) ctx in
        let hole_meta = g#fresh_meta (abstract_ctx g ctx typ) in
        typ, apply_ctxC (Core.Meta("", hole_meta)) ctx

and check err_ctx g ctx typ expr =
    match typ, expr.shape with
    | _, Surface.Let((name, ann, rhs), body) ->
        let rhs_typ, rhsC =
            match ann with
            | Some ann ->
                let _, annC = check_typ g ctx ann in
                let rhs_typ = Eval.eval g ctx.venv annC in
                (rhs_typ, check "type annotation" g ctx rhs_typ rhs)
            | None ->
                infer g ctx rhs
        in
        let ctx' = add_local name rhs_typ ~value:(Eval.eval g ctx.venv rhsC) ctx in
        let bodyC = check err_ctx g ctx' typ body in
        Core.Let(name, rhsC, bodyC)

    | TyFun(_, param_typ, ret_typ), Surface.Fun(name, ann, body) ->
        let param_typ =
            match ann with
            | Some ann ->
                let _, annC = check_typ g ctx ann in
                let annV = Eval.eval g ctx.venv annC in
                begin match g#subtyp ctx.level ctx.tenv param_typ annV with
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

    | TyPair(_, fst_typ, snd_typ), Surface.Pair(fst, snd) ->
        let fstC = check err_ctx g ctx fst_typ fst in
        let fstV = Eval.eval g ctx.venv fstC in
        let sndC = check err_ctx g ctx (snd_typ fstV) snd in
        Core.Pair(fstC, sndC)

    | typ, Surface.Hole ->
        let meta = g#fresh_meta (abstract_ctx g ctx typ) in
        apply_ctxC (Core.Meta("", meta)) ctx

    | _ ->
        let actual_typ, exprC = infer g ctx expr in
        begin match g#subtyp ctx.level ctx.tenv actual_typ typ with
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



let rec check_env g env =
    match env with
    | [] ->
        empty_ctx, []
    | (name, typ, kind) :: env' ->
        let elab_ctx, envC = check_env g env' in
        let _, typC = check_typ g elab_ctx typ in
        ( add_local name (Eval.eval g elab_ctx.venv typC) elab_ctx
        , (name, typC, kind) :: envC )



let check_top_level g (span, top) =
    match top with
    | Surface.AxiomDecl(name, typ) ->
        let _, typC = check_typ g empty_ctx typ in
        g#solve_all;
        g#check_metas;
        begin try g#add_global_decl name (Eval.eval g [] typC) with
        | Context.RedefineGlobal -> raise (Error.Error (span, RedeclareVar name))
        end;
        Core.AxiomDecl(name, typC)

    | Surface.Definition(name, typ, def) ->
        let typV, typC, defC =
            match typ with
            | Some typ ->
                let _, typC = check_typ g empty_ctx typ in
                let typV = Eval.eval g [] typC in
                (typV, typC, check "global definition" g empty_ctx typV def)
            | None ->
                let typV, defC = infer g empty_ctx def in
                let _, typC = Quote.typ_to_core g 0 [] typV in
                (typV, typC, defC)
        in
        g#solve_all;
        g#check_metas;
        g#add_global_def name typV (Eval.eval g [] defC);
        Core.Definition(name, typC, defC)



let rec check_program g = function
    | []          -> []
    | (span1, Surface.AxiomDecl(name1, typ))
        :: (span2, Surface.Definition(name2, None, def))
        :: tops when name1 = name2 ->
        let span = { lhs = span1.lhs; rhs = span2.rhs } in
        check_program g ((span, Surface.Definition(name1, Some typ, def)) :: tops)
    | top :: tops ->
        let c_top = check_top_level g top in
        c_top :: check_program g tops
