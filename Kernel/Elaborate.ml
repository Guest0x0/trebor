
open Syntax
open Eval

type context =
    { level : int
    ; shift : int
    ; venv  : Value.value list
    ; tenv  : Value.env }


let empty_ctx =
    { level = 0
    ; shift = 0
    ; venv  = []
    ; tenv  = [] }


let add_local name typ ?value ctx =
    let value, kind =
        match value with
        | Some value -> value, `Defined
        | None       -> Value.stuck_local ctx.level typ, `Bound
    in
    { level = ctx.level + 1
    ; shift = ctx.shift
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
    let _, typC = Quote.typ_to_core g ctx.level typ in
    raise @@ Error.Error(span, WrongType(ctxC, typC, expected))

let type_mismatch g ctx span expected actual err_ctx =
    let ctxC = Quote.env_to_core g ctx.tenv in
    let _, expectedC = Quote.typ_to_core g ctx.level expected in
    let _, actualC   = Quote.typ_to_core g ctx.level actual in
    raise @@ Error.Error(span, TypeMismatch(ctxC, expectedC, actualC, err_ctx))



let rec infer g ctx expr =
    match expr.Surface.shape with
    | Surface.Var(s, name) ->
        begin match find_local name ctx with
        | idx, typ ->
            if s <> 0 then
                raise @@ Error.Error(expr.span, Error.CanOnlyShiftGlobal);
            ( typ, Core.Local idx )
        | exception Not_found ->
            match g#find_global name with
            | Value.(AxiomDecl typ | Definition(typ, _)) ->
                ( typ s, 
                    if s = 0
                    then Core.TopVar name
                    else Core.Shift(s, Core.TopVar name) )
            | exception Not_found ->
                raise @@ Error.Error(expr.span, UnboundVar name)
        end

    | Surface.Let((name, ann, rhs), body) ->
        let rhs_typ, c_rhs =
            match ann with
            | Some ann ->
                let _, c_ann = check_typ g ctx ann in
                let rhs_typ = Eval.eval g 0 ctx.venv c_ann in
                (rhs_typ, check "type annotation" g ctx rhs_typ rhs)
            | None ->
                infer g ctx rhs
        in
        let ctx' = add_local name rhs_typ ~value:(Eval.eval g 0 ctx.venv c_rhs) ctx in
        let res_typ, c_body = infer g ctx' body in
        ( res_typ
        , Core.Let(name, c_rhs, c_body ) )


    | Surface.Ann(expr, typ) ->
        let _, ctyp = check_typ g ctx typ in
        let typV = Eval.eval g 0 ctx.venv ctyp in
        let exprC = check "type annotation" g ctx typV expr in
        ( typV, exprC )

    | Surface.Type ulevel ->
        ( Type(ulevel + 1), Core.Type ulevel )

    | Surface.TyFun(name, kind, a, b) ->
        let ul_a, ca = check_typ g ctx a in
        let va = Eval.eval g 0 ctx.venv ca in
        let ul_b, cb = check_typ g (add_local name va ctx) b in
        ( Value.Type(max ul_a ul_b)
        , Core.TyFun(name, kind, ca, cb) )

    | Surface.Fun(_, _, None, _) ->
        raise @@ Error.Error(expr.span, CannotInfer "function without parameter annotation")

    | Surface.Fun(name, kind, Some param_typ, body) ->
        let _, param_typC = check_typ g ctx param_typ in
        let param_typV = Eval.eval g 0 ctx.venv param_typC in
        let ret_typV, bodyC = infer g (add_local name param_typV ctx) body in
        let _, ret_typC = Quote.typ_to_core g (ctx.level + 1) ret_typV in
        ( Value.TyFun(name, kind, param_typV, fun v -> Eval.eval g 0 (v :: ctx.venv) ret_typC)
        , Core.Fun(name, bodyC) )

    | Surface.App(func, arg) ->
        let func_typ0, funcC = infer g ctx func in
        let func_typ, funcC = Implicit.elim_implicit g ctx.level ctx.tenv funcC func_typ0 in
        let (a, b) =
            try g#refine_to_function ctx.level ctx.tenv func_typ with
              Unification.UnificationFailure ->
                wrong_type g ctx expr.span func_typ0 "function"
        in
        let argC = check "function application" g ctx a arg in
        ( b (Eval.eval g 0 ctx.venv argC), Core.App(funcC, argC) )

    | Surface.TyPair(name, fst_typ, snd_typ) ->
        let ul_fst, fst_typC = check_typ g ctx fst_typ in
        let fst_typV  = Eval.eval g 0 ctx.venv fst_typC in
        let ul_snd, snd_typC = check_typ g (add_local name fst_typV ctx) snd_typ in
        ( Type(max ul_fst ul_snd)
        , Core.TyPair(name, fst_typC, snd_typC) )

    | Surface.Pair(fst, snd) ->
        let fst_typ, fstC = infer g ctx fst in
        let snd_typ, sndC = infer g ctx snd in
        ( Value.TyPair("", fst_typ, Fun.const snd_typ)
        , Core.Pair(fstC, sndC) )

    | Surface.Proj(pair, field) ->
        let pair_typ0, pairC = infer g ctx pair in
        let pair_typ, pairC = Implicit.elim_implicit g ctx.level ctx.tenv pairC pair_typ0 in
        let (fst_typ, snd_typ) =
            try g#refine_to_pair ctx.level ctx.tenv pair_typ with
              Unification.UnificationFailure ->
                wrong_type g ctx expr.span pair_typ0 "pair"
        in
        begin match field with
        | `Fst ->
            ( fst_typ, Core.Proj(pairC, field) )
        | `Snd ->
            let fstV = Eval.project (Eval.eval g 0 ctx.venv pairC) `Fst in
            ( snd_typ fstV, Core.Proj(pairC, field) )
        end

    | Surface.TyEq(lhs, rhs) ->
        let lhs_typ, lhsC = infer g ctx lhs in
        let rhs_typ, rhsC = infer g ctx rhs in
        let ul_lhs, lhs_typC = Quote.typ_to_core g ctx.level lhs_typ in
        let ul_rhs, rhs_typC = Quote.typ_to_core g ctx.level rhs_typ in
        ( Type(max ul_lhs ul_rhs)
        , Core.TyEq((lhsC, lhs_typC), (rhsC, rhs_typC)) )

    | Surface.Coe(coerced, eq) ->
        let eq_typ0, eqC = infer g ctx eq in
        let eq_typ , eqC = Implicit.elim_implicit g ctx.level ctx.tenv eqC eq_typ0 in
        begin match eq_typ with
        | TyEq((lhs, lhs_typ), (rhs, rhs_typ)) ->
            begin match Eval.force g lhs_typ, Eval.force g rhs_typ with
            | Type ul_lhs, Type ul_rhs ->
                let coercedC = check "coerced value" g ctx lhs coerced in
                let _, lhsC = Quote.typ_to_core g ctx.level lhs in
                let _, rhsC = Quote.typ_to_core g ctx.level rhs in
                ( rhs
                , Core.Coe { ulevel  = max ul_lhs ul_rhs
                           ; coerced = coercedC
                           ; lhs     = lhsC
                           ; rhs     = rhsC
                           ; eq      = Lazy.from_val eqC } )
            | _ ->
                wrong_type g ctx expr.span eq_typ0 "equality between types"
            end
        | _ ->
            wrong_type g ctx expr.span eq_typ0 "equality"
        end

    | Surface.Hole ->
        let typ_meta = g#fresh_meta (Unification.env_to_typ g ctx.level ctx.tenv (Value.Type 0)) in
        let elim = Unification.env_to_elim ctx.level ctx.tenv in
        let typ = Value.Stuck(Type 0, Value.Meta("", typ_meta), elim) in
        let hole_meta = g#fresh_meta (Unification.env_to_typ g ctx.level ctx.tenv typ) in
        (typ, Quote.neutral_to_core g ctx.level (Value.Meta("", hole_meta)) elim)

    | Surface.Explicitfy expr' ->
        let typ, exprC = infer g ctx expr' in
        Implicit.explicitfy g typ, exprC

    | Surface.ElimImplicit expr' ->
        let typ, exprC = infer g ctx expr' in
        Implicit.elim_implicit g ctx.level ctx.tenv exprC typ


and check err_ctx g ctx typ expr =
    match typ, expr.shape with
    | _, Surface.Let((name, ann, rhs), body) ->
        let rhs_typ, rhsC =
            match ann with
            | Some ann ->
                let _, annC = check_typ g ctx ann in
                let rhs_typ = Eval.eval g 0 ctx.venv annC in
                (rhs_typ, check "type annotation" g ctx rhs_typ rhs)
            | None ->
                infer g ctx rhs
        in
        let ctx' = add_local name rhs_typ ~value:(Eval.eval g 0 ctx.venv rhsC) ctx in
        let bodyC = check err_ctx g ctx' typ body in
        Core.Let(name, rhsC, bodyC)

    | TyFun(_, kind1, param_typ, ret_typ), Surface.Fun(name, kind2, ann, body)
        when kind1 = kind2 ->
        let param_typ =
            match ann with
            | Some ann -> check_annotation "function annotation" g ctx param_typ ann
            | None     -> param_typ
        in
        let ret_typ = ret_typ @@ Value.stuck_local ctx.level param_typ in
        let bodyC = check err_ctx g (add_local name param_typ ctx) ret_typ body in
        Core.Fun(name, bodyC)

    | TyFun(name, Implicit, param_typ, ret_typ), _ ->
        let var = Value.stuck_local ctx.level param_typ in
        let exprC = check err_ctx g (add_local name param_typ ctx) (ret_typ var) expr in
        Core.Fun(name, exprC)

    | TyPair(_, fst_typ, snd_typ), Surface.Pair(fst, snd) ->
        let fstC = check err_ctx g ctx fst_typ fst in
        let fstV = Eval.eval g 0 ctx.venv fstC in
        let sndC = check err_ctx g ctx (snd_typ fstV) snd in
        Core.Pair(fstC, sndC)

    | typ, Surface.Hole ->
        let meta = g#fresh_meta (Unification.env_to_typ g ctx.level ctx.tenv typ) in
        Quote.neutral_to_core g ctx.level (Value.Meta("", meta))
            (Unification.env_to_elim ctx.level ctx.tenv)

    | _ ->
        let actual_typ, exprC = infer g ctx expr in
        let actual_typ, exprC =
            match typ with
            | Stuck(_, Meta _, _) -> actual_typ, exprC
            | _                   -> Implicit.elim_implicit g ctx.level ctx.tenv exprC actual_typ
        in
        begin match g#subtyp ctx.level actual_typ typ with
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


and check_annotation err_ctx g ctx typV ann =
    let _, annC = check_typ g ctx ann in
    let annV = Eval.eval g 0 ctx.venv annC in
    begin match g#subtyp ctx.level typV annV with
    | () ->
        annV
    | exception Unification.UnificationFailure ->
        type_mismatch g ctx ann.span typV annV err_ctx
    end



let rec check_env g env =
    match env with
    | [] ->
        empty_ctx, []
    | (name, typ, kind) :: env' ->
        let elab_ctx, envC = check_env g env' in
        let _, typC = check_typ g elab_ctx typ in
        ( add_local name (Eval.eval g 0 elab_ctx.venv typC) elab_ctx
        , (name, typC, kind) :: envC )



let flush_meta span g =
    try g#solve_all; g#check_metas
    with Unification.CannotSolveYet | Context.UnsolvedMeta _ ->
        let metas = g#dump_metas |> List.map @@ fun (meta, info) ->
            (meta, Quote.meta_info_to_core g info)
        in
        raise @@ Error.Error(span, Error.UnsolvedMeta metas)


let check_top_level g (span, top) =
    match top with
    | Surface.AxiomDecl(name, typ) ->
        let _, typC = check_typ g empty_ctx typ in
        flush_meta span g;
        begin try g#add_global_decl name (Eval.eval_poly g [] typC) with
        | Context.RedefineGlobal -> raise (Error.Error (span, RedeclareVar name))
        end;
        Core.AxiomDecl(name, typC)

    | Surface.Definition(name, typ, def) ->
        let typC, defC =
            match typ with
            | Some typ ->
                let _, typC = check_typ g empty_ctx typ in
                let typV = Eval.eval g 0 [] typC in
                (typC, check "global definition" g empty_ctx typV def)
            | None ->
                let typV, defC = infer g empty_ctx def in
                let _, typC = Quote.typ_to_core g 0 typV in
                (typC, defC)
        in
        flush_meta span g;
        g#add_global_def name (Eval.eval_poly g [] typC) (Eval.eval_poly g [] defC);
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
