
open Syntax
open Format


let prec_binder = 10
let prec_comma  = 20
let prec_eq     = 30
let prec_coe    = 40
let prec_app    = 50
let prec_shift  = 60
let prec_proj   = 70


type pp_context =
    { names   : string list
    ; level   : int
    ; prec    : int 
    ; verbose : bool }


let add_var name ctx =
    let name = if List.mem name ctx.names then "" else name in
    ( name, { ctx with names = name :: ctx.names; level = ctx.level + 1 })

let pp_name fmt (name, lvl) =
    if name = ""
    then fprintf fmt "$%d" lvl
    else fprintf fmt "%s" name


let incr_prec  ctx = { ctx with prec  = ctx.prec  + 1 }


let rec pp_core ctx fmt core =
    match core with
    | Core.TopVar name ->
        fprintf fmt "%s" name

    | Core.Local idx ->
        pp_name fmt (List.nth ctx.names idx, ctx.level - idx - 1)

    | Core.Let(name, rhs, body) when ctx.prec <= prec_binder ->
        let name, ctx' = add_var name ctx in
        fprintf fmt "@[<hv>@[<hv2>let %s =@ %a@]@ in@ %a@]"
            name (pp_core { ctx with prec = prec_binder }) rhs
            (pp_core { ctx' with prec = prec_binder }) body

    | Core.Type ulevel ->
        fprintf fmt "Type %d" ulevel

    | Core.Shift(shift, core') when ctx.prec <= prec_shift ->
        begin match shift with
        | 0 -> pp_core ctx fmt core'
        | 1 -> fprintf fmt "@[<hov2>~@ %a@]" (pp_core { ctx with prec = prec_shift }) core'
        | _ ->
            fprintf fmt "@[<hov2>~%d@ %a@]" shift (pp_core { ctx with prec = prec_shift }) core'
        end

    | Core.TyFun(name, kind, a, b) when ctx.prec <= prec_binder ->
        fprintf fmt "@[<hov2>forall %a@]"
            (pp_core_tyfun { ctx with prec = prec_binder }) (name, kind, a, b)

    | Core.Fun(name, body) when ctx.prec <= prec_binder ->
        fprintf fmt "@[<hov2>fun %a@]"
            (pp_core_fun { ctx with prec = prec_binder }) (name, body)

    | Core.App(f, a) when ctx.prec <= prec_app ->
        fprintf fmt "@[<hov2>%a@]" (pp_core_app { ctx with prec = prec_app }) (f, a)

    | Core.TyPair(name, a, b) when ctx.prec <= prec_binder ->
        fprintf fmt "@[<hov2>exists %a@]"
            (pp_core_typair { ctx with prec = prec_binder }) (name, a, b)

    | Core.Pair(fst, snd) when ctx.prec <= prec_comma ->
        fprintf fmt "@[<hov2>%a@]"
            (pp_core_pair { ctx with prec = prec_comma }) (fst, snd)

    | Core.Proj(pair, field) ->
        fprintf fmt "%a.%d"
            (pp_core { ctx with prec = prec_proj }) pair
            (match field with Fst -> 1 | Snd -> 2)

    | Core.TyEq((lhs, lhs_typ), (rhs, rhs_typ)) when ctx.prec <= prec_eq ->
        begin match ctx.verbose with
        | true ->
            fprintf fmt "@[<hov2>%a : %a =@ %a : %a@]"
                (pp_core { ctx with prec = prec_coe }) lhs
                (pp_core { ctx with prec = prec_coe + 1 }) lhs_typ
                (pp_core { ctx with prec = prec_coe }) rhs
                (pp_core { ctx with prec = prec_coe + 1 }) rhs_typ
        | false ->
            fprintf fmt "@[<hov2>%a =@ %a@]"
                (pp_core { ctx with prec = prec_eq + 1}) lhs
                (pp_core { ctx with prec = prec_eq + 1}) rhs
        end

    | Core.Coe { coerced; eq; _ } when ctx.prec <= prec_coe ->
        fprintf fmt "@[<hov2>%a :>@ " (pp_core { ctx with prec = prec_coe }) coerced;
        if ctx.verbose
        then fprintf fmt "%a@]" (pp_core { ctx with prec = prec_coe + 1 }) (Lazy.force eq)
        else fprintf fmt "_@]"

    | Core.Meta meta ->
        fprintf fmt "?%d" meta

    | _ ->
        fprintf fmt "(%a)" (pp_core { ctx with prec = 0 }) core


and pp_core_tyfun ctx fmt (name, kind, a, b) =
    let name, ctx' = add_var name ctx in
    begin match kind with
    | Explicit ->
        fprintf fmt "(%a : %a)"
            pp_name (name, ctx.level)
            (pp_core @@ incr_prec ctx) a;
    | Implicit ->
        fprintf fmt "{%a : %a}"
            pp_name (name, ctx.level)
            (pp_core @@ incr_prec ctx) a;
    end;
    match b with
    | Core.TyFun(name', kind', a', b') -> fprintf fmt "@ %a" (pp_core_tyfun ctx') (name', kind', a', b')
    | _                                -> fprintf fmt " ->@ %a" (pp_core ctx') b

and pp_core_typair ctx fmt (name, a, b) =
    let name, ctx' = add_var name ctx in
    fprintf fmt "(%a : %a)" pp_name (name, ctx.level) (pp_core @@ incr_prec ctx) a;
    match b with
    | Core.TyPair(name', a', b') -> fprintf fmt "@ %a" (pp_core_typair ctx') (name', a', b')
    | _                          -> fprintf fmt " ->@ %a" (pp_core ctx') b

and pp_core_fun ctx fmt (name, body) =
    let name, ctx' = add_var name ctx in
    fprintf fmt "%a" pp_name (name, ctx.level);
    match body with
    | Core.Fun(name', body') -> fprintf fmt "@ %a" (pp_core_fun ctx') (name', body')
    | _                      -> fprintf fmt " ->@ %a" (pp_core ctx') body


and pp_core_pair ctx fmt (fst, snd) =
    fprintf fmt "%a,@ " (pp_core @@ incr_prec ctx) fst;
    match snd with
    | Core.Pair(fst', snd') -> pp_core_pair ctx fmt (fst', snd')
    | _                  -> pp_core ctx fmt snd


and  pp_core_app ctx fmt (f, a) =
    begin match f with
    | Core.App(f', a') -> pp_core_app ctx fmt (f', a')
    | _             -> pp_core ctx fmt f
    end;
    fprintf fmt "@ %a" (pp_core @@ incr_prec ctx) a



let pp_core ?(verbose=false) names =
    pp_core { names; level = List.length names; prec = 0; verbose }


let pp_core_top_level verbose fmt top =
    match top with
    | Core.AxiomDecl(name, typ) ->
        fprintf fmt "let %s : %a" name (pp_core ~verbose []) typ
    | Core.Definition(name, def, typ) ->
        fprintf fmt "@[<v>let %s : %a@ let %s = %a@]"
            name (pp_core ~verbose []) typ
            name (pp_core ~verbose []) def


let pp_env verbose fmt ctx =
    let rec loop = function
        | [] ->
            0, []
        | (_, name, typ) :: ctx' ->
            let level, names = loop ctx' in
            if level <> 0 then
                fprintf fmt "@ ";
            begin match name with
            | "" -> fprintf fmt "$%d : %a" level (pp_core ~verbose names) typ
            | _  -> fprintf fmt "%s : %a" name (pp_core ~verbose names) typ
            end;
            (level + 1, name :: names)
    in
    ignore (loop ctx)


let pp_span fmt span =
    let open Syntax in
    fprintf fmt "[%d:%d to %d:%d, %s]"
        span.lhs.pos_lnum (span.lhs.pos_cnum - span.lhs.pos_bol)
        span.rhs.pos_lnum (span.rhs.pos_cnum - span.rhs.pos_bol)
        span.lhs.pos_fname


let pp_error verbose fmt err =
    match err with
    | Error.SyntaxError msg -> fprintf fmt "syntax error: %s" msg
    | Error.UnboundVar name -> fprintf fmt "unbound variable %s" name
    | Error.CannotInfer msg -> fprintf fmt "cannot infer type of %s" msg
    | Error.WrongType(env, typ, expected) ->
        fprintf fmt "@[<v>expected: %s@ found: %a@ "
            expected (pp_core ~verbose @@ List.map (fun (_, name, _) -> name) env) typ;
        fprintf fmt "@[<v2>in context:@ %a@]@]" (pp_env verbose) env
    | Error.TypeMismatch(env, expected, actual, err_ctx) ->
        let names = List.map (fun (_, name, _) -> name) env in
        fprintf fmt "@[<v>type mismatch at %s:@ " err_ctx;
        fprintf fmt "expected: %a@ " (pp_core ~verbose names) expected;
        fprintf fmt "received: %a@ " (pp_core ~verbose names) actual;
        fprintf fmt "@[<v2>in context:@ %a@]@]" (pp_env verbose) env
    | Error.RedeclareVar name  -> fprintf fmt "re-declaring %s" name
    | Error.RedefineVar  name  -> fprintf fmt "re-defining %s" name
    | Error.CanOnlyShiftGlobal -> fprintf fmt "only global definitions can be shifted"
    | Error.UnsolvedMeta(metas, eqs) ->
        let pp_entry fmt (meta, info) =
            match info with
            | Core.Free typ ->
                fprintf fmt "?%d : %a" meta (pp_core ~verbose []) typ
            | Core.Solved(_, value) ->
                fprintf fmt "?%d := %a" meta (pp_core ~verbose []) value
        in
        let pp_equation fmt (level, lhs, rhs) =
            let names = List.init level (fun idx -> "$" ^ string_of_int (level - idx - 1)) in
            fprintf fmt "@[<hov2>%a@ = %a@]"
                (pp_core ~verbose names) lhs
                (pp_core ~verbose names) rhs
        in
        fprintf fmt "@[<v>@[<v2>unsolved meta:@ %a@]@ "
            (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@ ") pp_entry) metas;
        fprintf fmt "@[<v2>unsolved equations:@ %a@]@]"
            (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@ ") pp_equation) eqs


let pp_exception verbose fmt exn =
    match exn with
    | Error.Error(span, err) ->
        fprintf fmt "@[<v>at %a:@ %a@]" pp_span span (pp_error verbose) err
    | exn ->
        fprintf fmt "fatal exception %s" (Printexc.to_string exn)
