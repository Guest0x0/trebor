
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
    let name =
        if name = "" || List.mem name ctx.names
        then "$" ^ string_of_int ctx.level
        else name
    in
    ( name, { ctx with names = name :: ctx.names; level = ctx.level + 1 })

let incr_prec  ctx = { ctx with prec  = ctx.prec  + 1 }


let rec pp_core ctx fmt core =
    match core with
    | Core.TopVar name ->
        fprintf fmt "%s" name

    | Core.Local idx ->
        fprintf fmt "%s" (List.nth ctx.names idx)

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

    | Core.TyFun(name, a, b) when ctx.prec <= prec_binder ->
        fprintf fmt "@[<hov2>forall %a@]"
            (pp_core_tyfun { ctx with prec = prec_binder }) (name, a, b)

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
            (match field with `Fst -> 1 | `Snd -> 2)

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

    | _ ->
        fprintf fmt "(%a)" (pp_core { ctx with prec = 0 }) core


and pp_core_tyfun ctx fmt (name, a, b) =
    let name, ctx' = add_var name ctx in
    fprintf fmt "(%s : %a)" name (pp_core @@ incr_prec ctx) a;
    match b with
    | Core.TyFun(name', a', b') -> fprintf fmt "@ %a" (pp_core_tyfun ctx') (name', a', b')
    | _                         -> fprintf fmt " ->@ %a" (pp_core ctx') b

and pp_core_typair ctx fmt (name, a, b) =
    let name, ctx' = add_var name ctx in
    fprintf fmt "(%s : %a)" name (pp_core @@ incr_prec ctx) a;
    match b with
    | Core.TyPair(name', a', b') -> fprintf fmt "@ %a" (pp_core_typair ctx') (name', a', b')
    | _                          -> fprintf fmt " ->@ %a" (pp_core ctx') b

and pp_core_fun ctx fmt (name, body) =
    let name, ctx' = add_var name ctx in
    fprintf fmt "%s" name; 
    match body with
    | Core.Fun(name', body') -> fprintf fmt "@ %a" (pp_core_fun ctx') (name', body')
    | _           -> fprintf fmt " ->@ %a" (pp_core ctx') body


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


let pp_context verbose fmt ctx =
    let rec loop = function
        | [] ->
            []
        | (name, typ) :: ctx' ->
            let names = loop ctx' in
            if names <> [] then
                fprintf fmt "@ ";
            fprintf fmt "%s : %a" name (pp_core ~verbose names) typ;
            name :: names
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
    | Syntax.SyntaxError msg -> fprintf fmt "syntax error: %s" msg
    | Syntax.UnboundVar name -> fprintf fmt "unbound variable %s" name
    | Syntax.CannotInfer msg -> fprintf fmt "cannot infer type of %s" msg
    | Syntax.WrongType(ctx, typ, expected) ->
        fprintf fmt "@[<v>expected: %s@ found: %a@ "
            expected (pp_core ~verbose @@ List.map fst ctx) typ;
        fprintf fmt "@[<v2>in context:@ %a@]@]" (pp_context verbose) ctx
    | Syntax.TypeMismatch(ctx, expected, actual, err_ctx) ->
        let names = List.map fst ctx in
        fprintf fmt "@[<v>type mismatch at %s:@ " err_ctx;
        fprintf fmt "expected: %a@ " (pp_core ~verbose names) expected;
        fprintf fmt "received: %a@ " (pp_core ~verbose names) actual;
        fprintf fmt "@[<v2>in context:@ %a@]@]" (pp_context verbose) ctx
    | Syntax.RedeclareVar name -> fprintf fmt "re-declaring %s" name
    | Syntax.RedefineVar  name -> fprintf fmt "re-defining %s" name


let pp_exception verbose fmt exn =
    match exn with
    | Syntax.Error(span, err) ->
        fprintf fmt "@[<v>at %a:@ %a@]" pp_span span (pp_error verbose) err
    | exn ->
        fprintf fmt "fatal exception %s" (Printexc.to_string exn)
