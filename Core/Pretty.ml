
open Syntax
open Format


let prec_binder = 10
let prec_comma  = 20
let prec_eq     = 30
let prec_coe    = 40
let prec_app    = 50
let prec_atom   = 60


type pp_context =
    { names   : string list
    ; level   : int
    ; prec    : int 
    ; verbose : bool }

let add_var name ctx =
    let name =
        if List.mem name ctx.names
        then "$" ^ string_of_int ctx.level
        else name
    in
    ( name, { ctx with names = name :: ctx.names; level = ctx.level + 1 })

let incr_prec  ctx = { ctx with prec  = ctx.prec  + 1 }


let rec pp_core ctx fmt core =
    match core with
    | C_TopVar name ->
        fprintf fmt "%s" name

    | C_Local idx ->
        fprintf fmt "%s" (List.nth ctx.names idx)

    | C_Type ulevel ->
        fprintf fmt "Type %d" ulevel

    | C_TyFun(a, b) when ctx.prec <= prec_binder ->
        fprintf fmt "@[<hov2>forall %a@]"
            (pp_core_tyfun { ctx with prec = prec_binder }) (a, b)

    | C_Fun(name, body) when ctx.prec <= prec_binder ->
        fprintf fmt "@[<hov2>fun %a@]"
            (pp_core_fun { ctx with prec = prec_binder }) (name, body)

    | C_App(f, a) when ctx.prec <= prec_app ->
        fprintf fmt "@[<hov2>%a@]" (pp_core_app ctx) (f, a)

    | C_TyPair(a, b) when ctx.prec <= prec_binder ->
        fprintf fmt "@[<hov2>exists %a@]"
            (pp_core_typair { ctx with prec = prec_binder }) (a, b)

    | C_Pair(fst, snd) when ctx.prec <= prec_comma ->
        fprintf fmt "@[<hov2>%a@]"
            (pp_core_pair { ctx with prec = prec_comma }) (fst, snd)

    | C_Proj(pair, field) ->
        fprintf fmt "%a.%d"
            (pp_core { ctx with prec = prec_atom }) pair
            (match field with `Fst -> 1 | `Snd -> 2)

    | C_TyEq((lhs, lhs_typ), (rhs, rhs_typ)) when ctx.prec <= prec_eq ->
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

    | C_Coe { target; eq; _ } when ctx.prec <= prec_coe ->
        fprintf fmt "@[<hov2>%a :>@ " (pp_core { ctx with prec = prec_coe }) target;
        if ctx.verbose
        then fprintf fmt "%a@]" (pp_core { ctx with prec = prec_coe + 1 }) (Lazy.force eq)
        else fprintf fmt "_@]"

    | _ ->
        fprintf fmt "(%a)" (pp_core { ctx with prec = 0 }) core


and pp_core_tyfun ctx fmt ((name, a), b) =
    let name, ctx' = add_var name ctx in
    fprintf fmt "(%s : %a)" name (pp_core @@ incr_prec ctx) a;
    match b with
    | C_TyFun(a', b') -> fprintf fmt "@ %a" (pp_core_tyfun ctx') (a', b')
    | _               -> fprintf fmt "->@ %a" (pp_core ctx') b

and pp_core_typair ctx fmt ((name, a), b) =
    let name, ctx' = add_var name ctx in
    fprintf fmt "(%s : %a)" name (pp_core @@ incr_prec ctx) a;
    match b with
    | C_TyPair(a', b') -> fprintf fmt "@ %a" (pp_core_tyfun ctx') (a', b')
    | _                -> fprintf fmt "->@ %a" (pp_core ctx') b

and pp_core_fun ctx fmt (name, body) =
    let name, ctx' = add_var name ctx in
    fprintf fmt "%s" name; 
    match body with
    | C_Fun(name', body') -> fprintf fmt "@ %a" (pp_core_fun ctx') (name', body')
    | _           -> fprintf fmt "->@ %a" (pp_core ctx') body


and pp_core_pair ctx fmt (fst, snd) =
    fprintf fmt "%a,@ " (pp_core @@ incr_prec ctx) fst;
    match snd with
    | C_Pair(fst', snd') -> pp_core_pair ctx fmt (fst', snd')
    | _                  -> pp_core ctx fmt snd


and  pp_core_app ctx fmt (f, a) =
    begin match f with
    | C_App(f', a') -> pp_core_app ctx fmt (f', a')
    | _             -> pp_core ctx fmt f
    end;
    fprintf fmt "@ %a" (pp_core @@ incr_prec ctx) a



let pp_core ?(verbose=false) names =
    pp_core { names; level = List.length names; prec = 0; verbose }


let pp_core_top_level verbose fmt top =
    match top with
    | C_AxiomDecl(name, typ) ->
        fprintf fmt "let %s : %a" name (pp_core ~verbose []) typ
    | C_Definition(name, def, typ) ->
        fprintf fmt "@[<v>let %s : %a@ let %s = %a@]"
            name (pp_core ~verbose []) typ
            name (pp_core ~verbose []) def


let pp_span fmt span =
    fprintf fmt "[%d:%d to %d:%d, %s]"
        span.lhs.pos_lnum (span.lhs.pos_cnum - span.lhs.pos_bol)
        span.rhs.pos_lnum (span.rhs.pos_cnum - span.rhs.pos_bol)
        span.lhs.pos_fname


let pp_error fmt err =
    match err with
    | UnboundVar name -> fprintf fmt "unbound variable %s" name
    | CannotInfer msg -> fprintf fmt "cannot infer type of %s" msg
    | WrongType(ctx, typ, expected) ->
        fprintf fmt "@[<v>expected: %s@ found: %a@]"
            expected (pp_core @@ List.map fst ctx) typ
    | TypeMismatch(ctx, expected, actual, err_ctx) ->
        let names = List.map fst ctx in
        fprintf fmt "@[<v>type mismatch at %s:@ " err_ctx;
        fprintf fmt "expected: %a@ " (pp_core names) expected;
        fprintf fmt "received: %a@]" (pp_core names) actual


let pp_exception fmt exn =
    match exn with
    | TypeError(span, err) ->
        fprintf fmt "@[<v>at %a:@ %a@]" pp_span span pp_error err
    | exn ->
        fprintf fmt "fatal exception %s" (Printexc.to_string exn)
