
open Syntax
open Value


let rec gen_implicit_args g level env typ =
    match Eval.force g typ with
    | TyFun(_, Implicit, a, b) ->
        let meta = g#fresh_meta (Unification.env_to_tyfun g env a) in
        let arg = Stuck(Meta meta, Unification.env_to_elim level env) in
        let typ', args = gen_implicit_args g level env (b arg) in
        typ', arg :: args
    | typ ->
        (typ, [])


let fill_implicit_args g level env funcC typ =
    let typ', args = gen_implicit_args g level env typ in
    ( typ'
    , List.fold_left
            (fun func arg -> Core.App(func, Quote.value_to_core g level arg))
            funcC args )


let rec explicitfy g value =
    match Eval.force g value with
    | TyFun(name, Implicit, a, b) -> TyFun(name, Explicit, a, fun v -> explicitfy g (b v))
    | typ                         -> typ
