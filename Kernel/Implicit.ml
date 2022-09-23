
open Syntax
open Value


let rec elim_implicit g level env core typ =
    match Eval.force g typ with
    | TyFun(_, Implicit, a, b) ->
        let meta = g#fresh_meta (Unification.env_to_typ g level env a) in
        let arg = Stuck(a, Meta("", meta), Unification.env_to_elim level env) in
        elim_implicit g level env
            (Core.App(core, Quote.value_to_core g level a arg)) (b arg)
    | typ ->
        (typ, core)


let rec explicitfy g value =
    match Eval.force g value with
    | TyFun(name, Implicit, a, b) -> TyFun(name, Explicit, a, fun v -> explicitfy g (b v))
    | typ                         -> typ
