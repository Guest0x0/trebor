
open Syntax
open Value


let rec elim_implicit g level env core typ =
    match typ with
    | TyFun(_, Implicit, a, b) ->
        let meta = g#fresh_meta (Unification.env_to_typ g level env a) in
        let arg = Stuck(a, Meta("", meta), Unification.env_to_elim level env) in
        elim_implicit g level env
            (Core.App(core, Quote.value_to_core g level a arg)) (b arg)
    | _ ->
        (typ, core)


let rec explicitfy = function
    | TyFun(name, Implicit, a, b) -> TyFun(name, Explicit, a, fun v -> explicitfy (b v))
    | typ                         -> typ
