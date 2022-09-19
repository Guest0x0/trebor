
open Syntax

exception RedefineGlobal
exception UnsolvedMeta of meta

class context : object
    method find_global     : string -> Value.top_level
    method add_global_decl : string -> Value.value -> unit
    method add_global_def  : string -> Value.value -> Value.value -> unit

    method find_meta  : meta -> Value.meta_info
    method solve_meta : meta -> Value.value -> unit
    method fresh_meta : Value.value -> meta

    method check_metas : unit
    method dump_metas  : (meta * Value.meta_info) list
end
