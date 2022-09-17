
open Syntax




let garbage = Value.Solved(Value.Type 0)

exception RedefineGlobal

class context = object(self)
    val globals : (string, Value.top_level) Hashtbl.t = Hashtbl.create 42
    val mutable meta_count = 0
    val mutable metas = Array.make 10 garbage


    method find_global name =
        Hashtbl.find globals name

    method add_global_decl name typ =
        if Hashtbl.mem globals name then
            raise RedefineGlobal;
        Hashtbl.add globals name (Value.AxiomDecl typ)

    method add_global_def name typ value =
        if Hashtbl.mem globals name then
            raise RedefineGlobal;
        Hashtbl.add globals name (Value.Definition(typ, value))



    method find_meta meta =
        if meta >= meta_count then
            raise Not_found;
        metas.(meta)

    method solve_meta meta value =
        if meta >= meta_count then
            raise Not_found;
        metas.(meta) <- Solved value


    method fresh_meta name typ =
        if meta_count = Array.length metas then
            metas <- Array.init (2 * meta_count)
                    (fun i -> if i < meta_count then metas.(i) else garbage);
        let meta = meta_count in
        metas.(meta) <- Free(name, typ);
        meta_count <- meta_count + 1;
        meta
end
