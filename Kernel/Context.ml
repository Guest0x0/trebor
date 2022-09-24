
open Syntax



exception RedefineGlobal
exception UnsolvedMeta of meta



let garbage = Value.Free(Value.Type 0)

class context = object(self)
    val globals : (string, Value.top_level) Hashtbl.t = Hashtbl.create 42
    val mutable meta_count   = 0
    val mutable solved_count = 0
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
        match self#find_meta meta with
        | Value.Free typ ->
            solved_count <- solved_count + 1;
            metas.(meta) <- Solved(typ, value)
        | Value.Solved _ -> failwith "Context.context#solve_meta"

    method solved_count = solved_count


    method fresh_meta typ =
        if meta_count = Array.length metas then
            metas <- Array.init (2 * meta_count)
                    (fun i -> if i < meta_count then metas.(i) else garbage);
        let meta = meta_count in
        metas.(meta) <- Free typ;
        meta_count <- meta_count + 1;
        meta


    method check_metas =
        metas |> Array.iteri begin fun meta info ->
            if meta < meta_count then
                match info with
                | Value.Free _   -> raise (UnsolvedMeta meta)
                | Value.Solved _ -> ()
        end

    method dump_metas =
        Array.to_seqi metas
        |> Seq.filter (fun (meta, info) -> meta < meta_count)
        |> List.of_seq
end
