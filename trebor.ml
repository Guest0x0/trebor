
open Core

let global = Hashtbl.create 37
let _ = Hashtbl.add_seq global
        (List.to_seq Typecheck.prelude
         |> Seq.map (fun (name, typ) -> name, Normalization.V_Axiom typ))

let _ =
    let file = Sys.argv.(1) in
    let lexbuf = Lexing.from_channel (open_in file) in
    let program = Parser.program Lexer.token lexbuf in
    Typecheck.process_program global program
