
open Core

let globals = Prelude.make_globals 37

let _ =
    let file = Sys.argv.(1) in
    let lexbuf = Lexing.from_channel (open_in file) in
    let program = Parser.program Lexer.token lexbuf in
    Typecheck.process_program globals program
