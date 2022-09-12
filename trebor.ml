
open Kernel

let globals = Prelude.make_globals 37

let _ =
    let file = Sys.argv.(1) in
    let lexbuf = Lexing.from_channel (open_in file) in
    let program = Parser.program Lexer.token lexbuf in
    Elaborate.check_program globals program
