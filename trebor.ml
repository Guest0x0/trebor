
open Kernel

let g = new Context.context

let _ =
    let file = Sys.argv.(1) in
    let lexbuf = Lexing.from_channel (open_in file) in
    let program = Parser.program Lexer.token lexbuf in
    Elaborate.check_program g program
