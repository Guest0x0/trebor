{
open Parser

let keyword_table = Hashtbl.of_seq @@ List.to_seq
    [ "Type"  , TOK_KW_TYPE
    ; "forall", TOK_KW_FORALL
    ; "exists", TOK_KW_EXISTS
    ; "fun"   , TOK_KW_FUN
    ; "let"   , TOK_KW_LET
    ; "in"    , TOK_KW_IN ]
}

let dex_digit = ['0'-'9']
let lowercase = ['a'-'z']
let uppercase = ['A'-'Z']
let other_name_char = ['_' '-' '\'' '*' '+']
let name_head = other_name_char | lowercase | uppercase
let name_char = name_head | dex_digit

let blank   = [' ' '\t']
let newline = ['\n']


rule token = parse
    | eof     { TOK_EOF }
    | blank+  { token lexbuf }
    | newline { Lexing.new_line lexbuf; token lexbuf }
    | '('     { TOK_LPAREN }
    | ')'     { TOK_RPAREN }
    | '['     { TOK_LBRACK }
    | ']'     { TOK_RBRACK }
    | '{'     { TOK_LBRACE }
    | '}'     { TOK_RBRACE }
    | '~'     { TOK_TILDE }
    | "->"    { TOK_MINUS_GT }
    | "=>"    { TOK_EQ_GT }
    | ','     { TOK_COMMA }
    | '.'     { TOK_DOT }
    | ':'     { TOK_COLON }
    | '='     { TOK_EQ }
    | ":>"    { TOK_COLON_GT }
    | dex_digit+
        { TOK_INT(int_of_string (Lexing.lexeme lexbuf)) }
    | (name_head)(name_char*)
        { let name = Lexing.lexeme lexbuf in
          try Hashtbl.find keyword_table name with Not_found -> TOK_NAME name }
