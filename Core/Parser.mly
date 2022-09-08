%{
open Syntax

let cur_span () =
    { lhs = Parsing.symbol_start_pos ()
    ; rhs = Parsing.symbol_end_pos () }

let mk_expr shape =
    { shape; span = cur_span () }

let join_span sp1 sp2 =
    { lhs = sp1.lhs
    ; rhs = sp2.rhs }


exception SyntaxError of span * string

let error msg = raise (SyntaxError(cur_span (), msg))
%}

%token TOK_EOF
%token TOK_LPAREN TOK_RPAREN TOK_LBRACK TOK_RBRACK TOK_LBRACE TOK_RBRACE
%token TOK_EQ
%token TOK_MINUS_GT TOK_EQ_GT
%token TOK_COMMA TOK_DOT
%token TOK_COLON TOK_COLON_GT

%token<string> TOK_NAME
%token<int> TOK_INT
%token TOK_KW_TYPE TOK_KW_FORALL TOK_KW_EXISTS
%token TOK_KW_FUN TOK_KW_LET



%right    TOK_MINUS_GT TOK_EQ_GT
%right    TOK_COMMA
%nonassoc TOK_EQ
%left     TOK_COLON TOK_COLON_GT
%left     APP


%type<Syntax.expr> expr
%start expr

%type<Syntax.top_level> top_level
%start top_level

%type<Syntax.top_level list> program
%start program

%%

program :
    | top_level TOK_EOF { [$1] }
    | top_level program { $1 :: $2 }
;


top_level :
    | TOK_KW_LET TOK_NAME TOK_COLON expr { AxiomDecl ($2, $4) }
    | TOK_KW_LET TOK_NAME TOK_EQ    expr { Definition($2, $4) }
    | error                              { error "expecting top level clause" }
;


expr :
    | binary_op_expr
        { $1 }

    | TOK_KW_FORALL param_list TOK_MINUS_GT expr
        { List.fold_right (fun param body -> mk_expr @@ E_TyFun(param, body)) $2 $4 }

    | binary_op_expr TOK_MINUS_GT expr
        { mk_expr @@ E_TyFun(("", $1), $3) }

    | TOK_KW_FUN param_list_opt_ann TOK_MINUS_GT expr
        { List.fold_right (fun param body -> mk_expr @@ E_Fun(param, body)) $2 $4 }

    | TOK_KW_EXISTS param_list TOK_MINUS_GT expr
        { List.fold_right (fun param body -> mk_expr @@ E_TyPair(param, body)) $2 $4 }

    | error
        { error "expecting expression" }
;

binary_op_expr:
    | app_expr
        { $1 }

    | binary_op_expr TOK_COLON binary_op_expr
        { mk_expr @@ E_Ann($1, $3) }

    | binary_op_expr TOK_COMMA binary_op_expr
        { mk_expr @@ E_Pair($1, $3) }

    | binary_op_expr TOK_EQ binary_op_expr
        { mk_expr @@ E_TyEq($1, $3) }

    | binary_op_expr TOK_COLON_GT binary_op_expr
        { mk_expr @@ E_Coe($1, $3) }

;

app_expr:
    | atom_expr
        { $1 }

    | app_expr atom_expr
        { mk_expr @@ E_App($1, $2) }
;

atom_expr :
    | TOK_NAME
        { mk_expr @@ E_Var $1 }

    | TOK_KW_TYPE TOK_INT
        { mk_expr @@ E_Type $2 }

    | TOK_LPAREN expr TOK_RPAREN
        { $2 }

    | atom_expr TOK_DOT TOK_INT
        { match $3 with
          | 1 -> mk_expr @@ E_Proj($1, `Fst)
          | 2 -> mk_expr @@ E_Proj($1, `Snd)
          | _ -> failwith "invalid field of pair" }
;


param_list :
    | param_decl
        { $1 }
    | param_decl param_list
        { $1 @ $2 }
;


param_list_opt_ann :
    | param_decl_opt_ann
        { $1 }
    | param_decl_opt_ann param_list_opt_ann
        { $1 @ $2 }
;


param_decl :
    | TOK_LPAREN name_list_nonempty TOK_COLON expr TOK_RPAREN
        { List.map (fun name -> (name, $4)) $2 }
;

param_decl_opt_ann :
    | TOK_LPAREN name_list_nonempty TOK_COLON expr TOK_RPAREN
        { List.map (fun name -> (name, Some $4)) $2 }
    | TOK_NAME
        { [$1, None] }
;

name_list_nonempty :
    | TOK_NAME                    { [$1] }
    | TOK_NAME name_list_nonempty { $1 :: $2 }
;
