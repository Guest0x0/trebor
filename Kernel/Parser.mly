%{
open Syntax
open Surface

let cur_span () =
    { lhs = Parsing.symbol_start_pos ()
    ; rhs = Parsing.symbol_end_pos () }

let mk_expr shape =
    { shape; span = cur_span () }

let join_span sp1 sp2 =
    { lhs = sp1.lhs
    ; rhs = sp2.rhs }


let error msg = raise (Error.Error(cur_span (), SyntaxError msg))
%}

%token TOK_EOF
%token TOK_LPAREN TOK_RPAREN TOK_LBRACK TOK_RBRACK TOK_LBRACE TOK_RBRACE
%token TOK_TILDE
%token TOK_MINUS_GT TOK_EQ_GT
%token TOK_STAR TOK_COMMA TOK_DOT
%token TOK_EQ
%token TOK_COLON TOK_COLON_GT
%token TOK_UNDERSCORE
%token TOK_AT

%token<string> TOK_NAME
%token<int> TOK_INT
%token TOK_KW_TYPE TOK_KW_FORALL TOK_KW_EXISTS
%token TOK_KW_FUN TOK_KW_LET TOK_KW_IN



%right    TOK_MINUS_GT TOK_EQ_GT
%right    TOK_COMMA
%right    TOK_STAR
%nonassoc TOK_EQ
%left     TOK_COLON TOK_COLON_GT
%left     TOK_TILDE
%nonassoc TOK_AT
%left     TOK_DOT


%type<Syntax.Surface.expr> single_expr
%start single_expr

%type<Syntax.span * Syntax.Surface.top_level> single_top_level
%start single_top_level

%type<(Syntax.span * Syntax.Surface.top_level) list> program
%start program

%%

program :
    | top_level TOK_EOF { [$1] }
    | top_level program { $1 :: $2 }
;


single_top_level :
    | top_level TOK_EOF { $1 }
;


single_expr :
    | expr TOK_EOF { $1 }
;


top_level :
    | TOK_KW_LET TOK_NAME TOK_COLON expr { cur_span (), AxiomDecl ($2, $4) }
    | TOK_KW_LET TOK_NAME TOK_EQ    expr { cur_span (), Definition($2, None, $4) }
    | error                              { error "expecting top level clause" }
;


expr :
    | binop_expr
        { $1 }

    | TOK_KW_LET TOK_NAME TOK_EQ expr TOK_KW_IN expr
        { mk_expr @@ Let(($2, None, $4), $6) }

    | TOK_KW_LET TOK_NAME TOK_COLON binop_expr TOK_EQ expr TOK_KW_IN expr
        { mk_expr @@ Let(($2, Some $4, $6), $8) }

    | TOK_KW_FORALL param_list TOK_MINUS_GT expr
        { List.fold_right (fun (name, kind, typ) body -> mk_expr @@ TyFun(name, kind, typ, body)) $2 $4 }

    | binop_expr TOK_MINUS_GT expr
        { mk_expr @@ TyFun("", Explicit, $1, $3) }

    | TOK_KW_FUN param_list_opt_ann TOK_MINUS_GT expr
        { List.fold_right (fun (name, kind, typ) body -> mk_expr @@ Fun(name, kind, typ, body)) $2 $4 }

    | TOK_KW_EXISTS explicit_param_list TOK_MINUS_GT expr
        { List.fold_right (fun (name, _, typ) body -> mk_expr @@ TyPair(name, typ, body)) $2 $4 }

    | error
        { error "expecting expression" }
;

binop_expr:
    | app_expr
        { $1 }

    | binop_expr TOK_COLON binop_expr
        { mk_expr @@ Ann($1, $3) }

    | binop_expr TOK_STAR binop_expr
        { mk_expr @@ TyPair("", $1, $3) }

    | binop_expr TOK_COMMA binop_expr
        { mk_expr @@ Pair($1, $3) }

    | binop_expr TOK_EQ binop_expr
        { mk_expr @@ TyEq($1, $3) }

    | binop_expr TOK_COLON_GT binop_expr
        { mk_expr @@ Coe($1, $3) }
;

app_expr:
    | atom_expr
        { $1 }

    | app_expr atom_expr
        { mk_expr @@ App($1, $2) }
;

atom_expr :
    | TOK_LPAREN expr TOK_RPAREN
        { $2 }

    | TOK_NAME
        { mk_expr @@ Var $1 }

    | TOK_KW_TYPE
        { mk_expr @@ Type 0 }

    | TOK_KW_TYPE TOK_INT
        { mk_expr @@ Type $2 }

    | TOK_TILDE atom_expr
        { mk_expr @@ Shift(1, $2) }

    | atom_expr TOK_DOT TOK_INT
        { match $3 with
          | 1 -> mk_expr @@ Proj($1, `Fst)
          | 2 -> mk_expr @@ Proj($1, `Snd)
          | _ -> failwith "invalid field of pair" }

    | TOK_UNDERSCORE
        { mk_expr Hole }

    | TOK_AT atom_expr
        { mk_expr @@ Explicitfy $2 }

    | TOK_AT TOK_LBRACE expr TOK_RBRACE
        { mk_expr @@ ElimImplicit $3 }
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


explicit_param_list :
    | explicit_param_decl
        { $1 }
    | explicit_param_decl explicit_param_list
        { $1 @ $2 }
;


explicit_param_decl :
    | TOK_LPAREN name_list_nonempty TOK_COLON expr TOK_RPAREN
        { List.map (fun name -> (name, Explicit, $4)) $2 }
;

param_decl :
    | explicit_param_decl
        { $1 }
    | TOK_LBRACE name_list_nonempty TOK_COLON expr TOK_RBRACE
        { List.map (fun name -> (name, Implicit, $4)) $2 }
;

param_decl_opt_ann :
    | TOK_LPAREN name_list_nonempty TOK_COLON expr TOK_RPAREN
        { List.map (fun name -> (name, Explicit, Some $4)) $2 }
    | TOK_NAME
        { [$1, Explicit, None] }
    | TOK_LBRACE name_list_nonempty TOK_COLON expr TOK_RBRACE
        { List.map (fun name -> (name, Implicit, Some $4)) $2 }
    | TOK_LBRACE name_list_nonempty TOK_RBRACE
        { List.map (fun name -> name, Implicit, None) $2 }
;

name_list_nonempty :
    | TOK_NAME                    { [$1] }
    | TOK_NAME name_list_nonempty { $1 :: $2 }
;
