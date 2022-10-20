%{
    open Raw_expr
%}

%token <string> IDENT
%token BINOP UNOP LPAREN RPAREN CONST LBRACE RBRACE EQ IF THEN ELSE SEMI SKIP DEF EOF TO ASSERT BY

%start main
%type <raw_program> main

%%

main: fdecl_list EOF {Raw_Program($1)}

fdecl_list: {[]}
  | fdecl fdecl_list {$1 :: $2}

fdecl: DEF IDENT ident_list TO ident_list LBRACE expr RBRACE {
  {raw_name=$2; raw_params=$3; raw_results=$5; raw_body = $7}
}

ident_list: LPAREN idents RPAREN {$2}

idents: {[]}
  | IDENT idents {$1 :: $2}


expr:
  | SKIP {Raw_Skip}
  | IF aexp LBRACE expr RBRACE ELSE LBRACE expr RBRACE {Raw_Cond($2, $4, $8)}
  | IDENT EQ aexp {Raw_Assign($1, $3)}
  | expr SEMI expr {Raw_Seq($1, $3)}
  | ASSERT IDENT BY aexp {Raw_Assert($2, $4)}
  | aexp {Raw_AExp($1)}

aexp:
  | LPAREN aexp RPAREN {$2}
  | IDENT {Raw_Var($1)}
  | CONST {Raw_Const}
  | UNOP aexp {Raw_Unop($2)}
  | aexp BINOP aexp {Raw_Binop($1, $3)}
  | IDENT LPAREN aexp RPAREN {Raw_FApp($1, $3)}


