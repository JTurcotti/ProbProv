%{
    open Raw_expr
    let fst (x, _, _) = x

    let make_raw_aexp d s e : raw_aexp =
      {data=d; start_pos=s; end_pos=e}

    let desugar_fld_assign (obj_str, obj_s, obj_e) (dot_s, _) (_, _, fld_e) v : raw_expr =
      let obj_aexp = make_raw_aexp (Raw_Var(obj_str)) obj_s obj_e in
      let obj_and_fld = make_raw_aexp (Raw_Unop(obj_aexp)) dot_s fld_e in
      let obj_and_fld_and_val = make_raw_aexp (Raw_Binop(obj_and_fld, v)) dot_s fld_e in
      Raw_Assign(obj_str, obj_and_fld_and_val)
      
%}

%token <string * int * int> IDENT
%token <int * int> CONST
%token <int * int> BINOP
%token <int * int> UNOP
%token <int * int> DOT
%token LPAREN RPAREN LBRACE RBRACE EQ IF ELSE SEMI SKIP DEF EOF TO ASSERT BY COMMA

%start main
%type <raw_program> main
%type <raw_aexp> aexp
%type <raw_expr> expr

%%

main: fdecl_list EOF {Raw_Program($1)}

fdecl_list: {[]}
  | fdecl fdecl_list {$1 :: $2}

fdecl: DEF IDENT ident_list TO ident_list LBRACE expr RBRACE {
  {raw_name=fst $2; raw_params=$3; raw_results=$5; raw_body = $7}
}

ident_list: LPAREN idents RPAREN {$2}
  | IDENT {[$1]}

idents: {[]}
  | some_idents {$1}


some_idents: IDENT {$1 :: []}
  | IDENT COMMA some_idents {$1 :: $3}


two_or_more_idents: IDENT COMMA IDENT {(fst $1) :: (fst $3) :: []}
  | IDENT COMMA two_or_more_idents {(fst $1) :: $3}


expr:
  | SKIP {Raw_Skip}
  | IF aexp LBRACE expr RBRACE ELSE LBRACE expr RBRACE {Raw_Cond($2, $4, $8)}
  | IF aexp LBRACE expr RBRACE  {Raw_Cond($2, $4, Raw_Skip)}
  | IDENT EQ aexp {Raw_Assign(fst $1, $3)}
  | IDENT DOT IDENT EQ aexp {desugar_fld_assign $1 $2 $3 $5}
  | two_or_more_idents EQ aexp {Raw_FAssign($1, $3)}
  | expr SEMI expr {Raw_Seq($1, $3)}
  | ASSERT IDENT BY aexp {Raw_Assert(fst $2, $4)}
  | aexp {Raw_AExp($1)}

some_aexps: aexp {$1 :: []}
  | aexp COMMA some_aexps {$1 :: $3}

aexps: {[]}
  | some_aexps {$1}

aexp:
  | LPAREN aexp RPAREN {$2}
  | IDENT {match $1 with (str, s, e) -> make_raw_aexp (Raw_Var(str)) s e}
  | CONST {match $1 with (s, e) -> make_raw_aexp Raw_Const s e}
  | UNOP aexp {match $1 with (s, e) -> make_raw_aexp (Raw_Unop($2)) s e}
  | aexp DOT IDENT {match $2, $3 with (s, _), (_, _, e) -> make_raw_aexp (Raw_Unop($1)) s e}
  | aexp BINOP aexp {match $2 with (s, e) -> make_raw_aexp (Raw_Binop($1, $3)) s e}
  | IDENT LPAREN aexps RPAREN {match $1 with (str, s, e) ->
				 make_raw_aexp (Raw_FApp(str, $3)) s e}


