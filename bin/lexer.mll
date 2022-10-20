{
open Parser
exception FAIL
}

rule token = parse
     | [' ' '\t' '\n'] {token lexbuf}
     | "//"[^'\n']* {token lexbuf}
     | ['0'-'9']+ {CONST}
     |	'(' {LPAREN}
     |	')' {RPAREN}
     |	'{' {LBRACE}
     |	'}' {RBRACE}
     |  ['+''-''*''/'] | "==" | "!=" | "||" | "&&" {BINOP}
     |	'!' {UNOP}
     |  '=' {EQ}
     |	"->" {TO}
     |  "if"	{IF}
     |	"else"	{ELSE}
     |  ';' {SEMI}
     |	"skip" {SKIP}
     |	"def"  {DEF}
     | 	"assert" {ASSERT}
     |	"by" {BY}
     | ['a'-'z''A'-'Z']['a'-'z''A'-'Z''0'-'9'''''_']* as ident { IDENT(ident) }
     | 	eof {EOF}
