%{
  open Syntax
%}

%token <string> IDENT
%token <int> INT
%token MU COMMA INL INR LBRACE BAR RBRACE BREAK GETC PUTC
%token LANGLE RANGLE LPAREN RPAREN OFCOURSE UP
%token EOF

%type <Syntax.term> term
%start term

%%

term:
 | term_pattern {
   match $1 with
   | Id(t) -> t
   | p -> Pat(p)
 }
 | MU id_pattern COMMA command { Mu($2, $4) }
 | INL term { InL($2) }
 | INR term { InR($2) }
 | LBRACE id_pattern COMMA command BAR id_pattern COMMA command RBRACE
     { Proj(($2, $4), ($6, $8)) }
 | INT { Const(CInt($1)) }
 | BREAK { Const(CBreak) }
 | GETC { Const(CGetc) }
 | PUTC { Const(CPutc) }

command:
 | LANGLE term BAR term RANGLE
     { Cmd($2, $4) }

term_pattern:
 | IDENT { Id(Var($1)) }
 | OFCOURSE term { Floor($2) }
 | UP term { Up($2) }
 | LPAREN term_pattern COMMA term_patterns RPAREN
     { Tuple($2, $4) }

term_patterns:
 | term_pattern { $1 }
 | term_pattern COMMA term_patterns
     { Tuple($1, $3) }

id_pattern:
 | IDENT { Id($1) }
 | OFCOURSE IDENT { Floor($2) }
 | UP IDENT { Up($2) }
 | LPAREN id_pattern COMMA id_patterns RPAREN
     { Tuple($2, $4) }

id_patterns:
 | id_pattern { $1 }
 | id_pattern COMMA id_patterns
     { Tuple($1, $3) }
