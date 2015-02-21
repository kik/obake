%{
  open Syntax
%}

%token <string> IDENT
%token <int> INT
%token MU QMU COMMA INL INR LBRACE BAR RBRACE BREAK GETC PUTC FIX
%token PRINT_INT NEG ADD SUB LT GT LE GE EQ NE
%token LANGLE RANGLE LPAREN RPAREN OFCOURSE UP
%token EOF

%type <Syntax.term> term
%start term

%%

term:
 | IDENT { Var($1) }
 | OFCOURSE term { Pat(Floor($2)) }
 | UP term { Up($2) }
 | LPAREN RPAREN { Pat(Unit) }
 | LPAREN term RPAREN { $2 }
 | LPAREN term_pattern COMMA term_patterns RPAREN
     { Pat(Tuple($2, $4)) }
 | MU  id_pattern COMMA command { Mu(NegMu, $2, $4) }
 | QMU id_pattern COMMA command { Mu(PosMu, $2, $4) }
 | INL term { InL($2) }
 | INR term { InR($2) }
 | LBRACE id_pattern COMMA command BAR id_pattern COMMA command RBRACE
     { Proj(($2, $4), ($6, $8)) }
 | INT { Const(CInt($1)) }
 | BREAK { Const(CBreak) }
 | GETC { Const(CGetc) }
 | PUTC { Const(CPutc) }
 | PRINT_INT { Const(CPrintInt) }
 | FIX  { Const(CFix) }
 | NEG { Const(CNeg) }
 | ADD { Const(CAdd) }
 | SUB { Const(CSub) }
 | LT { Const(CLt) }
 | GT { Const(CGt) }
 | LE { Const(CLe) }
 | GE { Const(CGe) }
 | EQ { Const(CEq) }
 | NE { Const(CNe) }

command:
 | LANGLE term BAR term RANGLE
     { Cmd($2, $4) }

term_pattern:
 | term {
   match $1 with
   | Pat(p) -> p
   | t -> Id(t)
 }

term_patterns:
 | term_pattern { $1 }
 | term_pattern COMMA term_patterns
     { Tuple($1, $3) }

id_pattern:
 | IDENT { Id($1) }
 | OFCOURSE IDENT { Floor($2) }
 | LPAREN RPAREN { Unit }
 | LBRACE RBRACE { False }
 | LPAREN id_pattern RPAREN { $2 }
 | LPAREN id_pattern COMMA id_patterns RPAREN
     { Tuple($2, $4) }

id_patterns:
 | id_pattern { $1 }
 | id_pattern COMMA id_patterns
     { Tuple($1, $3) }
