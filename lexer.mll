{
  open Parser
}

let space = [' ' '\t' '\n' '\r']
let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']

rule token = parse
| space+ { token lexbuf }
| "#" [^ '\n' ]* '\n' { token lexbuf }
| "(*" { comment lexbuf; token lexbuf }
| ',' { COMMA }
| '{' { LBRACE }
| '|' { BAR }
| '}' { RBRACE }
| '<' { LANGLE }
| '>' { RANGLE }
| '(' { LPAREN }
| ')' { RPAREN }
| '!' { OFCOURSE }
| '^' { UP }
| "mu" { MU }
| "'mu" { QMU }
| "inl" { INL }
| "inr" { INR }
| "break" { BREAK }
| "getc" { GETC }
| "putc" { PUTC }
| digit+ { INT(int_of_string (Lexing.lexeme lexbuf)) }
| alpha (digit|alpha|'_')* { IDENT(Lexing.lexeme lexbuf) }
| eof { EOF }

and comment = parse
| "*)" { () }
| "(*" { comment lexbuf; comment lexbuf }

