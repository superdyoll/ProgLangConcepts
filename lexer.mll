(* File lexer.mll *)
{
open Parser        (* The type token is defined in parser.mli *)
}
rule lexer_main = parse
      [' ' '\t' '\n']     { lexer_main lexbuf }     (* skip blanks *)
    | ['0'-'9']+ as lxm { INT(int_of_string lxm) }
    | "//" _ +  { COMMENT }
    (* Functions *)
    | "print"    { PRINT }
    | "read"    { READ }
    (* Types *)
    | "int"     { ITYPE }
    | "stream"  { STYPE }
    | "lambda"  { LTYPE }
    | "let"     { LET }
    | "def"     { DEFINE }
    | "if"      { IF }
    | "else"    { ELSE }
    | ['a'-'z' '_'] + as lxm { IDENT(lxm) }
    (* Comparison Operators *)
    | ">="      { GEQ }
    | "<="      { LEQ }
    | '<'       { LT }
    | '>'       { GT }
    | "=="      { EQ }
    | "!="      { NEQ }
    | "!"       { NOT }
    (* Operators *)
    | '+'       { PLUS }
    | '-'       { MINUS }
    | '*'       { MULTIPLY }
    | '/'       { DIVIDE }
    | '%'       { MODULUS }
    (* Concatenators *)
    | "::"      { CONS }
    | '.'       { DOT }
    (* Assignment *)
    | '='       { ASSIGN }
    | ','       { COMMA }
    (* Bracketing *)
    | '('       { LPAREN }
    | ')'       { RPAREN }
    | '{'       { LBRACE }
    | '}'       { RBRACE }
    (* Indexing *)
    | '['       { LSQ }
    | ']'       { RSQ }
    | ':'       { COLON }
    | eof       { EOF }
