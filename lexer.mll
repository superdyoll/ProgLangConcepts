(* File lexer.mll *)
{
open Parser        (* The type token is defined in parser.mli *)
}
rule lexer_main = parse
      [' ' '\t' '\n']     { lexer_main lexbuf }     (* skip blanks *)
    | '-'? ['0'-'9']+ as lxm { INT(int_of_string lxm) }
    | "//" _ +  { COMMENT }
    (* Types *)
    | "int"     { ITYPE }
    | "<"       { GSTART }
    | ">"       { GEND }
    | "let"     { LET }
    | "def"     { DEFINE }
    | "if"      { IF }
    | "else"    { ELSE }
    | ';'       { SEMICOLON }
    (* Functions *)
    | "loop"    { LOOP }
    | "print"    { PRINT }
    | "read"    { READ }
    | ['a'-'z'] + as lxm { IDENT(lxm) }
    (* Operators *)
    | '+'       { PLUS }
    | '-'       { MINUS }
    | '*'       { MULTIPLY }
    | '/'       { DIVIDE }
    (* Comparison Operators *)
    | '<'       { LT }
    | '>'       { GT }
    | ">="      { GEQ }
    | "<="      { LEQ }
    | "!"       { NOT }
    | "=="      { EQ }
    | "!="      { NEQ }
    (* Concatenators *)
    | "::"      { CONS }
    | '.'       { DOT }
    (* Assignment *)
    | '='       { ASSIGN }
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
