/* File parser.mly */
%{
    open River
%}
%token COMMENT
%token <int> INT
%token <string> IDENT
%token ITYPE
%token STYPE
%token PLUS MINUS MULTIPLY DIVIDE
%token NOT
%token LT GT GEQ LEQ NEQ EQ
%token CONS DOT
%token ASSIGN
%token LPAREN RPAREN
%token LBRACE RBRACE
%token LSQ COLON RSQ
%token LET
%token DEFINE
%token LTYPE
%token IF ELSE
%token LOOP PRINT READ
%token SEMICOLON
%token EOF
/* Lowest Precedence */
%right ASSIGN
%nonassoc ITYPE STYPE
%nonassoc LTYPE
%nonassoc DEFINE
%nonassoc IF
%nonassoc ELSE
%left PLUS MINUS
%left MULTIPLY DIVIDE
%right LT GT GEQ LEQ NEQ EQ
%nonassoc UMINUS
/* Highest Precedence */
%start parser_main
%type <Riv.rivTerm> parser_main
%type <Riv.rivType> type_spec
%%
parser_main: lines EOF;

lines: line lines | line;

line: expr SEMICOLON { $1 };

type_spec: ITYPE { RivInt }
    | STYPE LT type_spec GT {RivStream($3)}
    | type_spec LTYPE LPAREN comma_sep RPAREN {RivLambda($1, $4)}
    | LPAREN type_spec RPAREN {$2}
;

comma_sep: type_spec { $1 }
    | type_spec COMMA comma_sep { $1 :: $3 }
;

expr: INT                      { RmNum $1 }
 | IDENT                       { RmVar $1 }
 | LET LPAREN IDENT COLON type_spec RPAREN EQUALS expr IN expr { RmLet ($3, $5, $8, $10) }
 | expr LPAREN expr RPAREN     { RmApp ($1, $3) }
 | expr PLUS expr              { RmPlus ($1, $3) }
 | expr MINUS expr             { RmMinus ($1, $3) }
 | expr MULTIPLY expr          { RmMultiply ($1, $3) }
 | expr DIVIDE expr            { RmDivide ($1,$3) }
 | expr LT expr                { RmLessThan ($1, $3) }
 | expr GT expr                { RmGreaterThan ($1, $3) }
 | expr GEQ expr               { RmGreaterEqualTo ($1, $3) }
 | expr LEQ expr               { RmLessEqualTo ($1, $3) }
 | expr NEQ expr               { RmNotEqualTo ($1, $3) }
 | expr EQ expr                { RmEqualTo ($1, $3) }
 | expr CONS expr              { RmCons ($1, $3) } /* :: (INT * INT -> STREAM<INT>) */
 | expr DOT expr               { RmAppend($1, $3) } /* . (INT * INT -> INT) */
 | IDENT LSQ expr RSQ           { RmIndex($1, $3) }
 | IDENT LSQ COLON INT RSQ     { RmSection($1, 0, $4) }
 | IDENT LSQ INT COLON RSQ     { RmSectionEnd($1, $3) }
 | IDENT LSQ INT COLON INT RSQ { RmSection($1, $3, $5) }
 /* Predefined Function */
 | 
 | type_spec IDENT ASSIGN expr { RmSet ($2, $4)}
 | IF LPAREN expr RPAREN LBRACE expr RBRACE ELSE LBRACE expr RBRACE  { RmIf ($3, $6, $10) }
 | IF LPAREN expr RPAREN LBRACE expr RBRACE { RmIf ($3, $6) }
 | type_spec LTYPE LPAREN type_spec IDENT RPAREN LBRACE expr RBRACE {RmAbs ($1, $4, $8) }
 | LPAREN expr RPAREN          { $2 }
;