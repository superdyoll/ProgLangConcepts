/* File parser.mly */
%{
    open River
%}
%token <int> INT
%token <string> IDENT
%token ITYPE
%token STYPE
%token PLUS MINUS MULTIPLY DIVIDE MODULUS
%token NOT
%token LT GT GEQ LEQ NEQ EQ
%token CONS DOT
%token ASSIGN
%token LPAREN RPAREN
%token LRPAREN
%token LBRACE RBRACE
%token LSQ COLON RSQ
%token LET
%token DEFINE
%token LTYPE
%token IF ELSE
%token PRINT READ
%token EOF
%token COMMA
%token EQUALS
/* Lowest Precedence */
%right ASSIGN
%nonassoc ITYPE STYPE
%nonassoc LTYPE
%nonassoc DEFINE
%nonassoc IF
%nonassoc ELSE
%right DOT
%left PLUS MINUS
%left MULTIPLY DIVIDE MODULUS
%right LT GT GEQ LEQ NEQ EQ
%right LSQ RSQ COLON
/* Highest Precedence */
%start parser_main
%type <River.rivTerm> parser_main
%type <River.rivType> type_spec
%%
parser_main: line EOF { $1 };

line: expr { $1 };

type_spec:
    | ITYPE { RivStream(RivInt) }
    | STYPE LT type_spec GT { RivStream($3) }
    | type_spec LTYPE LPAREN type_spec RPAREN { RivFun($4, $1) }
    | type_spec LTYPE LRPAREN { RivFun(RivStream(RivInt), $1) }
    | LPAREN type_spec RPAREN { $2 }
;

expr: 
/* Let Statements */
 | LET LPAREN type_spec IDENT ASSIGN expr RPAREN LBRACE expr RBRACE { print_string "RmLet\n"; RmLet ($3, $4, $6, $9) }
/* If statements */
 | IF LPAREN expr RPAREN LBRACE expr RBRACE ELSE LBRACE expr RBRACE  { print_string "RmIf\n"; RmIf ($3, $6, $10) }
 /* Lambdas */
 | type_spec LTYPE LPAREN type_spec IDENT RPAREN LBRACE expr RBRACE {RmLbd ($1, $4, $5, $8) }
 | type_spec LTYPE LRPAREN LBRACE expr RBRACE { print_string "RmLbdEmpty\n"; RmLbdEmpty($1,$5) }
/* Apply */
 | READ LRPAREN          { print_string "RmRead\n"; RmRead() }
 | expr LPAREN expr RPAREN     { print_string "RmApp\n"; RmApp ($1, $3) }
 | expr LRPAREN          { print_string "RmApp\n"; RmApp ($1, RmUnit())}
 /* Sections */
| expr LSQ COLON expr RSQ     { print_string "RmSectionStart\n"; RmSectionStart($1, $4) }
 | expr LSQ expr COLON expr RSQ { print_string "RmSection\n"; RmSection($1, $3, $5) }
 | expr LSQ expr COLON RSQ     { print_string "RmSectionEnd\n"; RmSectionEnd($1, $3) }
 | expr LSQ expr RSQ          { print_string "RmIndex\n"; RmIndex($1, $3) }
 /* Operators */
 | expr PLUS expr              { print_string "RmPlus\n"; RmPlus ($1, $3) }
 | expr MINUS expr             { print_string "RmMinus\n"; RmMinus ($1, $3) }
 | expr MULTIPLY expr          { print_string "RmMultiply\n"; RmMultiply ($1, $3) }
 | expr DIVIDE expr            { print_string "RmDivide\n"; RmDivide ($1,$3) }
 | expr MODULUS expr           { print_string "RmModulus\n"; RmModulus ($1,$3) }
 | expr LT expr                { print_string "RmLessThan\n"; RmLessThan ($1, $3) }
 | expr GT expr                { print_string "RmGreaterThan\n"; RmGreaterThan ($1, $3) }
 | expr GEQ expr               { print_string "RmGreaterEqualTo\n"; RmGreaterEqualTo ($1, $3) }
 | expr LEQ expr               { print_string "RmLessEqualTo\n"; RmLessEqualTo ($1, $3) }
 | expr NEQ expr               { print_string "RmNotEqualTo\n"; RmNotEqualTo ($1, $3) }
 | expr EQ expr                { print_string "RmEqualTo\n"; RmEqualTo ($1, $3) }
 | expr CONS expr              { print_string "RmCons\n"; RmCons ($1, $3) } /* :: (INT * INT -> STREAM<INT>) */
 | expr DOT expr               { print_string "RmAppend\n"; RmAppend($1, $3) } /* . (INT * INT -> INT) */
 | LPAREN expr RPAREN          { print_string "BRACKETS\n"; $2 }
 | IDENT                       { print_string "RmVar\n"; RmVar $1 }
 | INT                         { print_string "RmInt\n"; RmStream(RivInt,Stream(RmNum($1), function () -> StreamEnd())) }
 | MINUS expr                  { print_string "RmUMinus\n"; RmUMinus ($2) }
 | LRPAREN                     { print_string "RmUnit\n"; RmUnit() }
;
