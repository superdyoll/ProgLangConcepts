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
%token COMMA
%token EQUALS
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
/* Highest Precedence */
%start parser_main
%type <River.rivTerm> parser_main
%type <River.rivType> type_spec
%%
parser_main: line EOF { $1 };

line: expr SEMICOLON { $1 };

type_spec:
    | LPAREN RPAREN { RivUnit } 
    | ITYPE { RivStream(RivInt) }
    | STYPE LT type_spec GT { RivStream($3) }
    | type_spec LTYPE LPAREN type_spec RPAREN { RivFun($4, $1) }
    | type_spec LTYPE LPAREN RPAREN { RivFun(RivUnit, $1) }
    | LPAREN type_spec RPAREN { $2 }
;

expr: 
/* Let Statements */
 | LET LPAREN type_spec IDENT ASSIGN expr RPAREN LBRACE expr RBRACE { RmLet ($3, $4, $6, $9) }
/* If statements */
 | IF LPAREN expr RPAREN LBRACE expr RBRACE ELSE LBRACE expr RBRACE  { RmIf ($3, $6, $10) }
 /* Lambdas */
 | type_spec LTYPE LPAREN type_spec IDENT RPAREN LBRACE expr RBRACE {RmLbd ($1, $4, $5, $8) }
 | type_spec LTYPE LPAREN RPAREN LBRACE expr RBRACE { RmLbdEmpty($1,$6) }
/* Sections */
| expr LSQ COLON expr RSQ     { RmSectionStart($1, $4) }
 | expr LSQ expr COLON expr RSQ { RmSection($1, $3, $5) }
 | expr LSQ expr COLON RSQ     { RmSectionEnd($1, $3) }
 | expr LSQ expr RSQ          { RmIndex($1, $3) }
/* Apply */
 | expr LPAREN expr RPAREN     { RmApp ($1, $3) }
 | expr LPAREN RPAREN          { RmApp ($1, RmUnit())}
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
 | LPAREN expr RPAREN          { $2 }
 | IDENT                       { RmVar $1 }
 | INT                         { RmStream(RivInt,Stream(RmNum($1), function () -> StreamEnd())) }
 | LPAREN RPAREN               { RmUnit() }
 | MINUS expr                  { RmUMinus ($2) }
 | READ LPAREN RPAREN          { RmRead() }
;
