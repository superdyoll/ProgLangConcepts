%{
    open River
%}
%token COMMENT
%token <int> INT
%token <string> IDENT
%token ITYPE
%token GSTART GEND
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
%token LAMBDA
%token IF ELSE
%token LOOP PRINT READ
%token SEMICOLON
%token EOF
/* Lowest Precedence */
%right ASSIGN
%nonassoc DEFINE
%left PLUS MINUS
%left MULTIPLY DIVIDE
%right LT GT GEQ LEQ NEQ EQ
%nonassoc UMINUS
/* Highest Precedence */
%start parser_main             /* the entry point */
%type <Riv.rivTerm> parser_main
%type <Riv.rivType> type_spec
%%
parser_main: expr EOF { $1 }
;
type_spec: ITYPE { RivInt }
    | type_spec FUNTYPE type_spec { RivFun ($1,$3) }
    | LPAREN type_spec RPAREN {$2}
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
 | IF LPAREN expr RPAREN LBRACE expr RBRACE ELSE LBRACE expr RBRACE{ RmIf ($3, $6, $8) }
 | type_spec LAMBDA LPAREN type_spec IDENT RPAREN LBRACE expr RBRACE {RmAbs ($3, $5, $7) }
 | LPAREN expr RPAREN          { $2 }
;