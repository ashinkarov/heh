%{

open Ast;;

%}

%token <int> INT
%token <string> ID
%token TRUE FALSE IF THEN ELSE LETREC IN OMEGA ISLIM LAMBDA IMAP
%token BAR DOT COLON COMMA PLUS MINUS MULT DIV EQ NE LT LE GT GE
%token LSQUARE RSQUARE LPAREN RPAREN LBRACE EOF

%nonassoc IF
%nonassoc ELSE
%nonassoc IN
%nonassoc ISLIM
%nonassoc LETREC
%nonassoc LAMBDA
%nonassoc DOT
%nonassoc TRUE
%nonassoc FALSE
%nonassoc BAR
%nonassoc INT
%nonassoc IMAP
%nonassoc COLON
%nonassoc ID
%nonassoc OMEGA

%left COMMA

%left EQ NE LT LE GT GE
%left PLUS MINUS
%left MULT DIV

%nonassoc LPAREN LSQUARE

%left fun_Apply

%start prog
%type <Ast.expr> prog

%%


prog: expr EOF { $1 }
      ;


expr:
    const
      {
         $1
      }
    | ID
      {
          EVar ($1)
      }
    | ISLIM expr
      {
          EUnary (OpIsLim, $2)
      }
    | BAR expr BAR
      {
          EUnary (OpShape, $2)
      }
    | LAMBDA ID DOT expr
      {
          ELambda ($2, $4)
      }
    | expr binary_op expr
      {
          EBinOp ($2, $1, $3)
      }
    | IF expr THEN expr ELSE expr
      {
          ECond ($2, $4, $6)
      }
    | LETREC ID EQ expr IN expr
      {
          ELetRec ($2, $4, $6)
      }
    | IMAP expr BAR expr LBRACE gen_exprs
      {
          EImap ($2, $4, $6)
      }
    | expr expr %prec fun_Apply
      {
          EApply ($1, $2)
      }
    | LPAREN expr RPAREN
      {
          $2
      }
    ;


%inline binary_op:
    | PLUS                   { OpPlus }
    | MINUS                  { OpMinus }
    | MULT                   { OpMult }
    | DIV                    { OpDiv }
    | LT                     { OpLt }
    | GT                     { OpGt }
    | EQ                     { OpEq }
    | NE                     { OpNe }
    | GE                     { OpGe }
    | LE                     { OpLe }
    ;

gen_exprs:
    gen COLON expr
      {
          ($1, $3) :: []
      }
    | gen COLON expr COMMA gen_exprs
      {
          ($1, $3) :: $5
      }
    ;

gen:
    expr LE ID LT expr
    {
        ($1, $3, $5)
    }
    ;

expr_list:
    expr { $1 :: [] }
    | expr COMMA expr_list { $1 :: $3 }
    ;

const:
    INT { ENum ((0, $1) :: []) }
    | OMEGA { ENum ((1, 0) :: []) }
    | LSQUARE expr_list RSQUARE
      {
          EArray ($2)
      }
    | TRUE { ETrue }
    | FALSE { EFalse }
    ;
