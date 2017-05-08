%{

open Ast;;

%}

%token <int> INT
%token <string> ID
%token TRUE FALSE IF THEN ELSE LETREC IN REDUCE FILTER OMEGA ISLIM LAMBDA
%token BAR DOT COLON COMMA PLUS MINUS MULT DIV EQ NE LT LE GT GE
%token LSQUARE RSQUARE LPAREN RPAREN LBRACE RBRACE EOF

%nonassoc IF
%nonassoc THEN
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
%nonassoc REDUCE
%nonassoc FILTER
%nonassoc IMAP
%nonassoc COLON

%left COMMA

%left EQ NE LT LE GT GE
%left PLUS MINUS
%left MULT DIV

%nonassoc LPAREN RPAREN LSQUARE RSQUARE LBRACE RBRACE

%left fun_Apply

%start prog
%type <Ast.expr> prog

%%


prog: expr EOF { $1 }


expr:
    const
      {
         $1
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
    | expr PLUS expr
      {
          EBinOp (OpPlus, $1, $3)
      }
    | expr MULT expr
      {
          EBinOp (OpMult, $1, $3)
      }
    | IF expr THEN expr ELSE expr
      {
          ECond ($2, $4, $6)
      }
    | LETREC ID EQ expr IN expr
      {
          ELetRec ($2, $4, $6)
      }
    | REDUCE expr
      {
          (* TODO Check that Expr is 3-argument application! *)
          EReduce (ETrue, ETrue, ETrue)
      }
    | FILTER expr
      {
          (* TODO Check that Expr is 2-arg application application! *)
          EFilter (ETrue, ETrue)
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

gen_exprs:
    gen COLON expr
      {
          ($1, $3) :: []
      }
    | gen COLON expr COMMA gen_exprs
      {
          ($1, $3) :: $5
      }

gen:
    expr LE ID LT expr
    {
        ($1, $3, $5)
    }

expr_list:
    expr { $1 :: [] }
    | expr COMMA expr_list { $1 :: $3 }

const:
    INT { ENum ((0, $1) :: []) }
    | LSQUARE expr_list RSQUARE
      {
          EArray ($2)
      }
    | TRUE { ETrue }
    | FALSE { EFalse }
