(*
 * Copyright (c) 2017, Artem Shinkarov <artyom.shinkaroff@gmail.com>
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
 * REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
 * AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
 * INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
 * LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE
 * OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
 * PERFORMANCE OF THIS SOFTWARE.
 *)

%{

open Ast
open Lexing
open Ordinals

let error_loc pos msg =
    let line = pos.pos_lnum in
    let col = pos.pos_cnum - pos.pos_bol in
    Printf.sprintf "error:%d:%d: %s" line col msg

(* This is a helper type to allow for short generators of form:
   _(iv): expr
   as opposed to regular generators
   lb_expr <= iv < ub_expr  *)
type gen_opt =
     | FullGen of expr * string * expr
     | DefGen of string


let mk_full_gen shp x =
    let mul_shp_zero =
        ELambda ("x",
                 EImap (EUnary (OpShape, EVar ("x")),
                        EArray ([]),
                        [((EArray ([ENum (zero)]),
                           "iv",
                           EUnary (OpShape, EVar ("x"))),

                          EBinOp (OpMult,
                                  EApply (EVar ("x"), EVar ("iv")),
                                  ENum (zero)))]))
    in
        (EApply (mul_shp_zero, shp),
         x,
         shp)

%}

%token <int> INT
%token <string> ID
%token TRUE FALSE IF THEN ELSE LETREC IN OMEGA ISLIM LAMBDA IMAP
%token BAR DOT COLON COMMA PLUS MINUS MULT DIV EQ NE LT LE GT GE
%token LSQUARE RSQUARE LPAREN RPAREN LBRACE UNDERSCORE EOF

%nonassoc IF
%nonassoc ELSE
%nonassoc IN
%nonassoc ISLIM
%nonassoc LETREC
%nonassoc LAMBDA
%nonassoc DOT
%nonassoc TRUE
%nonassoc FALSE
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
%nonassoc BAR

%left fun_Apply

%start prog
%type <Ast.expr> prog

%%


prog: expr EOF { $1 }
      | error
      {
          raise (ImapFailure (error_loc $startpos "parser failed"))
      }
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
    | IMAP expr inner_frame LBRACE gen_exprs
      {
          let out_shp = $2 in
          let ge = List.map (fun x ->
                             match x with
                             | (FullGen (lb, x, ub), e) ->
                                     ((lb, x, ub), e)
                             | (DefGen (x), e) ->
                                     (* construct gen (out_shp * 0) <= x < out_shp *)
                                     (mk_full_gen out_shp x, e))
                             $5
          in
          EImap ($2, $3, ge)
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

%inline inner_frame:
    | (* empty *)
      {
          EArray ([])
      }
    | BAR expr
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
        FullGen ($1, $3, $5)
    }
    | UNDERSCORE LPAREN ID RPAREN
      {
          DefGen ($3)
      }
    ;

expr_list:
    | { [] }
    | expr { $1 :: [] }
    | expr COMMA expr_list { $1 :: $3 }
    ;

const:
    INT { ENum (int_to_ord $1) }
    | OMEGA { ENum (omega) }
    | LSQUARE expr_list RSQUARE
      {
          EArray ($2)
      }
    | TRUE { ETrue }
    | FALSE { EFalse }
    ;
