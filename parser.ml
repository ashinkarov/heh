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

module Loc = struct
    type t =
        {
            line: int;
            col: int;
        }
    type 'a loc =
        {
            value : 'a;
            loc : t;
        }

    let mk l c = {line=l ; col=c}
    let print l =
        Printf.printf "%s:%d:%d " !Globals.fname l.line l.col
end

module Tok = struct
    type t =
        {
            loc: Loc.t;
            tok: Lexer.token;
        }

    let mk loc tok = {loc; tok}
    let to_str tok = Lexer.tok_to_str tok.tok
    let get_tok tok = tok.tok
    let get_loc tok = tok.loc
    let eq tok lextok = tok.tok = lextok
end

let opt_get = function
  | Some x -> x
  | None -> raise (Invalid_argument "opt_get")


open Lexer
open Printf
open Ordinals
open Ast

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
                                  ESel (EVar ("x"), EVar ("iv")),
                                  ENum (zero)))]))
    in
        (EApply (mul_shp_zero, shp),
         x,
         shp)



let op_prec tok = match tok with
    (* = and <> have the least priority *)
    | EQ -> 1
    | NE -> 1

    (* comparisons <, <=, >, >=  *)
    | LT -> 2
    | LE -> 2
    | GT -> 2
    | GE -> 2

    (* addition/subtraction: +, -  *)
    | PLUS -> 3
    | MINUS -> 3

    (* multiplication/division/modulo: *, /, %  *)
    | MULT -> 4
    | DIV -> 4
    | MOD -> 4

    (* any other possibly user-defined operations  *)
    | _ -> 5

(* Stack to keep tokens that we have peeked at
   but not consumed yet.  *)
let tok_stack = ref []

(* State of the parser that indicates whether `|' can
   start an expression.  This is useful when disambiguating
   nested expression within |e|.  *)
let bar_starts_expr = ref true

(* FIXME add locations.  *)
let parse_err msg =
    raise (ImapFailure msg)

let get_loc lexbuf =
    let curr = lexbuf.Lexing.lex_curr_p in
    let line = curr.Lexing.pos_lnum in
    let col = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
    Loc.mk line col

(* Puts the token back on the to of the stack.  *)
let unget_tok tok =
    (* printf "unget-tok `%s'\n" @@ tok_to_str tok; *)
    tok_stack := tok :: !tok_stack

let get_token lexbuf =
    match !tok_stack with
    | [] ->
            let t = Lexer.token lexbuf in
            let l = get_loc lexbuf in
            (* print_sloc l; *)
            (* printf "get-token returns `%s'\n" @@ tok_to_str t; *)
            Tok.mk l t
    | h::t ->
            tok_stack := t;
            (*printf "get-token returns `%s'\n" @@ tok_to_str h;*)
            h

let peek_token lexbuf =
    let t = get_token lexbuf in
    unget_tok t;
    (*printf "peek-tok returns `%s'\n" @@ tok_to_str t;*)
    t

(* FIXME add 'msg' parameter to alter the error message.  *)
let expect_id lexbuf =
    let t = get_token lexbuf in
    match Tok.get_tok t with
    | ID (x) -> t
    | _ -> parse_err
           @@ sprintf "expected identifier, found `%s' instead"
                      (Tok.to_str t)

(* FIXME add 'msg' parameter to alter the error message.  *)
let expect_tok lexbuf t_exp =
    let t = get_token lexbuf in
    if Tok.get_tok t <> t_exp then
        parse_err
        @@ sprintf "expected token `%s', found `%s' instead"
                   (Lexer.tok_to_str t_exp)
                   (Tok.to_str t);
    t

(* Parse NON-EMPTY comma separated list of elements that
   can be parsed by `parse_fun' function.  *)
let rec parse_generic_list ?(msg="expression expected") lexbuf parse_fun =
    let e = parse_fun lexbuf in
    if e = None then
        parse_err msg;
    let t = peek_token lexbuf in
    if Tok.get_tok t = COMMA then
        let _ = get_token lexbuf in
        let l = parse_generic_list ~msg:msg lexbuf parse_fun in
        e :: l
    else
        [e]

let rec parse_primary lexbuf =
    let t = get_token lexbuf in
    match Tok.get_tok t with
    | TRUE ->   Some (ETrue)
    | FALSE ->  Some (EFalse)
    | ID x ->   Some (EVar (x))
    | INT n ->  Some (ENum (int_to_ord n))
    | OMEGA ->  Some (ENum (omega))
    | BAR ->    if !bar_starts_expr then begin
                    bar_starts_expr := false;
                    let e = parse_expr lexbuf in
                    if e = None then
                        parse_err "expression expected after |";
                    let t = peek_token lexbuf in
                    if Tok.get_tok t <> BAR then
                        parse_err "closing `|' missing to match the one at location";
                    let _ = get_token lexbuf in
                    bar_starts_expr := true;
                    Some (EUnary (OpShape, opt_get e))
                end else begin
                    unget_tok t;
                    None
                end
    | LSQUARE ->
                let bar_state = !bar_starts_expr in
                bar_starts_expr := true;

                let l = if Tok.get_tok (peek_token lexbuf) = RSQUARE then
                            []
                        else
                            parse_generic_list lexbuf parse_expr
                            ~msg:"array element definition is missing"
                        in
                let _ = expect_tok lexbuf RSQUARE in
                bar_starts_expr := bar_state;
                Some (EArray (List.map opt_get l))

    | LPAREN ->
                let bar_state = !bar_starts_expr in
                bar_starts_expr := true;
                let e = parse_expr lexbuf in
                if e = None then
                    parse_err "empty expression found";
                let _ = expect_tok lexbuf RPAREN in
                bar_starts_expr := bar_state;
                e

    | LAMBDA -> unget_tok t; parse_lambda lexbuf
    | IF     -> unget_tok t; parse_cond lexbuf
    | LETREC -> unget_tok t; parse_letrec lexbuf
    | IMAP   -> unget_tok t; parse_imap lexbuf


    | _ -> unget_tok t;
           None


and parse_postfix lexbuf =
    let e = ref @@ parse_primary lexbuf in
    while !e <> None && Tok.get_tok (peek_token lexbuf) = DOT do
        let _ = get_token lexbuf in
        let e1 = parse_primary lexbuf in
        if e1 = None then
            parse_err "expected index specification in selection";
        e := Some (ESel (opt_get !e, opt_get e1))
    done;
    !e

and parse_unary lexbuf =
    let t = peek_token lexbuf in
    match Tok.get_tok t with
    | ISLIM ->
            let _ = get_token lexbuf in
            let e = parse_unary lexbuf in
            if e = None then
                parse_err "expected expression after `islim' operator";
            Some (EUnary (OpIsLim, opt_get e))
    | _ ->
            parse_postfix lexbuf

and parse_app ?(e1=None) lexbuf  =
    match e1, parse_unary lexbuf with
    | None, Some e2 -> parse_app lexbuf ~e1:(Some e2)
    | Some e1, Some e2 -> parse_app lexbuf ~e1:(Some (EApply (e1, e2)))
    | _, None -> e1

and parse_binop ?(no_relop=false) lexbuf =
    let rec resolve_stack s prec =
        let e1, op1, p1 = Stack.pop s in

        if prec <= p1 then begin
            let e2, op2, p2 = Stack.pop s in
            let e = EBinOp (op_to_binop op1, opt_get e2, opt_get e1) in
            Stack.push (Some (e), op2, p2) s;
            resolve_stack s prec
        end else begin
            Stack.push (e1, op1, p1) s
        end
    in

    let e1 = parse_app lexbuf in
    let s = Stack.create () in

    (* First expression goes with no priority, priority = -1.
       FIXME we also use EOF as bogus operation, we can make this
             field of type token option to make it cleaner.  *)
    Stack.push (e1, EOF, -1) s;
    while is_op ~no_relop:no_relop (Tok.get_tok @@ peek_token lexbuf) do
        let t = get_token lexbuf in

        (* resolve priority stack.  *)
        resolve_stack s (op_prec @@ Tok.get_tok t);
        let e2 = parse_app lexbuf in
        if e2 = None then
            parse_err @@ sprintf "expression expected after %s" (Tok.to_str t);
        Stack.push (e2, Tok.get_tok t, (op_prec @@ Tok.get_tok t)) s;
    done;
    resolve_stack s 0;
    let e, op, prec = Stack.pop s in
    e


and parse_expr lexbuf =
    parse_binop lexbuf

and parse_lambda lexbuf =
    assert (LAMBDA = Tok.get_tok @@ get_token lexbuf);
    let t = expect_id lexbuf in
    let _ = expect_tok lexbuf DOT in
    let e = parse_expr lexbuf in
    if e = None then
        parse_err "expression expected after `.'";
    Some (ELambda (Tok.to_str t, opt_get e))

and parse_cond lexbuf =
    assert (IF = Tok.get_tok @@ get_token lexbuf);
    let bar_state = !bar_starts_expr in
    bar_starts_expr := true;
    let e1 = parse_expr lexbuf in
    if e1 = None then
        parse_err "expression expected after `if'";
    let _ = expect_tok lexbuf THEN in
    let e2 = parse_expr lexbuf in
    if e2 = None then
        parse_err "expression expected after `then'";
    let _ = expect_tok lexbuf ELSE in
    bar_starts_expr := bar_state;
    let e3 = parse_expr lexbuf in
    if e3 = None then
        parse_err "expression expected after `else'";
    Some (ECond (opt_get e1, opt_get e2, opt_get e3))

and parse_letrec lexbuf =
    assert (LETREC = Tok.get_tok @@ get_token lexbuf);
    let t = expect_id lexbuf in
    let _ = expect_tok lexbuf EQ in
    let bar_state = !bar_starts_expr in
    bar_starts_expr := true;
    let e1 = parse_expr lexbuf in
    bar_starts_expr := bar_state;
    if e1 = None then
        parse_err "expression expected after `=' and before `in'";
    let _ = expect_tok lexbuf IN in
    let e2 = parse_expr lexbuf in
    if e2 = None then
        parse_err "expression expected after `in'";
    Some (ELetRec (Tok.to_str t, opt_get e1, opt_get e2))

and parse_imap lexbuf =
    assert (IMAP = Tok.get_tok @@ get_token lexbuf);
    let bar_state = !bar_starts_expr in
    bar_starts_expr := (Tok.get_tok @@ peek_token lexbuf) = BAR;
    let sh1 = parse_expr lexbuf in
    if sh1 = None then
        parse_err "expression expected after `imap'";
    let sh2 = if BAR = Tok.get_tok @@ peek_token lexbuf then begin
                  bar_starts_expr := true;
                  let _ = get_token lexbuf in
                  let sh2 = parse_expr lexbuf in
                  if sh2 = None then
                      parse_err "cell shape specification expected";
                  sh2
              end else
                  Some (EArray ([])) in
    let _ = expect_tok lexbuf LBRACE in
    bar_starts_expr := bar_state;
    let l = parse_generic_list lexbuf parse_gen
                               ~msg:"generator expected" in
    let gl = List.map (fun x ->
                       match x with
                       | Some (FullGen (lb, x, ub), e) ->
                               ((lb, x, ub), e)
                       | Some (DefGen (x), e) ->
                               (* construct gen (out_shp * 0) <= x < out_shp *)
                               (mk_full_gen (opt_get sh1) x, e)
                       | _ -> raise (ImapFailure "error in parser function `parse_gen'"))
                       l
             in
    Some (EImap (opt_get sh1, opt_get sh2, gl))

and parse_gen lexbuf =
    let t = peek_token lexbuf in
    let gen = if Tok.get_tok t = UNDERSCORE then
                  let _ = get_token lexbuf in
                  let _ = expect_tok lexbuf LPAREN in
                  let iv = expect_id lexbuf in
                  let _ = expect_tok lexbuf RPAREN in
                  DefGen (Tok.to_str iv)
              else
                  let lb = parse_binop ~no_relop:true lexbuf in
                  if lb = None then
                      parse_err "lower bound expression expected";
                  let _ = expect_tok lexbuf LE in
                  let iv = expect_id lexbuf in
                  let _ = expect_tok lexbuf LT in
                  let ub = parse_binop lexbuf in
                  if ub = None then
                      parse_err "upper bound expression expected";
                  FullGen ((opt_get lb), (Tok.to_str iv), (opt_get ub))
              in
    let _ = expect_tok lexbuf COLON in
    let e = parse_expr lexbuf in
    if e = None then
        parse_err "generator body expected";
    Some (gen, opt_get e)

let prog lexbuf =
    tok_stack := [];
    bar_starts_expr := true;
    match parse_expr lexbuf with
    | Some (e) -> e
    | None -> raise (ImapFailure
                        (sprintf "failed to parse `%s' (parser rerutned None)"
                                !Globals.fname))

