(*
 * Copyright (c) 2017-2018, Artem Shinkarov <artyom.shinkaroff@gmail.com>
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
    let { loc = shp_loc } = shp in
    let mul_shp_zero =
        mk_elambda "__x"
                   (mk_eimap (mk_eunary OpShape (mk_evar "__x"))
                             (mk_earray [])
                             [(
                                 (* generator: [0] <= iv |__x| *)
                                 (mk_earray [mk_enum zero],
                                  "__iv",
                                  mk_eunary OpShape (mk_evar "__x")),

                                 (* body: 0 * __x.iv *)
                                 mk_ebinop OpMult
                                           (mk_enum zero)
                                           (mk_esel (mk_evar "__x") (mk_evar "__iv")))])
                   ~loc:shp_loc
    in
        (mk_eapply mul_shp_zero shp, x, shp)


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

let parse_err_loc loc msg =
    raise (ImapFailure (sprintf "%s: error: %s" (Loc.to_str loc) msg))

let get_loc lexbuf =
    (* XXX we can grab the end of the token as well, in case we want to. *)
    let open Lexing in
    let loc_s = lexeme_start_p lexbuf in
    let l = Loc.mk loc_s.pos_fname loc_s.pos_lnum
                   (loc_s.pos_cnum - loc_s.pos_bol + 1) in
    l

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

let peek_loc lexbuf =
    Tok.get_loc (peek_token lexbuf)

(* FIXME add 'msg' parameter to alter the error message.  *)
let expect_id lexbuf =
    let t = get_token lexbuf in
    match Tok.get_tok t with
    | ID (x) -> t
    | _ -> parse_err_loc (Tok.get_loc t)
           @@ sprintf "expected identifier, found `%s' instead"
                      (Tok.to_str t)

(* FIXME add 'msg' parameter to alter the error message.  *)
let expect_tok lexbuf t_exp =
    let t = get_token lexbuf in
    if Tok.get_tok t <> t_exp then
        parse_err_loc (Tok.get_loc t)
        @@ sprintf "expected token `%s', found `%s' instead"
                   (Lexer.tok_to_str t_exp)
                   (Tok.to_str t);
    t

(* Parse NON-EMPTY comma separated list of elements that
   can be parsed by `parse_fun' function.  *)
let rec parse_generic_list ?(msg="expression expected") lexbuf parse_fun =
    let e = parse_fun lexbuf in
    if e = None then
        parse_err_loc (peek_loc lexbuf) msg;
    let t = peek_token lexbuf in
    if Tok.get_tok t = COMMA then
        let _ = get_token lexbuf in
        let l = parse_generic_list ~msg:msg lexbuf parse_fun in
        e :: l
    else
        [e]

let rec parse_primary lexbuf =
    let t = get_token lexbuf in
    let l = Tok.get_loc t in
    match Tok.get_tok t with
    | TRUE ->   Some (mk_etrue () ~loc:l)
    | FALSE ->  Some (mk_efalse () ~loc:l)
    | ID x ->   Some (mk_evar x ~loc:l)
    | INT n ->  Some (mk_enum (int_to_ord n) ~loc:l)
    | OMEGA ->  Some (mk_enum (omega) ~loc:l)
    | BAR ->    if !bar_starts_expr then begin
                    bar_starts_expr := false;
                    let e = parse_expr lexbuf in
                    if e = None then
                        parse_err_loc (peek_loc lexbuf) "expression expected after |";
                    let t = peek_token lexbuf in
                    if Tok.get_tok t <> BAR then
                        parse_err_loc (Tok.get_loc t)
                                      (sprintf "missing closing `|' to match the one at location %s"
                                                (Loc.to_str l));
                    let _ = get_token lexbuf in
                    bar_starts_expr := true;
                    Some (mk_eunary OpShape (opt_get e) ~loc:l)
                end else begin
                    unget_tok t;
                    None
                end
    | LSQUARE ->
                let bar_state = !bar_starts_expr in
                bar_starts_expr := true;

                let lst = if Tok.get_tok (peek_token lexbuf) = RSQUARE then
                              []
                          else
                              parse_generic_list lexbuf parse_expr
                              ~msg:"array element definition is missing"
                in
                let _ = expect_tok lexbuf RSQUARE in
                bar_starts_expr := bar_state;
                Some (mk_earray (List.map opt_get lst) ~loc:l)

    | LPAREN ->
                let bar_state = !bar_starts_expr in
                bar_starts_expr := true;
                let e = parse_expr lexbuf in
                if e = None then
                    parse_err_loc (peek_loc lexbuf) "empty expression found";
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
            parse_err_loc (peek_loc lexbuf) "expected index specification in selection";
        e := Some (mk_esel (opt_get !e) (opt_get e1))
    done;
    !e

and parse_unary lexbuf =
    let t = peek_token lexbuf in
    let l = Tok.get_loc t in
    match Tok.get_tok t with
    | ISLIM ->
            let _ = get_token lexbuf in
            let e = parse_unary lexbuf in
            if e = None then
                parse_err_loc (peek_loc lexbuf) "expected expression after `islim' operator";
            Some (mk_eunary OpIsLim (opt_get e) ~loc:l)
    | _ ->
            parse_postfix lexbuf

and parse_app ?(e1=None) lexbuf  =
    match e1, parse_unary lexbuf with
    | None, Some e2 -> parse_app lexbuf ~e1:(Some e2)
    | Some e1, Some e2 -> parse_app lexbuf ~e1:(Some (mk_eapply e1 e2))
    | _, None -> e1

and parse_binop ?(no_relop=false) lexbuf =
    let rec resolve_stack s prec =
        let e1, op1, p1 = Stack.pop s in

        if prec <= p1 then begin
            let e2, op2, p2 = Stack.pop s in
            let e = mk_ebinop (op_to_binop op1) (opt_get e2) (opt_get e1) in
            Stack.push (Some (e), op2, p2) s;
            resolve_stack s prec
        end else begin
            Stack.push (e1, op1, p1) s
        end
    in

    let e1 = parse_app lexbuf in
    if e1 = None then
        e1
    else
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
                parse_err_loc (peek_loc lexbuf)  @@ sprintf "expression expected after %s" (Tok.to_str t);
            Stack.push (e2, Tok.get_tok t, (op_prec @@ Tok.get_tok t)) s;
        done;
        resolve_stack s 0;
        let e, op, prec = Stack.pop s in
        e


and parse_expr lexbuf =
    parse_binop lexbuf

and parse_lambda lexbuf =
    let t = get_token lexbuf in
    let l = Tok.get_loc t in
    assert (LAMBDA = Tok.get_tok t);
    let t = expect_id lexbuf in
    let _ = expect_tok lexbuf DOT in
    let e = parse_expr lexbuf in
    if e = None then
        parse_err_loc (peek_loc lexbuf) "expression expected after `.'";
    Some (mk_elambda (Tok.to_str t) (opt_get e) ~loc:l)

and parse_cond lexbuf =
    let t = get_token lexbuf in
    let l = Tok.get_loc t in
    assert (IF = Tok.get_tok t);
    let bar_state = !bar_starts_expr in
    bar_starts_expr := true;
    let e1 = parse_expr lexbuf in
    if e1 = None then
        parse_err_loc (peek_loc lexbuf) "expression expected after `if'";
    let _ = expect_tok lexbuf THEN in
    let e2 = parse_expr lexbuf in
    if e2 = None then
        parse_err_loc (peek_loc lexbuf) "expression expected after `then'";
    let _ = expect_tok lexbuf ELSE in
    bar_starts_expr := bar_state;
    let e3 = parse_expr lexbuf in
    if e3 = None then
        parse_err_loc (peek_loc lexbuf) "expression expected after `else'";
    Some (mk_econd (opt_get e1) (opt_get e2) (opt_get e3) ~loc:l)

and parse_letrec lexbuf =
    let t = get_token lexbuf in
    let l = Tok.get_loc t in
    assert (LETREC = Tok.get_tok t);
    let t = expect_id lexbuf in
    let _ = expect_tok lexbuf EQ in
    let bar_state = !bar_starts_expr in
    bar_starts_expr := true;
    let e1 = parse_expr lexbuf in
    bar_starts_expr := bar_state;
    if e1 = None then
        parse_err_loc (peek_loc lexbuf) "expression expected after `=' and before `in'";
    let _ = expect_tok lexbuf IN in
    let e2 = parse_expr lexbuf in
    if e2 = None then
        parse_err_loc (peek_loc lexbuf) "expression expected after `in'";
    Some (mk_eletrec (Tok.to_str t) (opt_get e1) (opt_get e2) ~loc:l)

and parse_imap lexbuf =
    let t = get_token lexbuf in
    let l = Tok.get_loc t in
    assert (IMAP = Tok.get_tok t);
    let bar_state = !bar_starts_expr in
    bar_starts_expr := (Tok.get_tok @@ peek_token lexbuf) = BAR;
    let sh1 = parse_expr lexbuf in
    if sh1 = None then
        parse_err_loc (peek_loc lexbuf) "expression expected after `imap'";
    let sh2 = if BAR = Tok.get_tok @@ peek_token lexbuf then begin
                  bar_starts_expr := true;
                  let _ = get_token lexbuf in
                  let sh2 = parse_expr lexbuf in
                  if sh2 = None then
                      parse_err_loc (peek_loc lexbuf) "cell shape specification expected";
                  sh2
              end else
                  Some (mk_earray []) in
    let _ = expect_tok lexbuf LBRACE in
    bar_starts_expr := bar_state;
    let lst = parse_generic_list lexbuf parse_gen
                                 ~msg:"generator expected" in
    let gl = List.map (fun x ->
                       match x with
                       | Some (FullGen (lb, x, ub), e) ->
                               ((lb, x, ub), e)
                       | Some (DefGen (x), e) ->
                               (* construct gen (out_shp * 0) <= x < out_shp *)
                               (mk_full_gen (opt_get sh1) x, e)
                       | _ -> raise (ImapFailure "error in parser function `parse_gen'"))
                       lst
             in
    Some (mk_eimap (opt_get sh1) (opt_get sh2) gl ~loc:l)

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
                      parse_err_loc (peek_loc lexbuf) "lower bound expression expected";
                  let _ = expect_tok lexbuf LE in
                  let iv = expect_id lexbuf in
                  let _ = expect_tok lexbuf LT in
                  let ub = parse_binop lexbuf in
                  if ub = None then
                      parse_err_loc (peek_loc lexbuf) "upper bound expression expected";
                  FullGen ((opt_get lb), (Tok.to_str iv), (opt_get ub))
              in
    let _ = expect_tok lexbuf COLON in
    let e = parse_expr lexbuf in
    if e = None then
        parse_err_loc (peek_loc lexbuf) "generator body expected";
    Some (gen, opt_get e)

let prog lexbuf =
    tok_stack := [];
    bar_starts_expr := true;
    match parse_expr lexbuf with
    | Some (e) -> e
    | None -> raise (ImapFailure
                        (sprintf "failed to parse `%s' (parser rerutned None)"
                                !Globals.fname))

