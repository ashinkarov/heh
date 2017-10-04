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


{
open Lexing
open Ast


type token =
  | UNDERSCORE
  | TRUE
  | THEN
  | RSQUARE
  | RPAREN
  | PLUS
  | OMEGA
  | NE
  | MULT
  | MOD
  | MINUS
  | LT
  | LSQUARE
  | LPAREN
  | LETREC
  | LE
  | LBRACE
  | LAMBDA
  | ISLIM
  | INT of (int)
  | IN
  | IMAP
  | IF
  | ID of (string)
  | GT
  | GE
  | FALSE
  | EQ
  | EOF
  | ELSE
  | DOT
  | DIV
  | COMMA
  | COLON
  | BAR


let tok_to_str = function
  | UNDERSCORE -> "_"
  | TRUE -> "true"
  | THEN -> "then"
  | RSQUARE -> "]"
  | RPAREN -> ")"
  | PLUS -> "+"
  | OMEGA -> "ω"
  | NE -> "<>"
  | MULT -> "*"
  | MOD -> "%"
  | MINUS -> "-"
  | LT -> "<"
  | LSQUARE -> "["
  | LPAREN -> "("
  | LETREC -> "letrec"
  | LE -> "<="
  | LBRACE -> "{"
  | LAMBDA -> "λ"
  | ISLIM -> "islim"
  | INT (x) -> string_of_int x
  | IN -> "in"
  | IMAP -> "imap"
  | IF -> "if"
  | ID (x) -> x
  | GT -> ">"
  | GE -> ">="
  | FALSE -> "false"
  | EQ -> "="
  | EOF -> "EOF"
  | ELSE -> "else"
  | DOT -> "."
  | DIV -> "/"
  | COMMA -> ","
  | COLON -> ":"
  | BAR -> "|"

let is_op ?(no_relop=false) tok = match tok with
    | EQ
    | NE
    | LT
    | GT
    | GE
    | PLUS
    | MINUS
    | MULT
    | DIV
    | MOD  -> true
    | LE -> not no_relop
    | _ -> false

let op_to_binop tok = match tok with
    | PLUS  -> OpPlus
    | MINUS -> OpMinus
    | MULT  -> OpMult
    | DIV   -> OpDiv
    | MOD   -> OpMod
    | LT    -> OpLt
    | GT    -> OpGt
    | EQ    -> OpEq
    | NE    -> OpNe
    | GE    -> OpGe
    | LE    -> OpLe
    | _ -> raise (ImapFailure "op_to_binop: not a binary operation")

}


let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

let digit = ['0'-'9']
let integer = digit+
let alpha = ['A'-'Z' 'a'-'z']
let ident = (alpha | '_') (alpha | digit | '_')*
let comment = ';' [^ '\n']*

rule token = parse
  | white                               { token lexbuf }
  | comment                             { token lexbuf }
  | newline                             { new_line lexbuf; token lexbuf }
  | integer                             { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | "true"                              { TRUE }
  | "false"                             { FALSE }
  | "if"                                { IF }
  | "then"                              { THEN }
  | "else"                              { ELSE }
  | "letrec"                            { LETREC }
  | "in"                                { IN }
  | "omega"                             { OMEGA }
  | "ω"                                 { OMEGA }
  | "islim"                             { ISLIM }
  | "imap"                              { IMAP }
  | "λ"                                 { LAMBDA }
  | "\\"                                { LAMBDA }
  | "."                                 { DOT }
  | "|"                                 { BAR }
  | "+"                                 { PLUS }
  | "-"                                 { MINUS }
  | "*"                                 { MULT }
  | "/"                                 { DIV }
  | "%"                                 { MOD }
  | "="                                 { EQ }
  | ">"                                 { GT }
  | ">="                                { GE }
  | "<"                                 { LT }
  | "<="                                { LE }
  | "<>"                                { NE }
  | "["                                 { LSQUARE }
  | "]"                                 { RSQUARE }
  | "("                                 { LPAREN }
  | ")"                                 { RPAREN }
  | "{"                                 { LBRACE }
  | ":"                                 { COLON }
  | ","                                 { COMMA }
  | "_"                                 { UNDERSCORE }
  | ident as i                          { ID i }
  | eof                                 { EOF }
  | _                                   { raise (ImapFailure "Lexing error") }
