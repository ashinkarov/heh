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
open Parser
open Lexing
open Ast

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
