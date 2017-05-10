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
  | "w"                                 { OMEGA }
  | "islim"                             { ISLIM }
  | "\\"                                { LAMBDA }
  | "."                                 { DOT }
  | "|"                                 { BAR }
  | "+"                                 { PLUS }
  | "-"                                 { MINUS }
  | "*"                                 { MULT }
  | "/"                                 { DIV }
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
  | ident as i                          { ID i }
  | eof                                 { EOF }
  | _                                   { raise (ImapFailure "Lexing error") }
