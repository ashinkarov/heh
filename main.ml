
open Printf;;
open Ast;;
open Traverse;;


let load file =
  let lexbuf = Lexing.from_channel file in
  let e = Parser.prog Lexer.token lexbuf in
  printf "%s" (expr_to_str (app_to_hof e))
;;

load stdin;;
