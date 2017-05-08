
open Printf;;
open Ast;;

let load file =
  let lexbuf = Lexing.from_channel file in
  let file = Parser.prog Lexer.token lexbuf in
  match file with
  | ETrue -> printf "value: true"
  | EFalse -> printf "value: false"
  | ENum x -> printf "number"
  | EBinOp (_, x, y) -> printf "binop"
  | _ -> raise (ImapFailure "invalid expression type")
;;

load stdin;;
