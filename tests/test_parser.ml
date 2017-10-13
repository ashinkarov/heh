open OUnit
open Printf
open Storage
open Value
open Valueops
open Ast
open Globals

let parse_prog prg =
    let lexbuf = Lexing.from_string prg in
    fname := sprintf "prog: `%s'" prg;
    Parser.prog lexbuf

let test_parser _ =
    let prg = "f a.iv" in
    let e1 = parse_prog prg in
    let e2 = mk_eapply (mk_evar "f") (mk_esel (mk_evar "a") (mk_evar "iv")) in
    (sprintf "test sel priority: `%s'" prg) @? (Ast.cmp_ast_noloc e1 e2)

