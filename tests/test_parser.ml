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
    let e = parse_prog prg in
    assert_equal ~msg:(sprintf "test sel priority: `%s'" prg)
                 (e)  (EApply (EVar "f", ESel (EVar "a", EVar "iv")))

