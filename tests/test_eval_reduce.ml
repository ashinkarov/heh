open OUnit
open Printf
open Storage
open Value
open Valueops
open Eval

let eval_prog prg =
    let lexbuf = Lexing.from_string prg in
    Globals.fname := sprintf "prog `%s'" prg;
    let e = Parser.prog lexbuf in
    let e = Traverse.app_to_hof e in
    Eval.eval (Storage.st_new ()) (Env.env_new ()) e



let test_eval_reduce _ =
    let prg01 =
        "letrec sum = \\x.\\y.x + y in " ^
        "reduce sum 0 [1,2,3]"
    in
    let st, p = eval_prog prg01 in
    assert_equal ~msg:(sprintf "test reduce `%s'" prg01)
                 (st_lookup st p) (mk_int_value 6);

    let prg02 =
        "letrec sum = \\x.\\y.x + y in " ^
        "letrec a = imap [10]|[] { [0] <= iv < [10]: iv . [0] in " ^
        "reduce sum 0 a"
    in

    let st, p = eval_prog prg02 in
    assert_equal ~msg:(sprintf "test reduce `%s'" prg02)
                 (st_lookup st p) (mk_int_value 45);


