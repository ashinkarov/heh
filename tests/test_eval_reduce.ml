open OUnit
open Printf
open Storage
open Value
open Valueops

open Test_common


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


