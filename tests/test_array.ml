open OUnit
open Printf
open Storage
open Valueops

open Test_common

let test_imm_array _ =
    let prg = "[]" in
    let st, p = eval_prog prg in
    assert_equal ~msg:(sprintf "immutable array: `%s'" prg)
                 (st_lookup st p) (mk_empty_vector ());

    let prg = "[[]]" in
    let st, p = eval_prog prg in
    assert_equal ~msg:(sprintf "immutable array: `%s'" prg)
                 (st_lookup st p) (mk_array_value [mk_int_value 1; mk_int_value 0] []);

    let prg = "[\\x.x].[0] 2" in
    let st, p = eval_prog prg in
    assert_equal ~msg:(sprintf "immutable array: `%s'" prg)
                 (st_lookup st p) (mk_int_value 2);

    let prg = "[imap [1] { _(iv): 2].[0,0]" in
    let st, p = eval_prog prg in
    assert_equal ~msg:(sprintf "immutable array: `%s'" prg)
                 (st_lookup st p) (mk_int_value 2);

    let prg = "[letrec x = 5 in x].[0]" in
    let st, p = eval_prog prg in
    assert_equal ~msg:(sprintf "immutable array: `%s'" prg)
                 (st_lookup st p) (mk_int_value 5);

    let prg = "[filter (\\x.x > 1) [1,2,1]].[0,0]" in
    let st, p = eval_prog prg in
    assert_equal ~msg:(sprintf "immutable array: `%s'" prg)
                 (st_lookup st p) (mk_int_value 2);

    let prg = "[reduce (\\x.\\y.x+y) 0 5].[0]" in
    let st, p = eval_prog prg in
    assert_equal ~msg:(sprintf "immutable array: `%s'" prg)
                 (st_lookup st p) (mk_int_value 5)






