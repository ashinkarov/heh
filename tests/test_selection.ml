open OUnit
open Printf
open Storage
open Value
open Valueops
open Eval
open Globals

let eval_prog prg =
    let lexbuf = Lexing.from_string prg in
    let e = Parser.prog Lexer.token lexbuf in
    let e = Traverse.app_to_hof e in
    Eval.eval (Storage.st_new ()) (Env.env_new ()) e

let test_empty_selection _ =
    let prog = "5.[]" in
    let st, p = eval_prog prog in
    assert_equal ~msg:(sprintf "empty selection: `%s'" prog)
                 (st_lookup st p) (mk_int_value 5);

    let prog = "false.[]" in
    let st, p = eval_prog prog in
    assert_equal ~msg:(sprintf "empty selection: `%s'" prog)
                 (st_lookup st p) (VFalse);

    let prog = "(\\x.2).[] 1" in
    let st, p = eval_prog prog in
    assert_equal ~msg:(sprintf "empty selection: `%s'" prog)
                 (st_lookup st p) (mk_int_value 2)

let test_expr_selection _ =
    let prog = "[1,2,3].(imap [1] { _(iv): 1)" in
    let st, p = eval_prog prog in
    assert_equal ~msg:(sprintf "select with imap: `%s'" prog)
                 (st_lookup st p) (mk_int_value 2);

    let prog = "[1,2,3].[reduce (\\x.\\y.x+y) 0 [1]]" in
    let st, p = eval_prog prog in
    assert_equal ~msg:(sprintf "select with reduce: `%s'" prog)
                 (st_lookup st p) (mk_int_value 2);

    let prog = "[1,2,3].(filter (\\x.x > 0) [0,1,0])" in
    let st, p = eval_prog prog in
    assert_equal ~msg:(sprintf "select with filter: `%s'" prog)
                 (st_lookup st p) (mk_int_value 2)

let test_letrec_selection _ =
    let prog = "[1,2,3].(letrec a = [1] in a)" in
    let st, p = eval_prog prog in
    assert_equal ~msg:(sprintf "select with letrec: `%s'" prog)
                 (st_lookup st p) (mk_int_value 2);

    let prog = "[[1,2],[3,4]]" ^
               ".(letrec a = imap [2] {[0] <= iv < [1]: 0, " ^
               "                       [1] <= iv < [2]: a.[0]+1 in a)" in
    let st, p = eval_prog prog in
    assert_equal ~msg:(sprintf "select with letrec: `%s'" prog)
                 (st_lookup st p) (mk_int_value 2)


let test_struct_selection _ =
    let prog = "(imap [] {_(iv): 5).[]" in
    let st, p = eval_prog prog in
    assert_equal ~msg:(sprintf "imap selection: `%s'" prog)
                 (st_lookup st p) (mk_int_value 5);

    let prog = "(imap [10] {_(iv): 5).[0]" in
    let st, p = eval_prog prog in
    assert_equal ~msg:(sprintf "imap selection: `%s'" prog)
                 (st_lookup st p) (mk_int_value 5);

    let prog = "(imap [omega] {_(iv): 5).[0]" in
    let st, p = eval_prog prog in
    assert_equal ~msg:(sprintf "imap selection: `%s'" prog)
                 (st_lookup st p) (mk_int_value 5);

    let prog = "(letrec a = imap [omega] {[0] <= iv < [1]: 0, " ^
               "                          [1] <= iv < [omega]: a.[0]+1 " ^
               " in a).[5]" in
    let st, p = eval_prog prog in
    assert_equal ~msg:(sprintf "rec imap selection: `%s'" prog)
                 (st_lookup st p) (mk_int_value 1);

    let prog = "(reduce (\\x.\\y.x+y) 0 [1,2,3]).[]" in
    let st, p = eval_prog prog in
    assert_equal ~msg:(sprintf "reduce selection: `%s'" prog)
                 (st_lookup st p) (mk_int_value 6);

    let prog = "(filter (\\x.x > 0) [1,2,3]).[0]" in
    let st, p = eval_prog prog in
    assert_equal ~msg:(sprintf "filter selection: `%s'" prog)
                 (st_lookup st p) (mk_int_value 1);

    let prog = "(filter (\\x.x > 0) imap [omega] {_(iv): iv.[0]).[5]" in
    let st, p = eval_prog prog in
    assert_equal ~msg:(sprintf "filter selection: `%s'" prog)
                 (st_lookup st p) (mk_int_value 6);


