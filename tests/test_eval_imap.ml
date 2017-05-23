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



let test_eval_imap _ =
    let prg01 =
        "imap [0]|[] { [0] <= iv < [0]: 10 "
    in
    let st, p = eval_prog prg01 in
    let v = st_lookup st p in
    assert_equal ~msg:"`%s' evaluates to VImap"
                 (value_is_imap v) (true);
    let _, _, parts, _ = value_imap_to_tuple v in
    assert_equal ~msg:(sprintf "no partitions in empty imap `%s'" prg01)
                 (List.length parts) (0);

    (* Regular test.  *)
    let prg02 =
        "letrec a = imap [10]|[] { [0] <= iv < [10]: iv [0] in " ^
        "a [5]"
    in
    let st, p = eval_prog prg02 in
    assert_equal ~msg:(sprintf "select idx [5] from `%s'" prg02)
                 (st_lookup st p) (mk_int_value 5);


    (* Out of bound access.  *)
    let try_out_of_bound _ =
        let prg03 =
            "letrec a = imap [10]|[] { [0] <= iv < [10]: iv [0] in " ^
            "a [10]"
        in
        eval_prog prg03
    in
    assert_raises (EvalFailure
                   "out of bound access in `((a) ([10]))' selection")
                  try_out_of_bound;

    (* Partition out of bounds.  *)
    let try_partition_out_of_bound _ =
        eval_prog "imap [10]|[] { [0] <= iv < [100]: iv [0] "

    in
    assert_raises (EvalFailure
                   "partition ([0], [100]) is not within ([0], [10])")
                  try_partition_out_of_bound;

    (* Does not form partitioning.  *)
    let try_poor_partitioning _ =
        eval_prog ("imap [10]|[] { [0] <= iv < [5]: 1, " ^
                   "               [6] <= iv < [10]: 2 ")

    in
    let err_msg = "partitions of " ^
                  "`imap [10]|[] { [0] <= iv < [5]: (1), [6] <= iv < [10]: (2)' " ^
                  "do not fill the specified imap range ([0], [10])" in
    assert_raises (EvalFailure err_msg)
                  try_poor_partitioning;

    (* Make sure that constant imap can be used in selection.  *)
    let prg04 = "[44] (imap [1] {_(iv): 0)" in
    let st, p = eval_prog prg04 in
    assert_equal ~msg:(sprintf "select with imap as index `%s'" prg04)
                 (st_lookup st p) (mk_int_value 44);


    (* Make sure that imap defining functions works correctly.  *)
    let prg05 = "((imap [5] {_(iv): \\x.x) [0]) 42" in
    let st, p = eval_prog prg05 in
    assert_equal ~msg:(sprintf "imap defining array of functions `%s'" prg05)
                 (st_lookup st p) (mk_int_value 42)



