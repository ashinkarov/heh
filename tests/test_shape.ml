open OUnit
open Printf
open Storage
open Value
open Valueops
open Eval
open Globals
open Ordinals

let eval_prog prg =
    let lexbuf = Lexing.from_string prg in
    let e = Parser.prog Lexer.token lexbuf in
    let e = Traverse.app_to_hof e in
    Eval.eval (Storage.st_new ()) (Env.env_new ()) e

let test_shape _ =
    let prg = "|[]|" in
    let st, p = eval_prog prg in
    assert_equal ~msg:(sprintf "shape of: `%s'" prg)
                 (st_lookup st p) (mk_array_value [VNum one] [VNum zero]);

    let prg = "|1|" in
    let st, p = eval_prog prg in
    assert_equal ~msg:(sprintf "shape of: `%s'" prg)
                 (st_lookup st p) (mk_array_value [VNum zero] []);

    let prg = "|false|" in
    let st, p = eval_prog prg in
    assert_equal ~msg:(sprintf "shape of: `%s'" prg)
                 (st_lookup st p) (mk_array_value [VNum zero] []);

    let prg = "|(\\x.x)|" in
    let st, p = eval_prog prg in
    assert_equal ~msg:(sprintf "shape of: `%s'" prg)
                 (st_lookup st p) (mk_array_value [VNum zero] []);

    let prg = "|(imap [0] { [0] <= iv < [0]: 0)|" in
    let st, p = eval_prog prg in
    assert_equal ~msg:(sprintf "shape of: `%s'" prg)
                 (st_lookup st p) (mk_array_value [VNum one] [VNum zero]);

    let prg = "|(imap [] { [] <= iv < []: 5)|" in
    let st, p = eval_prog prg in
    assert_equal ~msg:(sprintf "shape of: `%s'" prg)
                 (st_lookup st p) (mk_array_value [VNum zero] []);

    let prg = "|(imap [omega] {_(iv): 1)|" in
    let st, p = eval_prog prg in
    assert_equal ~msg:(sprintf "shape of: `%s'" prg)
                 (st_lookup st p) (mk_array_value [VNum one] [VNum omega]);

    let prg = "|(reduce (\\x.\\y.x+y) 0 [1,2,3])|" in
    let st, p = eval_prog prg in
    assert_equal ~msg:(sprintf "shape of: `%s'" prg)
                 (st_lookup st p) (mk_array_value [VNum zero] []);

    let prg = "|(filter (\\x.x > 1) [1,2,3])|" in
    let st, p = eval_prog prg in
    assert_equal ~msg:(sprintf "shape of: `%s'" prg)
                 (st_lookup st p) (mk_array_value [VNum one] [mk_int_value 2]);

    let prg = "|(filter (\\x.x > 1) (imap [omega+3] {_(iv): 1))|" in
    let st, p = eval_prog prg in
    assert_equal ~msg:(sprintf "shape of: `%s'" prg)
                 (st_lookup st p) (mk_array_value [VNum one] [VNum omega]);

    (* NOTE that despite we are defining the imap that diverges,
            we can still evaluate its shape.  *)
    let prg = "|(letrec a = imap [omega] {_(iv): a.iv in a)|" in
    let st, p = eval_prog prg in
    assert_equal ~msg:(sprintf "shape of: `%s'" prg)
                 (st_lookup st p) (mk_array_value [VNum one] [VNum omega])
