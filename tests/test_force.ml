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
    fname := sprintf "prog: `%s'" prg;
    let e = Parser.prog lexbuf in
    let e = Traverse.app_to_hof e in
    Eval.eval (Storage.st_new ()) (Env.env_new ()) e

let test_force _ =
    let prg = "letrec p = 1 in letrec x = [p,p] in p" in
    let st, p = eval_prog prg in
    assert_equal ~msg:(sprintf "forcing a number: `%s'" prg)
                 (st_lookup st p) (mk_int_value 1);

    let prg = "letrec p = true in letrec x = [p,p] in p" in
    let st, p = eval_prog prg in
    assert_equal ~msg:(sprintf "forcing a number: `%s'" prg)
                 (st_lookup st p) (mk_true_value);

    let prg = "letrec p = \\x.x+1 in letrec x = [p,p] in p" in
    let st, p = eval_prog prg in
    let st', p' = eval_prog "\\x.x+1" in
    let x, v, _ = value_closure_to_triple (st_lookup st p) in
    let x', v', _ = value_closure_to_triple (st_lookup st' p') in
    assert_equal ~msg:(sprintf "forcing a function: `%s'" prg)
                 (x, v) (x', v');

    let prg = "letrec p = [1,2,3] in letrec x = [p,p] in p" in
    let st, p = eval_prog prg in
    let st', p' = eval_prog "[1,2,3]" in
    assert_equal ~msg:(sprintf "forcing a vector: `%s'" prg)
                 (st_lookup st p) (st_lookup st' p')

