open OUnit
open Printf
open Storage
open Valueops
open Ordinals

open Test_common

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
    let x, e, _ = value_closure_to_triple (st_lookup st p) in
    let x', e', _ = value_closure_to_triple (st_lookup st' p') in
    (* FIXME we may want to update most of the tests to use @? *)
    (sprintf "forcing a function: `%s'" prg) @? (x = x' && Ast.cmp_ast_noloc e e');

    let prg = "letrec p = [1,2,3] in letrec x = [p,p] in p" in
    let st, p = eval_prog prg in
    let st', p' = eval_prog "[1,2,3]" in
    assert_equal ~msg:(sprintf "forcing a vector: `%s'" prg)
                 (st_lookup st p) (st_lookup st' p')

