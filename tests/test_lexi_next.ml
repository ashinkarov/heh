open OUnit
open Ast
open Value
open Eval

let vv = List.map (fun x -> Valueops.mk_int_value x)

let test_lexi_next _ =
    let lb = vv [0;0] in
    let ub = vv [3;3] in

    assert_equal ~msg:"test lexi_next [] [] []"
                 (lexi_next (Nxt (vv [])) [] []) (Done);

    assert_equal ~msg:"test lexi_next [0] [0] [1]"
                 (lexi_next (Nxt (vv [0])) (vv [0]) (vv [1])) (Done);

    assert_equal ~msg:"test lexi_next [0;0] [0;0] [3;3]"
                 (lexi_next (Nxt (vv [0;0])) lb ub) (Nxt (vv [0;1]));

    assert_equal ~msg:"test lexi_next [0;2] [0;0] [3;3]"
                 (lexi_next (Nxt (vv [0;2])) lb ub) (Nxt (vv [1;0]));

    assert_equal ~msg:"test lexi_next [2;1] [0;0] [3;3]"
                 (lexi_next (Nxt (vv [2;1])) lb ub) (Nxt (vv [2;2]));

    assert_equal ~msg:"test lexi_next [9] [0] [10]"
                 (lexi_next (Nxt (vv [9])) (vv [0]) (vv [10])) (Done)
