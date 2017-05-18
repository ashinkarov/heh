open OUnit
open Ast
open Env



let test_env () =
    let e = env_new () in
    let e = env_add e "x" "p1" in
    assert_equal ~msg:"environment lookup of `x'"
                 (env_lookup e "x") "p1";
    let e = env_add e "x" "p2" in
    let try_lookup () =
        env_lookup e "y" in
    assert_raises (EnvFailure "lookup of variable `y' failed") try_lookup;
    assert_equal ~msg:"environment size should be 2"
                 ( List.length e) 2
