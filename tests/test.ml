open OUnit
open Test_ordinals
open Test_storage
open Test_env
open Test_lexi_next
open Test_eval_reduce
open Test_value


let suite =
    "IMap Lang" >:::
    [
        "Ordinal testsuite" >:::
        [
            "ordinal-comparison" >:: test_ord_comparison;
            "ordinal-addition" >:: test_ord_addition;
            "ordinal-multiplication" >:: test_ord_mult;
            "ordinal-subtraction" >:: test_ord_sub;
            "ordinal-islimit" >:: test_ord_islimit;
            "ordinal-printing" >:: test_ord_print;
        ];
        "Storage testsuite" >:::
        [
            "storage-test" >:: test_storage
        ];
        "Env testsuite" >:::
        [
            "environment-test" >:: test_env
        ];
        "Value testsuite" >:::
        [
            "value constants" >:: test_value_const;
            "value arrays" >:: test_value_array;
        ];
        "Eval helpers" >:::
        [
            "lexi-next" >:: test_lexi_next
        ];
        "Eval progrs" >:::
        [
            "eval reducce" >:: test_eval_reduce
        ];
    ]

let _ =
run_test_tt_main suite
