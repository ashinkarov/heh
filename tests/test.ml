open OUnit
open Test_ordinals
open Test_storage
open Test_env


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
    ]

let _ =
run_test_tt_main suite
