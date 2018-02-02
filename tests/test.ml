open OUnit
open Test_ordinals
open Test_storage
open Test_parser
open Test_env
open Test_value
open Test_lexi_next
open Test_eval_reduce
open Test_eval_imap
open Test_selection
open Test_array
open Test_shape
open Test_force



let suite =
    "Heh language" >:::
    [
        "Ordinal testsuite" >:::
        [
            "ordinal-comparison" >:: test_ord_comparison;
            "ordinal-addition" >:: test_ord_addition;
            "ordinal-multiplication" >:: test_ord_mult;
            "ordinal-divmod" >:: test_ord_divmod;
            "ordinal-subtraction" >:: test_ord_sub;
            "ordinal-islimit" >:: test_ord_islimit;
            "ordinal-printing" >:: test_ord_print;
        ];
        "Storage testsuite" >:::
        [
            "storage-test" >:: test_storage;
            "free-variables" >:: test_free_vars;
            "reference-counting" >:: test_rc
        ];
        "Parser testsuite" >:::
        [
            "parser-tests" >:: test_parser
        ];
        "Env testsuite" >:::
        [
            "environment-test" >:: test_env
        ];
        "Value testsuite" >:::
        [
            "value-constants" >:: test_value_const;
            "value-arrays" >:: test_value_array;
        ];
        "Eval helpers" >:::
        [
            "lexi-next" >:: test_lexi_next
        ];
        (*"Eval progrs" >:::
        [
            "eval-reduce" >:: test_eval_reduce;
            "eval-imap" >:: test_eval_imap;
            "test-empty-selection" >:: test_empty_selection;
            "test-expr-selection" >:: test_expr_selection;
            "test-letrec-selection" >:: test_letrec_selection;
            "test-struct-selection" >:: test_struct_selection;
            "test-imm-array" >:: test_imm_array;
            "test-shape" >:: test_shape;
            "test-force" >:: test_force;
        ];*)
    ]

let _ =
run_test_tt_main suite
