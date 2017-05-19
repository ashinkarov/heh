open OUnit
open Ordinals
open Value
open Valueops

let vv = List.map (fun x -> Valueops.mk_int_value x)

let test_value_const _ =
    assert_equal ~msg:"mk_false" (mk_false_value) (VFalse);
    assert_equal ~msg:"mk_true" (mk_true_value) (VTrue);
    assert_equal ~msg:"mk_int 0"
                 (mk_int_value 0) (VNum (zero));
    assert_equal ~msg:"mk_int 42"
                 (mk_int_value 42) (VNum (int_to_ord 42));
    assert_equal ~msg:"mk_ord 0"
                 (mk_ord_value zero) (VNum (zero))


let test_value_array _ =
    assert_equal ~msg:"empty array of shape [0]"
                 (mk_array_value (vv [0]) (vv [])) (VArray (vv [0], vv []));
    assert_equal ~msg:"empty array of shape [0;4;4]"
                 (mk_array_value (vv [0;4;4]) (vv [])) (VArray (vv [0;4;4], vv []));
    assert_equal ~msg:"empty array of shape [0;omega]"
                 (mk_array_value [VNum (zero); VNum (omega)] (vv []))
                 (VArray ([VNum zero; VNum omega], vv []));


    let try_non_number_shape () =
        mk_array_value [VFalse] []
    in
    assert_raises (ValueFailure
                   "mk_array: invalid shape vector [vfalse]")
                  try_non_number_shape;

    let try_omega_shape () =
        mk_array_value [VNum (omega)] []
    in
    assert_raises (ValueFailure
                   "mk_array: shape [ω] suggests that arrray will have more than omega elements")
                  try_omega_shape;

    let try_wrong_data_size () =
        mk_array_value (vv [3;3]) (vv [1;2;3])
    in
    assert_raises (ValueFailure
                   "mk_array: shape [3, 3] does not match data [1, 2, 3]")
                  try_wrong_data_size;

