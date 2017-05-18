open OUnit
open Ordinals


let lt = -1
let eq = 0
let gt = 1

let test_ord_comparison _=
    assert_equal ~msg:"ordinal comparison 1 < 3"
                 (compare one (int_to_ord  3))  lt;
    assert_equal ~msg:"ordinal comparison w > 1"
                 (compare omega (int_to_ord  1)) gt;
    assert_equal ~msg:"ordinal comparison w+1 > w"
                 (compare [{exp = one; coeff = 1}; {exp = []; coeff = 1}] omega) gt;
    assert_equal ~msg:"ordinal comparison w*2 + 1 < w^2"
                 (compare [{exp = one; coeff = 1}; {exp = []; coeff = 1}]
                          [{exp = one; coeff = 2} ]) lt;
    assert_equal ~msg:"ordinal comparison w^w + 1 > w"
                 (compare [{exp = omega; coeff = 1}; {exp = []; coeff = 1}]
                          omega)
                 gt;
    assert_equal ~msg:"ordinal comparison w > 0"
                 (compare omega zero) gt;
    assert_equal ~msg:"ordinal comparison 0 < w"
                 (compare zero omega) lt


let test_ord_addition _ =
    assert_equal ~msg:"ordinal addition 1 + 1"
                 (add one one) (int_to_ord 2);
    assert_equal ~msg:"ordinal addition 0 + w"
                 (add zero omega) omega;
    assert_equal ~msg:"ordinal addition w + 0"
                 (add omega zero) omega;
    assert_equal ~msg:"ordinal addition w + 1"
                 (add omega one) [{exp = one; coeff = 1}; {exp = []; coeff = 1}];
    assert_equal ~msg:"ordinal addition 1 + w"
                 (add one omega) omega;
    assert_equal ~msg:"ordinal addition w + w"
                 (add omega omega) [{exp = one; coeff = 2}];
    assert_equal ~msg:"ordinal addition w + w + 1"
                 (add (add omega omega) one)
                 [{exp = one; coeff = 2}; {exp = []; coeff = 1}]


let test_ord_sub _ =
    assert_equal ~msg:"ordinal subtraction 1 - 0"
                 (sub one zero) one;
    assert_equal ~msg:"ordinal subtraction w - 0"
                 (sub omega zero) omega;
    assert_equal ~msg:"ordinal subtraction 1 - 1"
                 (sub one one) zero;
    assert_equal ~msg:"ordinal subtraction w - 1"
                 (sub omega one) omega;
    assert_equal ~msg:"ordinal subtraction w - w"
                 (sub omega omega) zero;
    assert_equal ~msg:"ordinal subtraction (w + w) - 1"
                 (sub (add omega omega) one) [{exp = one; coeff = 2}];;
    assert_equal ~msg:"ordinal subtraction (w + 1) - 1"
                 (sub (add omega one) one)
                 [{exp = one; coeff = 1}; {exp = []; coeff = 1}]


let test_ord_mult _ =
    assert_equal ~msg:"1 * 1"
                 (mult one one) one;
    assert_equal ~msg:"w * 1"
                 (mult omega one) omega;
    assert_equal ~msg:"w * w"
                 (mult omega omega) [{exp = [{exp = []; coeff = 2}]; coeff = 1}];
    assert_equal ~msg:"(w+1) * 2"
                 (mult (add omega one) [{exp = []; coeff = 2}])
                 [{exp = one; coeff = 2}; {exp = []; coeff = 1}];
    assert_equal ~msg:"(w*w+1) * 2"
                 (mult (add (mult omega omega) one) [{exp = []; coeff = 2}])
                 [{exp = [{exp = []; coeff = 2}]; coeff = 2}; {exp = []; coeff = 1}]



let test_ord_print _ =
    assert_equal ~msg:"printing ordinal w"
                 (ord_to_str [{exp = [{exp = []; coeff = 1}]; coeff = 1}])
                 "ω";
    assert_equal ~msg:"printing ordinal w"
                 (ord_to_str omega)
                 "ω";
    assert_equal ~msg:"printing ordinal w"
                 (ord_to_str [{exp = one; coeff = 1}])
                 "ω";
    assert_equal ~msg:"printing ordinal 44"
                 (ord_to_str [{exp = zero; coeff = 44}])
                 "44";
    assert_equal ~msg:"printing ordinal w^w"
                 (ord_to_str [{exp = omega; coeff = 1}])
                 "ω^(ω)";
    assert_equal ~msg:"printing ordinal w^w + w*2"
                 (ord_to_str [{exp = omega; coeff = 1};{exp = one; coeff = 2}])
                 "ω^(ω) + ω*2";
    assert_equal ~msg:"printing ordinal w^w + 33"
                 (ord_to_str [{exp = omega; coeff = 1};{exp = zero; coeff = 33}])
                 "ω^(ω) + 33"

let test_ord_islimit _ =
    assert_equal ~msg:"islim 22"
                 (ord_is_lim (int_to_ord 22)) false;
    assert_equal ~msg:"islim w"
                 (ord_is_lim omega) true;
    assert_equal ~msg:"islim w+1"
                 (ord_is_lim (add omega one)) false;
    let o = add (mult omega omega)
                (mult omega (int_to_ord 3)) in
    assert_equal ~msg:"islim w^2+w*3"
                 (ord_is_lim o) true


