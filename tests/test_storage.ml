open OUnit
open Ast
open Ordinals
open Storage


let test_storage _ =
    let s = st_new () in
    let s = st_add s "p1" (VNum (int_to_ord 1)) in
    let s = st_add s "p2" (VNum (int_to_ord 2)) in
    let s = st_update s "p1" (VNum (int_to_ord 42)) in
    assert_equal ~msg:"storage lookup p1"
                 (st_lookup s "p1") (VNum (int_to_ord 42));
    let try_add () =
        st_add s "p1" (VNum (int_to_ord 10)) in
    assert_raises (StorageFailure
                   "Attempt to add the pointer `p1' which already exists in the storage")
                  try_add;
    let s = st_remove s "p1" in
    let s = st_remove s "p2" in
    let try_remove () =
         st_remove s "p3" in
    assert_raises (StorageFailure
                   "Attempt to remove the pointer `p3' which does not exist in the storage")
                  try_remove;
    let try_update () =
        st_update s "p1" (VNum (int_to_ord 22)) in
    assert_raises (StorageFailure
                   "Attempt to update the pointer `p1' which does not exist in the storage")
                  try_update;
    assert_equal ~msg:"storage length expected to be 0"
                 (Hashtbl.length s) 0




