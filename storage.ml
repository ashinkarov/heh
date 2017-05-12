open Ast
open Ordinals

exception StorageFailure of string

type storage = (string, Ast.value) Hashtbl.t
;;

let st_new: unit -> storage = fun () ->
    Hashtbl.create 100
;;

(* A helper function to do debugging *)
let find_and_raise st p expected msg =
    let exists = try Hashtbl.find st p; true with Not_found -> false in
    if expected <> exists then
        raise (StorageFailure msg)
;;


let st_add st p v =
    (* This is for debugging purposes.  *)
    find_and_raise
        st p false
        (Printf.sprintf "Attempt to add the pointer `%s' which already exists in the storage" p);
    Hashtbl.add st p v;
    st
;;

let st_remove st p =
    (* This is for debugging purposes.  *)
    find_and_raise
        st p true
        (Printf.sprintf "Attempt to remove the pointer `%s' which does not exist in the storage" p);
    Hashtbl.remove st p;
    st
;;


let st_update st p v =
    (* This is for debugging purposes.  *)
    find_and_raise
        st p true
        (Printf.sprintf "Attempt to update the pointer `%s' which does not exist in the storage" p);
    Hashtbl.replace st p v;
    st
;;

let st_lookup st p =
    find_and_raise
        st p true
        (Printf.sprintf "Attempt to lookup the pointer `%s' which does not exist in the storage" p);
    Hashtbl.find st p
;;


let st_to_str st =
    Hashtbl.fold (fun k v tail_s ->
                  Printf.sprintf
                    "%s |-> %s%s"
                    k
                    (Ast.value_to_str v)
                    (if tail_s = "" then "" else ", ")) st ""
;;



let test_storage () =
    let s = st_new () in
    let s = st_add s "p1" (VNum (int_to_ord 1)) in
    let s = st_add s "p2" (VNum (int_to_ord 2)) in
    let s = st_update s "p1" (VNum (int_to_ord 42)) in
    let s = match st_lookup s "p1" with
            | VNum ([{exp = []; coeff = 42}]) -> s
            | _ -> failwith "incorrect lookup behaviour" in
    let s = try
              let _ = st_add s "p1" (VNum (int_to_ord 10)) in
              failwith "expected exception when adding the same pointer"
            with
              StorageFailure _ -> s in
    let s = st_remove s "p1" in
    let s = st_remove s "p2" in
    let s = try
              let _ = st_remove s "p3" in
              failwith "expected exception when removing non-existing pointer"
            with
              StorageFailure _ -> s in
    let s = try
              let _ = st_update s "p1" (VNum (int_to_ord 22)) in
              failwith "expected exception when updating non-existing pointer"
            with
              StorageFailure _ -> s in

    if Hashtbl.length s = 0 then
        Printf.printf "sorage tests passed\n"
    else
        Printf.printf "storage tests failed\n"
;;



