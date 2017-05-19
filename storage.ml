open Ast
open Value
open Print
open Ordinals

exception StorageFailure of string

type storage = (string, value) Hashtbl.t

let st_new: unit -> storage = fun () ->
    Hashtbl.create 100

(* A helper function to do debugging *)
let find_and_raise st p expected msg =
    let exists = try Hashtbl.find st p; true with Not_found -> false in
    if expected <> exists then
        raise (StorageFailure msg)


let st_add st p v =
    (* This is for debugging purposes.  *)
    find_and_raise
        st p false
        (Printf.sprintf "Attempt to add the pointer `%s' which already exists in the storage" p);
    Hashtbl.add st p v;
    st

let st_remove st p =
    (* This is for debugging purposes.  *)
    find_and_raise
        st p true
        (Printf.sprintf "Attempt to remove the pointer `%s' which does not exist in the storage" p);
    Hashtbl.remove st p;
    st

let st_update st p v =
    (* This is for debugging purposes.  *)
    find_and_raise
        st p true
        (Printf.sprintf "Attempt to update the pointer `%s' which does not exist in the storage" p);
    Hashtbl.replace st p v;
    st

let st_lookup st p =
    find_and_raise
        st p true
        (Printf.sprintf "Attempt to lookup the pointer `%s' which does not exist in the storage" p);
    Hashtbl.find st p


let st_to_str st =
    Hashtbl.fold (fun k v tail_s ->
                  Printf.sprintf
                    "%s |-> %s%s"
                    k
                    (value_to_str v)
                    (if tail_s = "" then "" else Printf.sprintf ", %s" tail_s)) st ""

