(*
 * Copyright (c) 2017, Artem Shinkarov <artyom.shinkaroff@gmail.com>
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
 * REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
 * AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
 * INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
 * LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE
 * OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
 * PERFORMANCE OF THIS SOFTWARE.
 *)

open Ast
open Value
open Ordinals
open Print
open Printf

(** Predicates.  **)

let value_is_true v =
    match v with
    | VTrue -> true
    | _ -> false

let value_is_false v =
    match v with
    | VFalse -> true
    | _ -> false

let value_is_num v =
    match v with
    | VNum (o) -> true
    | _ -> false

let value_is_array v =
    match v with
    | VArray (_, _) -> true
    | _ -> false

let value_is_closure v =
    match v with
    | VClosure (_, _) -> true
    | _ -> false

let value_is_imap v =
    match v with
    | VImap (_, _, _, _) -> true
    | _ -> false

let value_is_filter v =
    match v with
    | VFilter (_, _, _) -> true
    | _ -> false

let value_is_selectable v =
    match v with
    | VNum (_)
    | VArray (_, _)
    | VImap (_, _, _, _)
    | VFilter (_, _, _) -> true
    | _ -> false



(** Constructors  **)

let mk_false_value = VFalse

let mk_true_value = VTrue

let mk_int_value n = VNum (int_to_ord n)

let mk_ord_value o = VNum (o)

let mk_array_value shp_vec data_vec =
    if not @@ List.for_all (fun x -> value_is_num x) shp_vec then
        value_err @@ sprintf "mk_array: invalid shape vector [%s]"
                             @@ val_lst_to_str shp_vec;
    let elcount = List.fold_left (fun res x ->
                                  match x with
                                  | VNum o -> mult res o
                                  | _ -> failwith "non-number found in shape")
                                 one shp_vec in
    if compare elcount omega <> -1 then
        value_err @@ sprintf "mk_array: shape [%s] suggests that arrray will have more than omega elements"
                             @@ val_lst_to_str shp_vec;
    if ord_to_nat elcount <> List.length data_vec then
        value_err @@ sprintf "mk_array: shape [%s] does not match data [%s]"
                             (val_lst_to_str shp_vec) (val_lst_to_str data_vec);
    VArray (shp_vec, data_vec)


let mk_closure_value e env =
    if not @@ expr_is_lambda e then
        value_err @@ sprintf "mk_closure: expected abstraction as first argument, got `%s'"
                             @@ expr_to_str e;
    VClosure (e, env)

let mk_empty_vector () = VArray ([mk_int_value 0], [])

let mk_vector value_vec =
    VArray ([mk_int_value @@ List.length value_vec], value_vec)

let mk_imap_value p1 p2 parts env =
    (* XXX not sure we need to check that partitions are sane as it is
           quite expensive.  *)
    VImap (p1, p2, parts, env)

let mk_filter_value p1 p2 parts =
    VFilter (p1, p2, parts)

let value_num_to_ord v =
    match v with
    | VNum o -> o
    | _ -> value_err @@ sprintf "value_num_to ord called with `%s'" @@ value_to_str v

let value_num_add v1 v2 =
    VNum (add (value_num_to_ord v1) (value_num_to_ord v2))

let value_num_mult v1 v2 =
    VNum (mult (value_num_to_ord v1) (value_num_to_ord v2))

(* This function returns an integer. *)
let value_num_compare v1 v2 =
    compare (value_num_to_ord v1) (value_num_to_ord v2)

let value_array_to_pair v =
    match v with
    | VArray (s, d) -> (s, d)
    | _ -> value_err @@ sprintf "value_array_to_pair called with `%s'" @@ value_to_str v

let value_imap_to_tuple v =
    match v with
    | VImap (p1, p2, parts, env) -> (p1, p2, parts, env)
    | _ -> value_err "value_imap_to_tuple"

let value_filter_to_tuple v =
    match v with
    | VFilter (p1, p2, parts) -> (p1, p2, parts)
    | _ -> value_err "value_filter_to_tuple"

let value_num_vec_lt l r =
    List.fold_left2 (fun r x y ->
                     if not r then
                         r
                     else
                         value_num_compare x y = -1)
                     true
                     l r

let value_num_vec_le l r =
    List.fold_left2 (fun r x y ->
                     if not r then
                         r
                     else
                         let cmp = value_num_compare x y in
                         cmp = -1 || cmp = 0)
                     true
                     l r

let value_num_vec_in_vgen vec vgen =
    let lb, x, ub = vgen in
    let _, lb_data_vec = value_array_to_pair lb in
    let _, ub_data_vec = value_array_to_pair ub in
    value_num_vec_le lb_data_vec vec && value_num_vec_lt vec ub_data_vec

let value_closure_to_triple v =
    match v with
    | VClosure (ELambda (x, body), env) ->
            (x, body, env)
    | _ ->
            value_err @@ sprintf "expected closure with abstraction, but got `%s' instead"
                                 @@ value_to_str v


