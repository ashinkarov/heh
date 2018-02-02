(*
 * Copyright (c) 2017-2018, Artem Shinkarov <artyom.shinkaroff@gmail.com>
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
open Print
open Ordinals

exception StorageFailure of string

(* RC stores the reference count for each pointer;
 * V  stores a value: in case the value is None,
 *    this means that we are dealing with _|_ when
 *    evaluating letrec.  This value should lead to
 *    an error when such a pointer is looked-up.
 *    In case V is Some (value), we are dealing
 *    with a regular value from Value module.
 *)
type rcval = { rc: int; v: value option}
type storage = (string, rcval) Hashtbl.t

let mk_rcval rc v = { rc = rc; v = Some (v) }
let mk_bot_rcval rc = { rc = rc; v = None }

let st_new: unit -> storage = fun () ->
    Hashtbl.create 100

(* A helper function to do debugging *)
let find_and_raise st p expected msg =
    let exists = try Hashtbl.find st p; true with Not_found -> false in
    if expected <> exists then
        raise @@ StorageFailure (Printf.sprintf "pointer `%s': %s" p msg)


let st_add st p rc v =
    find_and_raise st p false "already exists";
    Hashtbl.add st p @@ mk_rcval rc v;
    st

let st_add_bottom st p rc =
    find_and_raise st p false "already exists";
    Hashtbl.add st p @@ mk_bot_rcval rc;
    st

let st_remove st p =
    find_and_raise st p true "doesn't exist --- cannot remove";
    Hashtbl.remove st p;
    st

let st_lookup st p =
    find_and_raise st p true "doesn't exist --- cannot lookup";
    match Hashtbl.find st p with
    | { v = Some (value) } ->
            value
    | { v = None } ->
            raise @@ StorageFailure (Printf.sprintf
                                     "attempt to lookup bottom value bound to `%s'" p)

let st_lookup_rc st p =
    find_and_raise st p true "doesn't exist --- cannot lookup reference count";
    let {rc = rc} = Hashtbl.find st p in
    rc

let st_lookup_rcval st p =
    find_and_raise st p true "doesn't exist --- cannot lookup";
    Hashtbl.find st p

let st_update st p v =
    find_and_raise st p true "doesn't exist --- cannot update";
    let rc = st_lookup_rc st p in
    Hashtbl.replace st p @@ mk_rcval rc v;
    st

let st_update_rcval st p rv =
    find_and_raise st p true "doesn't exist --- cannot update";
    Hashtbl.replace st p rv;
    st

let st_to_str st =
    Hashtbl.fold (fun k value tail_s ->
                  let { rc =rc;  v = v } = value in
                  Printf.sprintf
                    "%s |(%d)-> %s%s"
                    k
                    rc
                    (match v with
                     | Some (value) -> value_to_str value
                     | None -> "_|_")
                    (if tail_s = "" then "" else Printf.sprintf ", %s" tail_s)) st ""

(* update all the enclosed environments of the storage replacing bindings of
   form x |-> pold with x |-> pnew.  *)
let update_letrec_ptr st pold pnew =
    let rec env_updater env =
        match env with
        | [] -> []
        | (x, p) :: tl -> (if p = pold then (x, pnew) else (x, p))
                          :: env_updater tl
    in
    let value_updater k newval =
        let {v = value } = newval in
        let value =
            match value with
            | Some (VClosure (e, env)) ->
                    Some (VClosure (e, env_updater env))
            | Some (VImap (p1, p2, parts, env)) ->
                    Some (VImap (p1, p2, parts, env_updater env))
            | _ -> value
        in Some ({newval with v = value})
    in
    Hashtbl.filter_map_inplace value_updater st;
    st

let st_incrc ?(inc_by=1) st p =
    let rv = st_lookup_rcval st p in
    if inc_by < 0 then
        raise @@ StorageFailure (Printf.sprintf
                                 "negative rc increment: `%s' inc_by=`%d'"
                                 p inc_by);
    st_update_rcval st p {rv with rc = (rv.rc + inc_by)}


let rec _rc_dec (st:storage) p ptrs =
    if List.mem p ptrs then
        st
    else
        let rv = st_lookup_rcval st p in
        let st = st_update_rcval st p {rv with rc = (rv.rc - 1)} in
        if rv.rc = 1 then
            let rec upd st env vars = match vars with
            | v :: t ->
                    _rc_dec (upd st env t) (Env.env_lookup env v) (p::ptrs)
            | [] ->
                    st
            in

            match rv.v with
            | Some (VClosure (e, env)) ->
                    upd st env @@ free_vars_lst e
            | Some (VImap (_, _, parts, env)) ->
                    let st, vars = List.fold_left
                               (fun stvar part  ->
                                let ((v1, x, v2), pe) = part in
                                let st, vars = stvar in
                                match pe with
                                | EPptr (p) ->
                                        ((_rc_dec st p ptrs), vars)
                                | EPexpr (e) ->
                                        (st, List.append
                                             (List.filter (fun y -> y <> x)
                                              @@ Ast.free_vars_lst e)
                                             vars))
                                (st, [])
                                parts in
                    upd st env vars
            | _ ->
                    st
        else
            st

let st_decrc st p = _rc_dec st p []

let varcount vars x = List.fold_left
                          (fun count var ->
                           count + if x = var then 1 else 0)
                          0
                          vars

let st_decrc_fv st env e =
    let vars = Ast.free_vars_lst e in
    List.fold_left (fun st var -> st_decrc st @@ Env.env_lookup env var) st vars

let st_incrc_func_arg st p x body =
    let vars = Ast.free_vars_lst body in
    let count = varcount vars x in
    if count = 0 then
        st_decrc st p
    else
        st_incrc st p ~inc_by:(count-1)

let st_incrc_func_fv st env x body =
    let vars = List.filter (fun y -> x <> y) @@ Ast.free_vars_lst body in
    List.fold_left (fun st var -> st_incrc st @@ Env.env_lookup env var) st vars


let rec final_storage_consistent st p =
    let rec reachable st p ptrs =
        if List.mem p ptrs then
            ptrs
        else begin
            let {rc = rc; v = v} = st_lookup_rcval st p in
            if rc <= 0 then
                raise @@ StorageFailure
                         (Printf.sprintf
                          "pointer `%s' reachable, but its rc=%d"
                          p rc);
            match v with
            | None ->
                    raise @@ StorageFailure
                             (Printf.sprintf
                              "pointer `%s' bound to _|_ is reachable" p)
            | Some (VClosure (e, env)) ->
                    List.fold_left (fun ptrs var ->
                                    reachable st (Env.env_lookup env var) ptrs)
                                   (p :: ptrs)
                                   (Ast.free_vars_lst e)
            | Some (VImap (_, _, _, env)) ->
                    (* TODO implement *)
                    failwith "not implemented"
            | _ -> p :: ptrs
        end
    in
    let reachable_ptrs = reachable st p [] in
    (* Check that all the remaining pointers have reference count 0  *)
    Hashtbl.fold (fun p value () ->
                  let { rc =rc;  v = v } = value in
                  if v <> None
                     && not (List.mem p reachable_ptrs)
                     && rc <> 0 then
                         raise @@ StorageFailure
                                  (Printf.sprintf
                                   "pointer `%s' is not reachable but its rc=%d"
                                   p rc)
                  else
                      ())
                 st ()

