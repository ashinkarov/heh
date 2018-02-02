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


module StringSet = Set.Make (String)
module StringMap = Map.Make (String)


let free_vars e =
  List.fold_left (fun s v -> StringSet.add v s) StringSet.empty @@ Ast.free_vars_lst e

let print_free_vars e =
    Printf.printf "Free vars of expr %s\n" (Print.expr_to_str e);
    StringSet.iter (fun x -> Printf.printf "%s, " x)
                   (free_vars e);
    Printf.printf "\n"


let rec wrap_lambda lst e =
    match lst with
    | [] -> e
    | x :: t -> Ast.mk_elambda x @@ wrap_lambda t e

let rec lst_print l =
    match l with
    | [] -> ""
    | x :: xs -> Printf.sprintf "%s %s" x (lst_print xs)

let print_mapping m =
    let xprint var varlist_expr =
        let varlist, expr = varlist_expr in
        Printf.printf "%s: Λ%s.%s\n" var (lst_print varlist) (Print.expr_to_str expr)
    in
    (*let xprint1 var varlist_expr =
        let varlist, expr = varlist_expr in
        Printf.printf "%s: %s\n" var @@ Print.expr_to_str (wrap_lambda varlist expr)
    in*)
    StringMap.iter xprint m



let var_count = ref 0

(* Generate a fresh variable name.  *)
let fresh_var () =
    var_count := !var_count + 1;
    Printf.sprintf "__f%d" !var_count


let rec lift m e =
    match e with
    | {expr_kind = ELambda (x1, e1) } ->
            let fv = free_vars e in
            if StringSet.cardinal fv = 0 then
                let m, e1' = lift m e1 in
                Printf.printf "=1= lifting body %s into %s\n" (Print.expr_to_str e1) (Print.expr_to_str e1');
                (* XXX this avoids eta-extended functions, but maybe they can be useful.  *)
                match e1' with
                | {expr_kind = EApply (e', {expr_kind = EVar (x1)}) } ->
                        (m, e')
                | _ ->
                    let fresh = fresh_var () in
                    let m = StringMap.add fresh ([x1], e1') m
                    (* FIXME location. *)
                    in (m, mk_evar fresh)
            else
                let rec mk_app fvlist body =
                    match fvlist with
                    | x :: [] -> mk_eapply body (mk_evar x)
                    | x :: xs -> mk_app xs (mk_eapply body (mk_evar x))
                    | [] -> failwith "no free vars"
                in
                let m, e1' = lift m e1 in
                Printf.printf "=2= lifting body %s into %s\n" (Print.expr_to_str e1) (Print.expr_to_str e1');
                let fresh = fresh_var () in
                let fvlist = StringSet.fold (fun var lst -> var :: lst) fv [] in
                Printf.printf "=2= fvlist = %s\n" (lst_print fvlist);

                let m = StringMap.add fresh ((List.append fvlist [x1]),  e1') m  in
                (*let fresh1 = fresh_var () in
                let m = StringMap.add fresh1 (fvlist, (mk_app fvlist (mk_evar fresh))) m in*)
                (* FIXME location. *)
                (m, mk_app fvlist (mk_evar fresh))
    | _ ->
            Traversal.topdown lift m e


let rec propagate m e =
    match e with
    | {expr_kind = EVar x1 } ->
            if StringMap.mem x1 m then
                (m, StringMap.find x1 m)
            else
                (m, e)
    | {expr_kind = ELambda (x1, e1) } ->
            if StringMap.mem x1 m then
                let v = StringMap.find x1 m in
                let m = StringMap.remove x1 m in
                let m, e1' = propagate m e1 in
                (StringMap.add x1 v m, mk_elambda x1 e1')
            else
                let m, e1' = propagate m e1 in
                (m, mk_elambda x1 e1')
    | {expr_kind = ELetRec (x1, e1, e2) } ->
            if (match e1.expr_kind with
                | EFalse | ETrue | EVar _ | ENum _  -> true
                | _ -> false)
            then begin
                if StringMap.mem x1 m then
                    let m = StringMap.remove x1 m in
                    (* Add new mapping *)
                    let m = StringMap.add x1 e1 m in
                    (* Substitute e1 in the body of the letrec.  *)
                    let m, e2' = propagate m e2 in
                    (m, e2')
                else
                    let m = StringMap.add x1 e1 m in
                    let m, e2' = propagate m e2 in
                    (m, e2')
            end else
                let m, e1' = propagate m e1 in
                let m, e2' = propagate m e2 in
                (m, mk_eletrec x1 e1' e2')
    | _ ->
            Traversal.topdown propagate m e


let lift_lambdas e =
    let m, e = lift StringMap.empty e in
    Printf.printf "--- lifting lambdas into global functions and updating the expression\n";
    print_mapping m;
    let _, e = propagate StringMap.empty e in
    (*
     * Create an environment for all the functions, using the naming
     * scheme for the pointers __p + <fun-name>.
     *)
    let env = Env.env_new () in
    let env = StringMap.fold (fun var valist_expr env ->
                              Env.env_add env var ("__p" ^ var))
                             m
                             env in
    (*
     * Create pointers for global functions.
     *)
    let st = Storage.st_new () in
    let st = StringMap.fold (fun var varlist_expr st ->
                             let varlist, expr = varlist_expr in
                             Storage.st_add st ("__p" ^ var)
                                            (* FIXME it is not clear what shall we do with RC here
                                             *       we can use more sophisticated type than int
                                             *       to indicate that this is an infinite rc.
                                             *       Putting `1` for now, even though this is not
                                             *       correct.
                                             *)
                                            1
                                            (* Include `env` in all the function closures
                                             * so that they have access to all the global
                                             * functions.
                                             *)
                                            @@ Value.VClosure ((wrap_lambda varlist expr), env))
                            m
                            st in
    (st, env, e)
