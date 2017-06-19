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
open Printf

(* Convert value to string.  *)
let rec value_to_str v =
    match v with
    | VFalse ->
            "vfalse"
    | VTrue ->
            "vtrue"
    | VNum o ->
            ord_to_str o
    | VArray (shp, data) ->
            sprintf "<[%s], [%s]>" (val_lst_to_str shp) (val_lst_to_str data)
    | VClosure (e, func_env) ->
            sprintf "[%s, %s]" (expr_to_str e)  (Env.env_to_str func_env)
    | VImap (p1, p2, partitions, imap_env) ->
            sprintf "[imap %s|%s { %s; %s]" p1 p2 (vpart_lst_to_str partitions) (Env.env_to_str imap_env)
    | VFilter (p1, p2, filter_parts) ->
            sprintf "[filter %s %s { %s]" p1 p2 (filter_parts_to_str filter_parts)

and val_lst_to_str lst =
    String.concat ", " (List.map value_to_str lst)

and vpart_lst_to_str lst =
    String.concat ",\n " (List.map (fun gen_exp_ptr ->
                                  let vg, ep = gen_exp_ptr in
                                  let vgs = vgen_to_str vg in
                                  match ep with
                                  | EPptr p -> sprintf "%s: %s" vgs p
                                  | EPexpr e -> sprintf "%s: %s" vgs (expr_to_str e)) lst)

and filter_parts_to_str fps =
    String.concat ", " (List.map (fun ord_vl_max ->
                                 let o, lst, maxidx = ord_vl_max in
                                 sprintf "%s |-> [%s] max:%d" (ord_to_str o) (val_lst_to_str lst) maxidx)
                       fps)

and vgen_to_str vg =
    let lb, x, ub = vg in
    sprintf "%s <= %s < %s" (value_to_str lb) x (value_to_str ub)


(* TODO This printing is concise, but horribly inefficient as we copy the same string
        over and over again when substituting patterns recursively.  An alternative would
        be to combine patterns in a string tree first and then flatten it once.  *)
and expr_to_str e =
    match e with
    | ETrue ->
            "true"
    | EFalse ->
            "false"
    | ENum (e1) ->
            ord_to_str e1
    | EArray (e1) ->
            sprintf "[%s]" (array_to_str e1)
    | EVar (x) ->
            sprintf "%s" x
    | EFilter (e1, e2) ->
            sprintf "filter %s %s" (expr_to_str e1) (expr_to_str e2)
    | EReduce (e1, e2, e3) ->
            sprintf "reduce %s %s %s"
                    (expr_to_str e1) (expr_to_str e2) (expr_to_str e3)
    | EImap (e1, e2, gelst) ->
            sprintf "imap %s|%s { %s"
                    (expr_to_str e1) (expr_to_str e2) (gen_expr_list_to_str gelst)
    | ELetRec (x, e1, e2) ->
            sprintf "letrec %s = %s in %s"
                     x (expr_to_str e1) (expr_to_str e2)
    | ECond (e1, e2, e3) ->
            sprintf "if %s then %s else %s"
                    (expr_to_str e1) (expr_to_str e2) (expr_to_str e3)
    | EApply (e1, e2) ->
            sprintf "((%s) (%s))" (expr_to_str e1) (expr_to_str e2)
    | ESel (e1, e2) ->
            sprintf "((%s).(%s))" (expr_to_str e1) (expr_to_str e2)
    | ELambda (x, e1) ->
            sprintf "λ%s.(%s)" x (expr_to_str e1)
    | EBinOp (bop, e1, e2) ->
            sprintf "%s %s %s" (expr_to_str e1) (bop_to_str bop) (expr_to_str e2)
    | EUnary (uop, e1) ->
            match uop with
            | OpShape -> sprintf "|%s|" (expr_to_str e1)
            | OpIsLim -> sprintf "islim (%s)" (expr_to_str e1)

and array_to_str e =
    String.concat ", " (List.map expr_to_str e)

and gen_expr_list_to_str gelst =
    String.concat ", "
                (List.map (fun ge ->
                           let (g, e1) = ge in
                           sprintf "%s: (%s)" (gen_to_str g) (expr_to_str e1)) gelst)
and gen_to_str g =
    let (e1, x, e2) = g in
    sprintf "%s <= %s < %s" (expr_to_str e1) x (expr_to_str e2)

and bop_to_str bop =
    match bop with
    | OpPlus -> "+"
    | OpMinus -> "-"
    | OpMult -> "*"
    | OpDiv -> "/"
    | OpMod -> "%"
    | OpLt -> "<"
    | OpLe -> "<="
    | OpGt -> ">"
    | OpGe -> ">="
    | OpEq -> "="
    | OpNe -> "<>"

