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


(* Change applications of "reduce" and "filters" that were parsed as EApply
   into EReduce and EFilter constructs. *)
let rec app_to_hof () e =
    match e with
    | { expr_kind =
        EApply ({ expr_kind =
        EApply ({ expr_kind =
        EApply ({ expr_kind =
        EVar ("reduce")}, e1)}, e2)}, e3) } ->
        ((), mk_ereduce e1 e2 e3)

    | { expr_kind =
        EApply ({ expr_kind =
        EApply ({ expr_kind =
        EVar ("filter")}, e1)}, e2) } ->
        ((), mk_efilter e1 e2)

    | { expr_kind = EVar ("reduce"); loc=l } ->
        Parser.parse_err_loc l "reduce found with less than three arguments"

    | { expr_kind = EVar ("filter"); loc=l } ->
        Parser.parse_err_loc l "filter found with less than two arguments"

    | _ -> Traversal.topdown app_to_hof () e
