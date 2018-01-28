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


exception ValueFailure of string

type value =
    | VFalse
    | VTrue
    | VNum of Ordinals.ordinal
    | VArray of value list * value list
    | VClosure of Ast.expr * Env.env

    (* :: ptr_out_shape * ptr_inner_shape * [vgen * ptr_or_expr] * env *)
    | VImap of string * string * (vgen * expr_or_ptr) list * Env.env

    (* :: ptr_func * ptr_expr * [limit_ord * vector * int] *)
    | VFilter of string * string * (Ordinals.ordinal * (value list) * int) list

and vgen = value * string * value

and expr_or_ptr =
    | EPptr of string
    | EPexpr of Ast.expr

(* A shortcut for raising an exception.  *)
let value_err msg =
    raise (ValueFailure msg)

