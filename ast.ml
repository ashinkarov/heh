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

exception ImapFailure of string

type expr =
    | EFalse
    | ETrue
    | ENum of Ordinals.ordinal

    | EVar of string

    | EArray of expr list

    | EBinOp of binop * expr * expr
    | EUnary of unaryop * expr

    | ELambda of string * expr
    | EApply of expr * expr

    | ECond of expr * expr * expr

    | ELetRec of string * expr * expr

    | EImap of expr * expr * (generator * expr) list
    | EReduce of expr * expr * expr
    | EFilter of expr * expr


and binop =
    | OpPlus
    | OpMinus
    | OpDiv
    | OpMult
    | OpLt
    | OpLe
    | OpGt
    | OpGe
    | OpEq
    | OpNe

and unaryop =
    | OpShape
    | OpIsLim

and generator = expr * string * expr

(** Predicates **)


let expr_is_lambda e =
    match e with
    | ELambda (_, _) -> true
    | _ -> false
