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

type expr = { loc: Loc.t; expr_kind: expr_kind }

and expr_kind =
    | EFalse
    | ETrue
    | ENum of Ordinals.ordinal

    | EVar of string

    | EArray of expr list

    | EBinOp of binop * expr * expr
    | EUnary of unaryop * expr

    | ELambda of string * expr
    | EApply of expr * expr
    | ESel of expr * expr

    | ECond of expr * expr * expr

    | ELetRec of string * expr * expr

    | EImap of expr * expr * (generator * expr) list
    | EReduce of expr * expr * expr
    | EFilter of expr * expr


and binop =
    | OpPlus
    | OpMinus
    | OpDiv
    | OpMod
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

(** Constructors  **)
let mk_efalse ?(loc=Loc.internal) () = { loc=loc; expr_kind=EFalse }
let mk_etrue ?(loc=Loc.internal) () = { loc=loc; expr_kind=ETrue }
let mk_enum ?(loc=Loc.internal) o = { loc=loc; expr_kind=ENum o }
let mk_evar ?(loc=Loc.internal) x = { loc=loc; expr_kind=EVar x }
let mk_earray ?(loc=Loc.internal) lst = { loc=loc; expr_kind=EArray lst }
let mk_ebinop op lhs rhs = let {loc = l} = lhs in
                           { loc=l; expr_kind=EBinOp (op, lhs, rhs) }
let mk_eunary ?(loc=Loc.internal) op arg = { loc=loc; expr_kind=EUnary (op, arg) }
let mk_elambda ?(loc=Loc.internal) x body = { loc=loc; expr_kind=ELambda (x, body) }
let mk_eapply lhs rhs = let {loc = l} = lhs in
                        { loc=l; expr_kind=EApply (lhs, rhs) }
let mk_esel lhs rhs = let {loc = l} = lhs in
                      { loc=l; expr_kind=ESel (lhs, rhs) }
let mk_econd ?(loc=Loc.internal) p t f = { loc=loc; expr_kind=ECond (p, t, f) }
let mk_eletrec ?(loc=Loc.internal) x e1 e2 = { loc=loc; expr_kind=ELetRec (x, e1, e2) }
let mk_eimap ?(loc=Loc.internal) sh1 sh2 gelst = { loc=loc; expr_kind=EImap (sh1, sh2, gelst) }
let mk_ereduce ?(loc=Loc.internal) f neut arr = { loc=loc; expr_kind=EReduce (f, neut, arr) }
let mk_efilter ?(loc=Loc.internal) f arr = { loc=loc; expr_kind=EFilter (f, arr) }



(** Predicates **)


let expr_is_lambda e =
    match e with
    | { expr_kind = ELambda (_, _) } -> true
    | _ -> false
