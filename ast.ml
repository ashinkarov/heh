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



let rec cmp_ast_noloc e1 e2 =
    match e1, e2 with
    | { expr_kind = EFalse }, { expr_kind = EFalse } -> true
    | { expr_kind = ETrue }, { expr_kind = ETrue } -> true
    | { expr_kind = ENum x }, { expr_kind = ENum y } -> x = y
    | { expr_kind = EVar x }, { expr_kind = EVar y } -> x = y
    | { expr_kind = EArray arr1 }, { expr_kind = EArray arr2 } ->
            List.length arr1 = List.length arr2
            && (List.fold_left2 (fun res x y -> res && cmp_ast_noloc x y) true arr1 arr2)
    | { expr_kind = EBinOp (op1, x1, y1) }, { expr_kind = EBinOp (op2, x2, y2) } ->
            op1 = op2
            && cmp_ast_noloc x1 x1
            && cmp_ast_noloc y1 y2
    | { expr_kind = EUnary (op1, x1) }, { expr_kind = EUnary (op2, x2) } ->
            op1 = op2
            && cmp_ast_noloc x1 x2
    | { expr_kind = ELambda (v1, e1) }, { expr_kind = ELambda (v2, e2) } ->
            v1 = v2
            && cmp_ast_noloc e1 e2
    | { expr_kind = EApply (x1, y1) }, { expr_kind = EApply (x2, y2) } ->
            cmp_ast_noloc x1 x2
            && cmp_ast_noloc y1 y2
    | { expr_kind = ESel (x1, y1) }, { expr_kind = ESel (x2, y2) } ->
            cmp_ast_noloc x1 x2
            && cmp_ast_noloc y1 y2
    | { expr_kind = ECond (x1, y1, z1) }, { expr_kind = ECond (x2, y2, z2) } ->
            cmp_ast_noloc x1 x2
            && cmp_ast_noloc y1 y2
            && cmp_ast_noloc z1 z2
    | { expr_kind = ELetRec (v1, x1, y1) }, { expr_kind = ELetRec (v2, x2, y2) } ->
            v1 = v2
            && cmp_ast_noloc x1 x2
            && cmp_ast_noloc y1 y2
    | { expr_kind = EImap (fr1, cell1, gel1) }, { expr_kind = EImap (fr2, cell2, gel2) } ->
            cmp_ast_noloc fr1 fr2
            && cmp_ast_noloc cell1 cell2
            && List.length gel1 = List.length gel2
            && (List.fold_left2
                (fun res ge1 ge2 ->
                    res
                    && match ge1, ge2 with
                       | ((lb1, v1, ub1), e1), ((lb2, v2, ub2), e2) ->
                               v1 = v2
                               && cmp_ast_noloc lb1 lb2
                               && cmp_ast_noloc ub1 ub2
                               && cmp_ast_noloc e1 e2)
                true
                gel1
                gel2)

    | { expr_kind = EReduce (x1, y1, z1) }, { expr_kind = EReduce (x2, y2, z2) } ->
            cmp_ast_noloc x1 x2
            && cmp_ast_noloc y1 y2
            && cmp_ast_noloc z1 z2

    | { expr_kind = EFilter (x1, y1) }, { expr_kind = EFilter (x2, y2) } ->
            cmp_ast_noloc x1 x2
            && cmp_ast_noloc y1 y2

    | _ -> false


