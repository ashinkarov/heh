open Ast
open Ordinals

exception ValueFailure of string

type value =
    | VFalse
    | VTrue
    | VNum of Ordinals.ordinal
    | VArray of value list * value list
    | VClosure of expr * Env.env

    (* :: ptr_out_shape * ptr_inner_shape * [vgen * ptr_or_expr] * env *)
    | VImap of string * string * (vgen * expr_or_ptr) list * Env.env

    (* :: ptr_func * ptr_expr * [limit_ord * vector * int] *)
    | VFilter of string * string * (Ordinals.ordinal * (value list) * int) list

and vgen = value * string * value

and expr_or_ptr =
    | EPptr of string
    | EPexpr of expr

(* A shortcut for raising an exception.  *)
let value_err msg =
    raise (ValueFailure msg)

