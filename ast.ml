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
