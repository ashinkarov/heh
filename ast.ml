exception ImapFailure of string

type expr = 
    | ENum of ord

    | EVar of string

    | EBinOp of binop * expr * expr
    | EUnary of unaryop * expr

    | ELambda of string * expr
    | EApply of expr * expr

    | ECond of expr * expr * expr

    | ELetRec of string * expr * expr

    | EImap of expr * expr * (generator * expr) list
    | EReduce of expr * expr * expr
    | EFilter of expr * expr

    | EFalse
    | ETrue
    | EArray of expr list

and binop =
    | OpPlus
    | OpMinus
    | OpDiv
    | OpMult

and unaryop = 
    | OpShape
    | OpIsLim

and generator = expr * string * expr

and env = (string * string) list

and value =
    | VInt of int
    | VArray of value list * value list
    | VClosure of expr * env

    (* :: ptr_out_shape * ptr_inner_shape * [vgen * ptr_or_expr] * env *)
    | VImap of string * string * (vgen * expr_or_ptr) list * env

    (* :: ptr_func * ptr_expr * [limit_ord * vector * int] *)
    | VFilter of string * string * (ord * (value list) * int) list

and vgen = value * string * value

and expr_or_ptr = 
    | EPptr of string
    | EPexpr of expr

and ord = (int * int) list

;;

