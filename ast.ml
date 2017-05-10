open Printf

exception ImapFailure of string

type expr = 
    | EFalse
    | ETrue
    | ENum of ord

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


let rec expr_to_str e =
    match e with
    | ETrue ->
            "true"
    | EFalse -> 
            "false"
    | ENum (e1) ->
            "Number XXX"
    | EArray (e1) -> 
            array_to_str e1
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
    | ELambda (x, e1) ->
            sprintf "\\%s.(%s)" x (expr_to_str e1)
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
    | OpLt -> "<"
    | OpLe -> "<="
    | OpGt -> ">"
    | OpGe -> ">="
    | OpEq -> "="
    | OpNe -> "<>"

;;
