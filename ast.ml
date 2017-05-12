open Printf
open Ordinals

exception ImapFailure of string

type expr =
    | EFalse
    | ETrue
    | ENum of ordinal

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

and value =
    | VNum of ordinal
    | VArray of value list * value list
    | VClosure of expr * Env.env

    (* :: ptr_out_shape * ptr_inner_shape * [vgen * ptr_or_expr] * env *)
    | VImap of string * string * (vgen * expr_or_ptr) list * Env.env

    (* :: ptr_func * ptr_expr * [limit_ord * vector * int] *)
    | VFilter of string * string * (ordinal * (value list) * int) list

and vgen = value * string * value

and expr_or_ptr =
    | EPptr of string
    | EPexpr of expr
;;


let rec value_to_str v =
    match v with
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
    String.concat ", " (List.map (fun gen_exp_ptr ->
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
    | OpLt -> "<"
    | OpLe -> "<="
    | OpGt -> ">"
    | OpGe -> ">="
    | OpEq -> "="
    | OpNe -> "<>"

;;
