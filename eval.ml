open Ast
open Ordinals
open Storage
open Env
open Printf

exception EvalFailure of string

(* A global variable to generate unique names of pointers.  *)
let ptr_count = ref 0
;;

(* Generate a fresh pointer name.  *)
let fresh_ptr_name () =
    ptr_count := !ptr_count + 1;
    sprintf "p%d" !ptr_count
;;

let eval_err msg =
    raise (EvalFailure msg)

let mk_int_value n = VNum (int_to_ord n)

let mk_empty_array () = VArray ([mk_int_value 0], [])

let value_is_array v =
    match v with
    | VArray (_, _) -> true
    | _ -> false


let value_is_num v =
    match v with
    | VNum (o) -> true
    | _ -> false

let value_num_to_ord v =
    match v with
    | VNum o -> o
    | _ -> eval_err (sprintf "value_num_to ord called with `%s'" (value_to_str v))

let value_num_add v1 v2 =
    VNum (add (value_num_to_ord v1) (value_num_to_ord v2))

let value_array_to_pair v =
    match v with
    | VArray (s, d) -> (s, d)
    | _ -> eval_err (sprintf "value_array_to_pair called with `%s'" (value_to_str v))

let shape st p =
    match st_lookup st p with
    | VFalse ->
            mk_empty_array ()
    | VTrue ->
            mk_empty_array ()
    | VNum _ ->
            mk_empty_array ()
    | VArray (shp, _) ->
            VArray ([mk_int_value (List.length shp)], shp)
    | VClosure (_, _) ->
            mk_empty_array ()
    | VImap (p1, p2, _, _) ->
            let v1 = st_lookup st p1 in
            let v2 = st_lookup st p2 in
            if not (value_is_array v1) then
                eval_err (sprintf "frame shape of imap `%s' is not an array" (value_to_str v1))
            else if not (value_is_array v2) then
                eval_err (sprintf "element shape of imap `%s' is not an array" (value_to_str v2))
            else begin
                let (s1, d1) = value_array_to_pair v1 in
                let (s2, d2) = value_array_to_pair v2 in
                VArray ([value_num_add (List.hd s1) (List.hd s2)], (List.append d1 d2))
            end

    | VFilter (p_func, p_expr, _) ->
            (* FIXME *)
            failwith "I don't know how  to take shape of a filter"
;;

let array_element_shape_valid st ptrlst =
    if (List.length ptrlst) <= 1 then
        true
    else
        let rec cmp st shp_first lst =
            match lst with
            | [] -> true
            | p :: tl ->
                    let v = shape st p in
                    if v <> shp_first then
                        false
                    else
                        cmp st shp_first tl
        in cmp st (shape st (List.hd ptrlst)) (List.tl ptrlst)
;;

let rec array_element_type_finite st ptrlst =
    match ptrlst with
    | [] -> true
    | p :: tl -> let v = st_lookup st p in
                 match v with
                 | VImap (_, _, _, _) -> false
                 | VFilter (_, _, _) -> false
                 | _ -> array_element_type_finite st tl
;;

(* return the shape vector of the first element of the pointer list.  *)
let ptr_list_fst_shape st ptrlst =
    if ptrlst = [] then
        []
    else
        let _, shp_vec = value_array_to_pair (shape st (List.hd ptrlst)) in
        shp_vec
;;

let value_closure_to_triple v =
    match v with
    | VClosure (e, env) ->
        begin
            match e with
            | ELambda (x, body) ->
                    (x, body, env)
            | _ -> eval_err
                      (sprintf
                          "value_closure_to_triple expected lambda expr, got `%s' isntead"
                          (expr_to_str e))
        end
    | _ -> eval_err
              (sprintf
                  "value_closure_to_triple expected VClosure but got `%s' instead"
                  (value_to_str v))
;;

let ptr_binop st op p1 p2 =
    let v1 = st_lookup st p1 in
    let v2 = st_lookup st p2 in
    if not (value_is_num v1) then
        eval_err (sprintf "attempt to perform binary operation on non-number `%s'"
                          (value_to_str v1));
    if not (value_is_num v2) then
        eval_err (sprintf "attempt to perform binary operation on non-number `%s'"
                          (value_to_str v2));
    let o1 = value_num_to_ord v1 in
    let o2 = value_num_to_ord v2 in
    match op with
    | OpPlus -> VNum (add o1 o2)
    | OpMult -> VNum (mult o1 o2)
    | OpMinus -> VNum (sub o1 o2)
    | OpDiv -> eval_err "ordinal division not yet implemented"
    | OpEq -> if compare o1 o2 = 0 then VTrue else VFalse
    | OpNe -> if compare o1 o2 <> 0 then VTrue else VFalse
    | OpLt -> if compare o1 o2 = -1 then VTrue else VFalse
    | OpLe -> let cmp = compare o1 o2 in
              if cmp = -1 || cmp = 0 then VTrue else VFalse
    | OpGt -> if compare o1 o2 = 1 then VTrue else VFalse
    | OpGe -> let cmp = compare o1 o2 in
              if cmp = 1 || cmp = 0 then VTrue else VFalse
;;

let ptr_unary st op p1 =
    let v1 = st_lookup st p1 in
    match op with
    | OpShape -> shape st p1
    | OpIsLim -> if not (value_is_num v1) then
                    eval_err (sprintf "attempt to apply islim to `%s'" (value_to_str v1));
                 if ord_is_lim (value_num_to_ord v1) then VTrue else VFalse
;;

(* update all the enclosed environments of the storage replacing bindings of
   form x |-> pold with x |-> pnew.  *)
let update_letrec_ptr st pold pnew =
    let rec env_updater env =
        match env with
        | [] -> []
        | (x, p) :: tl -> (if p = pold then (x, pnew) else (x, p))
                          :: env_updater tl
    in
    let value_updater k v =
        let res = match v with
                  | VClosure (x, env) -> VClosure (x, env_updater env)
                  | VImap (p1, p2, parts, env) -> VImap (p1, p2, parts, env_updater env)
                  | _ -> v
        in Some (res)
    in
    Hashtbl.filter_map_inplace value_updater st;
    st
;;


let rec eval st env e =
    let add_fresh_val_as_result st v =
        let p = fresh_ptr_name () in
        let st = st_add st p v in
        (st, p)
    in
    match e with
    | EFalse ->
            add_fresh_val_as_result st VFalse

    | ETrue ->
            add_fresh_val_as_result st VTrue

    | ENum (o) ->
            add_fresh_val_as_result st (VNum (o))

    | EVar (x) ->
            (st, (env_lookup env x))

    | EArray (lst) ->
            (* evaluate all the elements in the list sequentially.  *)
            let st, ptrlst = eval_expr_lst st env lst in
            (* check that the shape of the elements is the same.  *)
            if not (array_element_shape_valid st ptrlst) then
                eval_err (sprintf "elements of the array `%s' are of different shape" (expr_to_str e));
            if not (array_element_type_finite st ptrlst) then
                eval_err (sprintf "elements of the array `%s' have imap/filters" (expr_to_str e));
            (* get the data vector of the shape of the first element.  *)
            let shp_vec = ptr_list_fst_shape st ptrlst in
            let shp = List.append [mk_int_value (List.length ptrlst)] shp_vec in
            let data = List.fold_right
                            (fun ptr val_lst ->
                             let ptr_val = st_lookup st ptr in
                             match ptr_val with
                             | VArray (_, d) -> List.append d val_lst
                             | _ -> List.append [ptr_val] val_lst)

                            ptrlst [] in
            add_fresh_val_as_result st (VArray (shp, data))

    | ELambda (_, _) ->
            add_fresh_val_as_result st (VClosure (e, env))

    | EApply (e1, e2) ->
            let (st, p1) = eval st env e1 in
            let (st, p2) = eval st env e2 in
            let var, body, env' = value_closure_to_triple (st_lookup st p1) in
            eval st (env_add env' var p2) body

    | EBinOp (op, e1, e2) ->
            let (st, p1) = eval st env e1 in
            let (st, p2) = eval st env e2 in
            add_fresh_val_as_result st (ptr_binop st op p1 p2)

    | EUnary (op, e1) ->
            let (st, p1) = eval st env e1 in
            add_fresh_val_as_result st (ptr_unary st op p1)

    | ECond (e1, e2, e3) ->
            let (st, p1) = eval st env e1 in
            let v = st_lookup st p1 in
            begin
                match v with
                | VTrue -> eval st env e2
                | VFalse -> eval st env e3
                | _ -> eval_err (sprintf "predicate of `%s' evaluates to `%s' (true/false expected)"
                                         (expr_to_str e) (value_to_str v))
            end

    | ELetRec (var, e1, e2) ->
            let pname = fresh_ptr_name () in
            let (st, p1) = eval st (env_add env var pname) e1 in
            let st = update_letrec_ptr st pname p1 in
            eval st (env_add env var p1) e2


           (* FIXME *)
    | _ -> failwith (sprintf "I don't know how to evaluate `%s'" (expr_to_str e))

(* evaluate a list of expressions propagating storage at every recursive call;
   return a tuple:

       (last storage, list of pointers)  *)
and eval_expr_lst st env lst =
    match lst with
    | [] -> (st, [])
    | e :: tl ->
            let st', p = eval st env e in
            let st'', res = eval_expr_lst st' env tl in
            (st'', p :: res)
;;
