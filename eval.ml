open Globals
open Ast
open Ordinals
open Storage
open Env
open Value
open Valueops
open Print
open Printf

(* TODO:
    * write tests for imap
    * implement filter
*)
exception EvalFailure of string

(* A global variable to generate unique names of pointers.
   XXX Shall we move this to globals or make it module-local? *)
let ptr_count = ref 0

(* Generate a fresh pointer name.  *)
let fresh_ptr_name () =
    ptr_count := !ptr_count + 1;
    sprintf "p%d" !ptr_count

(* zip two lists of the same length.  *)
let rec zip l1 l2 = match l1,l2 with
  | [],[] ->
          []
  | (h1::tl1),(h2::tl2) ->
          (h1,h2) :: (zip tl1 tl2)
  | _ -> failwith "lists of different lengths passed to zip"

let rec list_split lst n =
    match n with
    | 0 -> ([], lst)
    | x when x > 0 ->
            begin match lst with
            | [] -> failwith "list_split"
            | h :: t ->
                    let l, r = list_split t (x-1) in
                    (h::l, r)
            end
    | _ -> failwith "list_split"

let eval_err msg =
    raise (EvalFailure msg)


let eval_warn msg =
    printf "warning: %s\n" msg


(* Find a partition in the `(vgen * expr_or_ptr) list' where idx ∊ gen.
   Return an index-value tuple.

   TODO this is a linear search, we can make it faster by using binary
         search while maintaining this list sorted.  *)
let find_partition lst idx_vec =
    let rec _find _lst_idx _lst _idx_vec =
        match _lst with
        | [] ->
                begin
                eval_err @@ sprintf "cannot find index [%s] in partitions %s"
                                    (val_lst_to_str idx_vec)
                                    (vpart_lst_to_str lst)
                end
        | (vg, ep) :: t ->
                begin
                if value_num_vec_in_vgen _idx_vec vg then
                    (_lst_idx, (vg, ep))
                else
                    _find (_lst_idx+1) t _idx_vec
                end
    in
    let index, v = _find 0 lst idx_vec in
    (*printf "--- find parts %s\n for vec %d length = %d returns %s\n"
           (vpart_lst_to_str lst) index (List.length lst) (val_lst_to_str idx_vec);*)
    (index, v)


let shape_v st v =
    match v with
    | VFalse ->
            mk_empty_vector ()
    | VTrue ->
            mk_empty_vector ()
    | VNum _ ->
            mk_empty_vector ()
    | VArray (shp, _) ->
            VArray ([mk_int_value (List.length shp)], shp)
    | VClosure (_, _) ->
            mk_empty_vector ()
    | VImap (p1, p2, _, _) ->
            let v1 = st_lookup st p1 in
            let v2 = st_lookup st p2 in
            if not (value_is_array v1) then
                eval_err @@ sprintf "frame shape of imap `%s' is not an array"
                            @@ value_to_str v1
            else if not @@ value_is_array v2 then
                eval_err @@ sprintf "element shape of imap `%s' is not an array"
                            @@ value_to_str v2
            else begin
                let s1, d1 = value_array_to_pair v1 in
                let s2, d2 = value_array_to_pair v2 in
                VArray ([value_num_add (List.hd s1) (List.hd s2)], (List.append d1 d2))
            end

    | VFilter (p_func, p_expr, _) ->
            (* FIXME *)
            failwith "I don't know how  to take shape of a filter"


let shape st p =
    shape_v st @@ st_lookup st p


(* Index-vector to offset.  SHP and IDX are value vectors.  *)
let idx_to_offset shp idx =
    let rec rowmajor sprod res shp idx =
        match (shp,idx) with
        | [],[] ->
                res
        | (sh::shptl), (i::idxtl) ->
                rowmajor (sprod*sh) (res + i*sprod) shptl idxtl
        | _ -> failwith "different length"
    in
    let value_num_to_int v =
        ord_to_nat @@ value_num_to_ord v
    in
    let shp_numvec = List.rev @@ List.map value_num_to_int shp in
    let idx_numvec = List.rev @@ List.map value_num_to_int idx in
    rowmajor 1 0 shp_numvec idx_numvec


(* Number of dimensions in the array.
   We assume that the value is always finite (< w), but we use ordinal type to return
   the result. *)
let dimension st pa =
    let _, data = value_array_to_pair @@ shape st pa in
    int_to_ord @@ List.length data

(* Number of elements.  *)
let element_count st pa =
    let _, data = value_array_to_pair @@ shape st pa in
    let vres = List.fold_left value_num_mult (VNum one) @@ List.rev data in
    value_num_to_ord vres

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

let rec array_element_type_finite st ptrlst =
    match ptrlst with
    | [] -> true
    | p :: tl -> let v = st_lookup st p in
                 match v with
                 | VImap (_, _, _, _) -> false
                 | VFilter (_, _, _) -> false
                 | _ -> array_element_type_finite st tl

(* return the shape vector of the first element of the pointer list.  *)
let ptr_list_fst_shape st ptrlst =
    if ptrlst = [] then
        []
    else
        let _, shp_vec = value_array_to_pair (shape st (List.hd ptrlst)) in
        shp_vec


let ptr_binop st op p1 p2 =
    let v1 = st_lookup st p1 in
    let v2 = st_lookup st p2 in
    if not @@ value_is_num v1 then
        eval_err @@ sprintf "attempt to perform binary operation on non-number `%s'"
                            @@ value_to_str v1;
    if not @@ value_is_num v2 then
        eval_err @@ sprintf "attempt to perform binary operation on non-number `%s'"
                            @@ value_to_str v2;
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


let ptr_unary st op p1 =
    let v1 = st_lookup st p1 in
    match op with
    | OpShape -> shape st p1
    | OpIsLim -> if not @@ value_is_num v1 then
                    eval_err @@ sprintf "attempt to apply islim to `%s'" @@ value_to_str v1;
                 if ord_is_lim @@ value_num_to_ord v1 then VTrue else VFalse


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


(* Extract lb-ub pairs from the list of partitions as it is stored in
   in the VImap.  The `lb' and `ub' are lower bound and upper bound of
   a partition.  The type of `lb' and `ub' is a list of values.  *)
let vparts_to_pairs parts =
    List.map (fun p ->
          let ((alb, _, aub), _) = p in
          let _, lb = value_array_to_pair alb in
          let _, ub = value_array_to_pair aub in
          (lb, ub))
         parts


(* Check if partition (plb, pub) is within (lb, ub) bounds.  *)
let part_within_bounds lb ub plb pub =
    value_num_vec_le lb plb && value_num_vec_lt plb ub
    && value_num_vec_le lb pub && value_num_vec_le pub ub


(* Check if two partitons (p1_top, p1_bot) and (p2_top, p2_bot) intersect.
   The type of p1_top, p1_bot, p2_top, p2_bot is list of values.
   The function returns option type with the intersection area in case
   partitions do intersect.  *)
let part_intersect p1_top p1_bot p2_top p2_bot =
    let max a b = if value_num_compare a b = 1 then a else b
    in
    let min a b = if value_num_compare a b = -1 then a else b
    in
    let vec_elem_max v1 v2 = List.map2 (fun x y -> max x y) v1 v2
    in
    let vec_elem_min v1 v2 = List.map2 (fun x y -> min x y) v1 v2
    in

    let maxtop = vec_elem_max p1_top p2_top in
    let minbot = vec_elem_min p1_bot p2_bot in
    (*printf "--[part_intersect] maxtop = [%s], minbot = [%s]\n"
           (val_lst_to_str maxtop) (val_lst_to_str minbot) ;

    printf "--[part_intersect] ([%s], [%s]) and ([%s], [%s]) "
           (val_lst_to_str p1_top) (val_lst_to_str p1_bot)
           (val_lst_to_str p2_top) (val_lst_to_str p2_bot);*)
    if value_num_vec_lt maxtop minbot
       (* If the intersected area lies within both partitions.  *)
       && part_within_bounds p1_top p1_bot maxtop minbot
       && part_within_bounds p2_top p2_bot maxtop minbot
    then
    begin
        (*printf "do intersect\n";*)
        Some ((maxtop, minbot))
    end
    else
    begin
        (*printf "do not intersect\n";*)
        None
    end


(* cut (part_lb, part_ub) from the (lb_vec, ub_vec) *)
let part_split lb_vec ub_vec part_lb part_ub =
    (* take elements at position < pos from l1 and the rest from l2.  *)
    let takedrop x y pos =
        let xl, xr = list_split x pos in
        let yl, yr = list_split y pos in
        List.append xl yr
    in
    let upd_vec vec pos v =
        let l, r = list_split vec pos in
        List.append l (v :: (List.tl r))
    in
    let chk_empty s e =
        let chk = value_num_vec_lt s e in
        (* printf "---[chk_empty] [%s] < [%s] = [%s]\n"
               (val_lst_to_str s) (val_lst_to_str e) (if chk then "true" else "false");*)
        if chk then
            [(s, e)]
        else
            []
    in
    let splitpos lb_vec ub_vec part_lb part_ub pos =
        let s1 = takedrop part_lb lb_vec pos in
        let e1 = takedrop part_ub (takedrop part_lb ub_vec (pos+1)) pos in
        let s2 = upd_vec (takedrop part_lb lb_vec (pos+1)) pos (List.nth part_ub pos) in
        let e2 = takedrop part_ub ub_vec pos in
        (*let pb = (s1, e1) :: (s2, e2) :: [] in
        debug @@
        sprintf "--[update_imap_part] splitpos returns %s\n"
                @@ String.concat ", " @@ List.map (fun x -> let l, b = x in
                                                   sprintf "([%s], [%s])"
                                                   (val_lst_to_str l) (val_lst_to_str b))
                                         pb;
        pb*)

        List.append (chk_empty s1 e1) (chk_empty s2 e2)
    in
    List.flatten @@
    List.mapi (fun i v -> splitpos lb_vec ub_vec part_lb part_ub i) lb_vec


(* Check that partitions of an imap partition the entire shape of the imap.  *)
let check_parts_form_partition glb gub parts =
    let rec _intersect parts_to_cover parts =
        match parts with
        | [] ->
                parts_to_cover
        | (lb, ub) :: tl ->
                if part_within_bounds glb gub lb ub then
                    let parts_to_cover =
                    List.flatten @@
                    List.map (fun p ->
                              let plb, pub = p in
                              match part_intersect plb pub lb ub with
                              | None ->
                                      [p]
                              | Some ((intlb, intub)) ->
                                      part_split plb pub intlb intub)
                             parts_to_cover
                    in
                    (*printf "--[_intersect] prt = ([%s], [%s]), parts_to_cover = %s\n"
                           (val_lst_to_str lb) (val_lst_to_str ub)
                           (String.concat ", " @@ List.map (fun x -> let xlb, xub = x in
                                                            sprintf "([%s], [%s])"
                                                                    (val_lst_to_str xlb)
                                                                    (val_lst_to_str xub))
                                                           parts_to_cover);*)
                    _intersect parts_to_cover tl
                else
                    eval_err @@ sprintf "partition ([%s], [%s]) is not within ([%s], [%s])"
                                (val_lst_to_str lb) (val_lst_to_str ub)
                                (val_lst_to_str glb) (val_lst_to_str gub)
    in
    let remaining_parts =
        (* For imaps that generate arrays of zero shape, we don't need
           to add (glb, gub) as it will be empty partition.  *)
        let parts_to_cover =
            if value_num_vec_lt glb gub then [(glb, gub)] else []
        in
            _intersect parts_to_cover @@ vparts_to_pairs parts
    in remaining_parts = []

(* Check whether partitions in parts intersect amongst each other.
   The type of parts is (vgen * expr_or_ptr) list.  *)
let check_parts_intersect parts =
    let rec _check parts =
        match parts with
        | [] -> false
        | (lb, ub) :: tl ->
                let local_intersect =
                List.fold_left (fun res p ->
                                if res then
                                    res
                                else
                                    let plb, pub = p in
                                    match part_intersect lb ub plb pub with
                                    | None -> false
                                    | Some (_) -> true)
                               false
                               tl

                in
                if local_intersect then
                    local_intersect
                else
                    _check tl
    in
    _check @@ vparts_to_pairs parts

(* Split the `part_idx' partition of the imap at index `idx_vec'
   binding the value at `idx_vec' to ptr.  *)
let update_imap_part st imap_ptr idx_vec ptr =
    (* Remove partition #idx_part from parts and append parts1.  *)
    let replace parts idx_part parts1 =
        let l, r = list_split parts idx_part in
        List.append (List.append l (List.tl r)) parts1
    in

    let p1, p2, parts, env = value_imap_to_tuple @@ st_lookup st imap_ptr in
    (* We find partition here instead of using the memoized value as
       during recursive evaluation, the index of partition may change.  *)
    let part_idx, _ = find_partition parts idx_vec in
    let ((lb, x, ub), e) = List.nth parts part_idx in
    (* FIXME Here we can inspect `e' and if it is a pointer, we can avoid
             cutting partitions as it has been computed before.  This can
             happen due to recomputing the same value during the recursive
             call.  *)
    (* split partitions at index `idx_vec'  *)
    let _, lb_vec = value_array_to_pair lb in
    let _, ub_vec = value_array_to_pair ub in
    (* Join partitions from the splitpos.  *)
    let inc_idx_vec = List.map (fun x -> value_num_add x (VNum (one))) idx_vec in
    let part_bounds = part_split lb_vec ub_vec idx_vec inc_idx_vec in
    (* Create a list of generator-ptr_expr pairs with expression `e'.  *)
    let parts1 = List.map (fun g -> let l, u = g in
                                    ((mk_vector l, x, mk_vector u), e)) part_bounds in
    (* Add 1-element partition for the idx.  *)
    let elem_part = ((mk_vector idx_vec, x, mk_vector inc_idx_vec), EPptr (ptr)) in
    let parts' = replace parts part_idx (elem_part::parts1) in
    let imap' = VImap (p1, p2, parts', env) in
    debug @@
    sprintf "--[update_imap_part] updating imap\n%s\n into\n%s\n\n"
            (value_to_str @@ st_lookup st imap_ptr) (value_to_str imap');
    st_update st imap_ptr imap'


let add_fresh_val_as_result st v =
    let p = fresh_ptr_name () in
    let st = st_add st p v in
    (st, p)


let lexi_next v lb ub =
    let rec _upd v lb ub carry =
        match v, lb, ub with
        | [], [], [] ->
                []
        | (v::vt), (l::lt), (u::ut) ->
                let v' = value_num_add v carry in
                if v' = u then
                    l :: (_upd vt lt ut @@ mk_int_value 1)
                else
                    v' :: vt
        | _ -> failwith "lexi_next"
    in

    (* For the "last" index (ub-1) we just increase the last element by one.  *)
    if List.map (fun x -> value_num_add x @@ mk_int_value 1) v = ub then
        let vl, _ = list_split v (List.length v - 1) in
        let _, ubr = list_split ub (List.length ub - 1) in
        List.append vl ubr
    else
        List.rev @@
        _upd (List.rev v) (List.rev lb) (List.rev ub) @@ mk_int_value 1


let rec eval st env e =
    match e with
    | EFalse ->
            add_fresh_val_as_result st @@ mk_false_value

    | ETrue ->
            add_fresh_val_as_result st @@ mk_true_value

    | ENum (o) ->
            add_fresh_val_as_result st @@ mk_ord_value o

    | EVar (x) ->
            (st, (env_lookup env x))

    | EArray (lst) ->
            (* evaluate all the elements in the list sequentially.  *)
            let st, ptrlst = eval_expr_lst st env lst in
            (* check that the shape of the elements is the same.  *)
            if not @@ array_element_shape_valid st ptrlst then
                eval_err @@ sprintf "elements of the array `%s' are of different shape"
                            @@ expr_to_str e;
            if not @@ array_element_type_finite st ptrlst then
                eval_err @@ sprintf "elements of the array `%s' have imap/filters"
                            @@ expr_to_str e;
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
            add_fresh_val_as_result st @@ mk_array_value shp data

    | ELambda (_, _) ->
            add_fresh_val_as_result st @@ mk_closure_value e env

    | EApply (e1, e2) ->
            let (st, p1) = eval st env e1 in
            let (st, p2) = eval st env e2 in
            if value_is_selectable (st_lookup st p1) then
                let (dobj, sobj) = value_array_to_pair @@ shape st p1 in
                let (didx, sidx) = value_array_to_pair @@ shape st p2 in
                let idx_val = st_lookup st p2 in

                (* Check that the index is an array.  *)
                if not @@ value_is_array idx_val then
                    eval_err @@ sprintf "the index in `%s' selection must evaluate to an array"
                                         @@ expr_to_str e;

                (* Check that shape of the index matches the shape of the object.  *)
                if dobj <> sidx then
                    eval_err @@ sprintf "shapes of lhs and index do not match in `%s' selection [%s] <> [%s]"
                                        (expr_to_str e) (val_lst_to_str dobj) (val_lst_to_str sidx);

                (* Check that the index is within the shape.  *)
                let _, idx_data = value_array_to_pair idx_val in
                if not @@ value_num_vec_lt idx_data sobj then
                    eval_err @@ sprintf "out of bound access in `%s' selection"
                                        @@ expr_to_str e;

                eval_selection st env p1 p2
            else
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
                | _ -> eval_err @@ sprintf "predicate of `%s' evaluates to `%s' (true/false expected)"
                                           (expr_to_str e) (value_to_str v)
            end

    | ELetRec (var, e1, e2) ->
            let pname = fresh_ptr_name () in
            let (st, p1) = eval st (env_add env var pname) e1 in
            let st = update_letrec_ptr st pname p1 in
            eval st (env_add env var p1) e2

    | EImap (e1, e2, ge_lst) ->
            let (st, p1) = eval st env e1 in
            let (st, p2) = eval st env e2 in
            let shp_out_vec, data_out_vec = value_array_to_pair @@ st_lookup st p1 in
            let st, vg_expr_lst = eval_gen_expr_lst st env shp_out_vec ge_lst in
            let lb = List.map (fun x -> mk_int_value 0) data_out_vec in
            (* Throw away all the empty partitions. *)
            let vg_expr_lst = List.flatten @@
                              List.map (fun x ->
                                        let ((lb, x, ub), ep) = x in
                                        let _, lb_vec = value_array_to_pair lb in
                                        let _, ub_vec = value_array_to_pair ub in
                                        if value_num_vec_lt lb_vec ub_vec then
                                            [((lb, x, ub), ep)]
                                        else begin
                                            eval_warn @@
                                            sprintf "partition ([%s], [%s]) of the imap `%s' is empty"
                                                    (val_lst_to_str lb_vec) (val_lst_to_str ub_vec)
                                                    (expr_to_str e);
                                            []
                                        end) vg_expr_lst in
            if not @@ check_parts_form_partition
                            lb
                            data_out_vec
                            vg_expr_lst then
                eval_err @@ sprintf "partitions of `%s' do not fill the specified imap range ([%s], [%s])"
                                    (expr_to_str e) (val_lst_to_str lb) (val_lst_to_str data_out_vec);
            if check_parts_intersect vg_expr_lst then
                eval_err @@ sprintf "partitions of `%s' are not disjoint"
                                    (expr_to_str e);

            let shp_in_vec, data_in_vec = value_array_to_pair @@ st_lookup st p2 in
            if  !finite_imap_strict_on
                && List.for_all (fun x -> (value_num_compare x (VNum omega)) = -1)
                                  (List.append data_out_vec data_in_vec) then
                (* FIXME It is not good enough to check that the shape is finite,
                     we would also need to check that the structure is not
                     recursive.  *)
                eval_strict_imap st env p1 p2 vg_expr_lst
            else
                add_fresh_val_as_result st @@ mk_imap_value p1 p2 vg_expr_lst env

    | EReduce (func, neut, a) ->
            let (st, pfunc) = eval st env func in
            let (st, pneut) = eval st env neut in
            let (st, pa) = eval st env a in
            if not @@ value_is_closure @@ st_lookup st pfunc then
                eval_err @@ sprintf "expected function as first argument of `%s'"
                                    @@ expr_to_str e;
            if not @@ value_is_selectable @@ st_lookup st pa then
                eval_err @@ sprintf "expected selectable object as third argument of `%s'"
                                    @@ expr_to_str e;
            if dimension st pa = zero then
                eval_err @@ sprintf "expected dimension of third argument of `%s' to be greater than 0"
                                    @@ expr_to_str e;
            eval_reduce st env pfunc pneut pa

           (* FIXME *)
    | _ -> failwith (sprintf "I don't know how to evaluate `%s'" (expr_to_str e))


and eval_bin_app st env p_func p_arg1 p_arg2 msg =
    try
        eval st
             (env_add (env_add (env_add env "__x0" p_arg1) "__x1" p_arg2) "__func" p_func)
             (EApply (EApply (EVar ("__func"), EVar ("__x0")), EVar ("__x1")))
    with
        EvalFailure _ ->
            eval_err msg


(* Evaluate selection p_obj at p_idx and emit msg in case
   evaluation throws an exception.  *)
and eval_obj_sel st env p_obj p_idx msg =
    try
        eval st
             (env_add (env_add env "__idx" p_idx) "__obj" p_obj)
             (EApply (EVar ("__obj"), EVar ("__idx")))
    with
        EvalFailure _ ->
            eval_err msg


and eval_selection st env p1 p2 =
    let v1 = st_lookup st p1 in
    let idx_shp_vec, idx_data_vec = value_array_to_pair (st_lookup st p2) in
    match v1 with
    | VNum (_) ->
            (st, p1)
    | VArray (shp_vec, data_vec) ->
            let offset = idx_to_offset shp_vec idx_data_vec in
            let v = List.nth data_vec offset in
            add_fresh_val_as_result st v

    | VImap (po, pi, parts, env') ->
            let vo_shp, vo_data = value_array_to_pair @@ st_lookup st po in
            let vi_shp, _ = value_array_to_pair @@ st_lookup st pi in
            let idx_o, idx_i = list_split idx_data_vec (List.length vo_data) in
            debug @@
            sprintf "--[imap-sel] splitting [%s] at %d = ([%s], [%s])"
                    (val_lst_to_str idx_data_vec) (List.length vo_data)
                    (val_lst_to_str idx_o) (val_lst_to_str idx_i);
            (* find partition *)
            let part_idx, (vg, e) = find_partition parts idx_o in
            (* extract or evaluate the expression at index idx_o.  *)
            let (st, ptr_out) = match e with
            (* if value at idx_o is already computed  *)
            | EPptr (p) ->
                    (st, p)
            (* if value at idx_o is not computed  *)
            | EPexpr (e) ->
                    let _, var, _ = vg in
                    let st, idx_o_ptr = add_fresh_val_as_result st @@ mk_array_value vo_shp idx_o in
                    let st, p = eval st (env_add env' var idx_o_ptr) e in
                    (* split partition and update imap *)
                    if !memo_on then
                        let st = update_imap_part st p1 idx_o p in
                        (st, p)
                    else
                        (st, p)
            in
            (* make selection *)
            debug @@
            sprintf "--[imap-sel] inner imap selection: `%s' at [%s]"
                    (value_to_str @@ st_lookup st ptr_out) (val_lst_to_str idx_i);
            let st, pidx = add_fresh_val_as_result st @@ mk_array_value vi_shp idx_i in
            eval_obj_sel st env' ptr_out pidx
                         @@ sprintf "failed to perform inner imap selection `%s' at [%s]"
                                    (value_to_str @@ st_lookup st ptr_out) (val_lst_to_str idx_i)

    | _ ->
            (* FIXME *)
            failwith "I'm too stupid to make selection of filters"


(* evaluate a list of expressions propagating storage at every recursive call;
   return a tuple: (last storage, list of pointers)  *)
and eval_expr_lst st env lst =
    match lst with
    | [] ->
            (st, [])
    | e :: tl ->
            let st, p = eval st env e in
            let st, res = eval_expr_lst st env tl in
            (st, p :: res)


(* evaluate gen-expr list into vgen-expr list  *)
and eval_gen_expr_lst st env idx_shp_vec ge_lst =
    match ge_lst with
    | [] ->
            (st, [])
    | ((lb, var, ub) as g, e) :: tl ->
            let st, p1 = eval st env lb in
            let st, p2 = eval st env ub in
            let v1 = st_lookup st p1 in
            let v2 = st_lookup st p2 in
            if not @@ value_is_array v1 then
                eval_err @@ sprintf "lower bound of generator `%s' is not array"
                                    @@ gen_to_str g;
            if shape_v st v1 <> mk_vector idx_shp_vec then
                eval_err @@ sprintf "wrong shape for lower bound of `%s: %s-element vector expected"
                                    (gen_to_str g) (val_lst_to_str idx_shp_vec);
            if not (value_is_array v2) then
                eval_err (sprintf "upper bound of generator `%s' is not array"
                                  (gen_to_str g));
            if shape_v st v2 <> mk_vector idx_shp_vec then
                eval_err @@ sprintf "wrong shape for upper bound of `%s: %s-element vector expected"
                                    (gen_to_str g) (val_lst_to_str idx_shp_vec);
            let st, res = eval_gen_expr_lst st env idx_shp_vec tl in
            (st, ((v1, var, v2), EPexpr (e)) :: res)


(* evaluate reduce, arguments are checked:
   - pfunc is a closure
   - pa is selectable
   - dim (pa) > 0   *)
and eval_reduce st env pfunc pneut pa =
    (* Evaluate application of p_func to p_arg1 p_arg2 and emit msg in case
       evaluation throws an exception.  *)
    let rec reduce_lst st lst p_res =
        match lst with
        | [] ->
                (st, p_res)
        | v :: tl ->
                let p_el = fresh_ptr_name () in
                let st = st_add st p_el v in
                let st, p_res' =
                    eval_bin_app
                        st env pfunc p_res p_el
                        @@ sprintf "evaluation of reduction step (%s) (%s) (%s) failed"
                                   (value_to_str @@ st_lookup st pfunc)
                                   (value_to_str @@ st_lookup st p_res)
                                   (value_to_str v)
                in reduce_lst st tl p_res'
    in
    let rec reduce_selectable st lb ub idx p_res =
        if not @@ value_num_vec_lt idx ub then
            (st, p_res)
        else
            (* Make selection at `idx' *)
            let p_idx = fresh_ptr_name () in
            let st = st_add st p_idx @@ mk_vector idx in
            let st, p_el = eval_obj_sel st env pa p_idx
                           @@ sprintf "evaluation of reduction failed at selection (%s) (%s)"
                                      (value_to_str @@ st_lookup st pa)
                                      (value_to_str @@ st_lookup st p_idx) in
            (* Reduce current result and the selected element.  *)
            let st, p_res' =
                    eval_bin_app
                        st env pfunc p_res p_el
                        @@ sprintf "evaluation of reduction step (%s) (%s) (%s) failed"
                                   (value_to_str @@ st_lookup st pfunc)
                                   (value_to_str @@ st_lookup st p_res)
                                   (value_to_str @@ st_lookup st p_el)
            in reduce_selectable st lb ub (lexi_next idx lb ub) p_res'
    in

    let va = st_lookup st pa in
    match va with
    | VArray (_, data_vec) ->
            reduce_lst st data_vec pneut
    | _ ->
            let _, shp = value_array_to_pair @@ shape st pa in
            let lb = List.map (fun x -> mk_int_value 0) shp in
            reduce_selectable st lb shp lb pneut


and eval_strict_imap st env p_out p_inner parts =
    let out_idx_hash: (value list,  string) Hashtbl.t = Hashtbl.create 100 in
    let out_shp_v, out_v = value_array_to_pair @@ st_lookup st p_out in
    let in_shp_v, in_v = value_array_to_pair @@ st_lookup st p_inner in

    let in_hash ht ptr =
        try Hashtbl.find ht ptr; true with Not_found -> false
    in
    let rec eval_idxes st env glb gub idx parts res =
        (*printf "--- eval-idxes: idx = [%s]\n" (val_lst_to_str idx);*)
        if not @@ value_num_vec_lt idx gub then
            res
        else
            let idx_o, idx_i = list_split idx (List.length out_v) in
            (*printf "--- eval-idxes: idx_o = [%s], idx_i = [%s]\n"
                   (val_lst_to_str idx_o) (val_lst_to_str idx_i);*)
            (* find partition *)
            let part_idx, (vg, e) = find_partition parts idx_o in
            (* extract or evaluate the expression at index idx_o.  *)
            let (st, ptr_out) = match e with
            (* if value at idx_o is already computed  *)
            | EPptr (p) ->
                    (st, p)
            (* if value at idx_o is not computed  *)
            | EPexpr (e) ->
                    if in_hash out_idx_hash idx_o then
                    begin
                        (*printf "--- found [%s] in hash\n" (val_lst_to_str idx_o);*)
                        (st, Hashtbl.find out_idx_hash idx_o)
                    end
                    else
                       let _, x, _ = vg in
                       let st, p_idx_o = add_fresh_val_as_result st @@ mk_array_value out_shp_v idx_o in
                       let st, p = eval st (env_add env x p_idx_o) e in
                       Hashtbl.add out_idx_hash idx_o p;
                       (st, p)
            in
            debug @@
            sprintf "--[eval-strict-imap] inner imap selection: `%s' at [%s]"
                    (value_to_str @@ st_lookup st ptr_out) (val_lst_to_str idx_i);
            let st, p_idx_i = add_fresh_val_as_result st @@ mk_array_value in_shp_v idx_i in
            let st, p_el = eval_obj_sel st env ptr_out p_idx_i
                               @@ sprintf "evaluation of strict imap failed at selection (%s) (%s)"
                                          (value_to_str @@ st_lookup st ptr_out)
                                          (value_to_str @@ st_lookup st p_idx_i) in
            let v = st_lookup st p_el in
            eval_idxes st env glb gub (lexi_next idx glb gub) parts (v :: res)

    in
    let gub = List.append out_v in_v in
    let glb = List.map (fun x -> mk_int_value 0) gub in
    let data = eval_idxes st env glb gub glb parts [] in
    add_fresh_val_as_result st (mk_array_value gub @@ List.rev data)

