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

open Ast


module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

let rec free_vars vars e =
    match e with
    | {expr_kind = EFalse }
    | {expr_kind = ETrue }
    | {expr_kind = ENum _ } ->
            StringSet.empty
    | {expr_kind = EVar x } ->
            if StringSet.mem x vars then
                StringSet.empty
            else
                StringSet.add x StringSet.empty

    | {expr_kind = EArray lst } ->
            let vslst = List.map (fun e -> free_vars vars e) lst in
            List.fold_left (fun vars vs ->
                            StringSet.union vars vs)
                           StringSet.empty
                           vslst

    | {expr_kind = EBinOp (_, e1, e2) }
    | {expr_kind = EApply (e1, e2) }
    | {expr_kind = ESel (e1, e2) }
    | {expr_kind = EFilter (e1, e2) } ->
            let vs1 = free_vars vars e1 in
            let vs2 = free_vars vars e2 in
            StringSet.union vs1 vs2

    | {expr_kind = EUnary (_, e1) } ->
            free_vars vars e1

    | {expr_kind = ELambda (x, e) } ->
            free_vars (StringSet.add x vars) e

    | {expr_kind = ECond (e1, e2, e3) }
    | {expr_kind = EReduce (e1, e2, e3) } ->
            let vs1 = free_vars vars e1 in
            let vs2 = free_vars vars e2 in
            let vs3 = free_vars vars e3 in
            StringSet.union (StringSet.union vs1 vs2) vs3

    | {expr_kind = ELetRec (x, e1, e2)} ->
            let vs1 = free_vars (StringSet.add x vars) e1 in
            let vs2 = free_vars (StringSet.add x vars) e2 in
            StringSet.union vs1 vs2

    | {expr_kind = EImap (e1, e2, gelst)} ->
            let vs1 = free_vars vars e1 in
            let vs2 = free_vars vars e2 in
            let vlst = List.map (fun ge ->
                                 let (e1, x, e2), body = ge in
                                 let vs1' = free_vars vars e1 in
                                 let vs2' = free_vars vars e2 in
                                 let vs3' = free_vars (StringSet.add x vars) body in
                                 StringSet.union (StringSet.union vs1' vs2') vs3')
                                gelst in
            let vs3 = List.fold_left StringSet.union StringSet.empty vlst in
            StringSet.union (StringSet.union vs1 vs2) vs3

let print_free_vars e =
    Printf.printf "Free vars of expr %s\n" (Print.expr_to_str e);
    StringSet.iter (fun x -> Printf.printf "%s, " x)
                   (free_vars StringSet.empty e);
    Printf.printf "\n"


let rec wrap_lambda lst e =
    match lst with
    | [] -> e
    | x :: t -> Ast.mk_elambda x @@ wrap_lambda t e

let rec lst_print l =
    match l with
    | [] -> ""
    | x :: xs -> Printf.sprintf "%s %s" x (lst_print xs)

let xprint var varlist_expr =
    let varlist, expr = varlist_expr in
    Printf.printf "%s: Λ%s.%s\n" var (lst_print varlist) (Print.expr_to_str expr)

let xprint1 var varlist_expr =
    let varlist, expr = varlist_expr in
    Printf.printf "letrec %s = %s in\n" var @@ Print.expr_to_str (wrap_lambda varlist expr)

let print_mapping m =
    StringMap.iter xprint1 m



let fun_name_count = ref 0
let var_name_count = ref 0

(* Generate a fresh function name.  *)
let fresh_fun_name () =
    fun_name_count := !fun_name_count + 1;
    Printf.sprintf "__f%d" !fun_name_count

(* Generate a fresh function name.  *)
let fresh_var () =
    var_name_count := !var_name_count + 1;
    Printf.sprintf "x%d" !var_name_count


(* FIXME there should be the same function further down.  *)
let rec mk_app fvlist body =
    match fvlist with
    | x :: [] -> mk_eapply body (mk_evar x)
    | x :: xs -> mk_app xs (mk_eapply body (mk_evar x))
    | [] -> body


let rec flat_lambda e =
    match e with
    | { expr_kind = ELambda (x, e') } ->
            let xs, e' = flat_lambda e' in
            (x::xs, e')
    | _ -> ([], e)


let rec lift ms e =
    let m, vl = ms in
    match e with
    | {expr_kind = ELambda (x1, e1) } ->
            let xs, e1 = flat_lambda e in
            let fv = free_vars StringSet.empty e in
            let fvlist = StringSet.fold (fun var lst -> var :: lst) fv [] in

            let (m, _), e1' = lift (m, []) e1 in

            let fresh = fresh_fun_name () in
            let m = StringMap.add fresh ((fvlist @ xs),  e1') m  in
            (* FIXME location. *)
            ((m, vl), mk_app (fvlist) (mk_evar fresh))

    | _ ->
            Traversal.topdown lift ms e


let rec lift1 m e =
    match e with
    | {expr_kind = ELambda (x1, e1) } ->
            let fv = free_vars StringSet.empty e in
            if StringSet.cardinal fv = 0 then
                let m, e1' = lift1 m e1 in
                Printf.printf "=1= lifting body %s into %s\n" (Print.expr_to_str e1) (Print.expr_to_str e1');
                (* XXX this avoids eta-extended functions, but maybe they can be useful.  *)
                match e1' with
                | {expr_kind = EApply (e', {expr_kind = EVar (x1)}) } ->
                        (m, e')
                | _ ->
                    let fresh = fresh_fun_name () in
                    let m = StringMap.add fresh ([x1], e1') m
                    (* FIXME location. *)
                    in (m, mk_evar fresh)
            else
                let rec mk_app fvlist body =
                    match fvlist with
                    | x :: [] -> mk_eapply body (mk_evar x)
                    | x :: xs -> mk_app xs (mk_eapply body (mk_evar x))
                    | [] -> failwith "no free vars"
                in
                let m, e1' = lift1 m e1 in
                Printf.printf "=2= lifting body %s into %s\n" (Print.expr_to_str e1) (Print.expr_to_str e1');
                let fresh = fresh_fun_name () in
                let fvlist = StringSet.fold (fun var lst -> var :: lst) fv [] in
                Printf.printf "=2= fvlist = %s\n" (lst_print fvlist);

                let m = StringMap.add fresh ((List.append fvlist [x1]),  e1') m  in
                (*let fresh1 = fresh_fun_name () in
                let m = StringMap.add fresh1 (fvlist, (mk_app fvlist (mk_evar fresh))) m in*)
                (* FIXME location. *)
                (m, mk_app fvlist (mk_evar fresh))
    | _ ->
            Traversal.topdown lift1 m e



(*
 * FIXME this doesn't quite work, as we don't handle the case
 *       when a substituted expression contains free variables
 *       x -> (y+z).
 *
 * Check that we do not bring new free variables by a
 * substitution.  For exampple, we want to avoid:
 *     (x + y)[x/y] -> y + y
 * to check this we do the following:
 *
 * FV(e)   Substs   Res
 *  x       y->x    x->x
 *  y       z->s    y->x
 *  z               z->s
 *
 * so we check that in the resulting mapping, there
 * are no duplicates.
 *)
let subst_is_sane (m: Ast.expr StringMap.t) e =
    let fv = free_vars StringSet.empty e in
    let res = StringSet.fold
                 (fun x l ->
                  if StringMap.mem x m then
                     let e = StringMap.find x m in
                     match Ast.expr_get_var_name e with
                     | Some (x') -> x'::l
                     | _ -> l
                  else
                      x :: l)
                  fv
                  [] in

    List.length (res) = (List.length @@ List.sort_uniq compare res)


(*
 * M is a tuple (x, e2) where x is a variable and e2 is expression.
 * The function substitues all free occurences of `x' in `e1' with e2.
 *)
let rec subst (m: Ast.expr StringMap.t) e =
    assert (subst_is_sane m e);
    if StringMap.cardinal m = 0 then
        (m, e)
    else
    match e with
    | { expr_kind = EVar x } ->
            if StringMap.mem x m then
                (m, StringMap.find x m)
            else
                (m, e)

    | { expr_kind = ELambda (x, e1) } ->
            let m1 = if StringMap.mem x m then
                        StringMap.remove x m
                     else
                        m in
            let _, e1 = subst m1 e1 in
            (m, mk_elambda ~loc:e.loc x e1)

    | { expr_kind = ELetRec (x, e1, e2) } ->
            let m1 = if StringMap.mem x m then
                        StringMap.remove x m
                     else
                         m in
            let _, e1 = subst m1 e1 in
            let _, e2 = subst m1 e2 in
            (m, mk_eletrec ~loc:e.loc x e1 e2)

    | {expr_kind = EImap (e1, e2, gelst) } ->
            let _, e1 = subst m e1 in
            let _, e2 = subst m e2 in
            let rec iter gelst =
                match gelst with
                | [] -> []
                | g :: gs ->
                        let (lb, x, ub), eb = g in
                        let _, lb = subst m lb in
                        let _, ub = subst m ub in
                        let m1 =
                            if StringMap.mem x m then
                                StringMap.remove x m
                            else m in
                        let _, eb = subst m1 eb in
                        let gs = iter gs in
                        ((lb, x, ub), eb) :: gs
            in
            let gelst = iter gelst in
            (m, mk_eimap e1 e2 gelst ~loc:e.loc)

    | _ -> Traversal.topdown subst m e


(*
 * Gets rid of letrecs that bind a constant or a variable
 * by propagating it into the body.
 *)
let rec propagate () e =
    match e with
    | {expr_kind = ELetRec (x1, e1, e2) } ->
            if (match e1.expr_kind with
                | EFalse | ETrue | EVar _ | ENum _  -> true
                | _ -> false)
            then
                let subst_map = StringMap.add x1 e1 StringMap.empty in
                let _, e2 = subst subst_map e2 in
                let (), e2 = propagate () e2 in
                ((), e2)
            else
                let (), e1' = propagate () e1 in
                let (), e2' = propagate () e2 in
                ((), mk_eletrec x1 e1' e2')
    | _ ->
            Traversal.topdown propagate () e



let print_expr_lst lst =
    Printf.printf "--- lst: %s\n\n" @@ Print.expr_to_str @@ mk_earray lst

let lst_to_eapply lst =
    let open List in
    if (length lst = 1) then
        hd lst
    else
        let e1 = hd lst in
        let e2 = hd @@ tl lst in
        List.fold_left (fun f arg -> mk_eapply f arg)
                        (mk_eapply e1 e2)
                        (tl @@ tl lst)

let rec flatten_apply e =
    match e with
    | { expr_kind = EApply (e1, e2) } ->
            flatten_apply e1 @ [e2]
    | _ -> [e]

(* Returns Some(var) in case e is EVar(var) or None otherwise.  *)
let expr_is_global_fun m e =
    let opt_varname = expr_get_var_name e in
    match opt_varname with
    | Some (x) ->
        if StringMap.mem x m then Some (x) else None
    | None -> None


let rec propagate_glob m e =
    match e with
    | {expr_kind = ELetRec (x1, e1, e2) } ->
            let subst_map = StringMap.add x1 e1 StringMap.empty in
            if None = expr_is_global_fun m e1
               && subst_is_sane subst_map e2 then 
                let _, e2 = subst subst_map e2 in
                let m, e2 = propagate_glob m e2 in
                (m, e2)
            else
                let m, e1' = propagate_glob m e1 in
                let m, e2' = propagate_glob m e2 in
                (m, mk_eletrec x1 e1' e2')
    | _ ->
            Traversal.topdown propagate_glob m e



(*
 * XXX Here we assume that global functions are not shaddowed by
 *     any local bindings.  If they are, we did a poor job at
 *     lifting time.
 *
 * Computes a set of global functions that are reachable form
 * the expression e.
 *)
let rec reachable_funs ms e =
    let m, s = ms in
    match e with
    | { expr_kind = EVar (x) } ->
            if StringSet.mem x s then
                (ms, e)
            else if StringMap.mem x m then
                let s = StringSet.add x s in
                let args, body = StringMap.find x m in
                let ms, _ = reachable_funs (m, s) body in
                (ms, e)
            else
                (ms, e)

    | _ -> Traversal.topdown reachable_funs ms e




(*
 * Lifts recursive application within the letrec into a
 * function definition.  For example, for we replace an
 * expression like:
 *      letrec f = __f x f z in ...
 *
 * with
 *      letrec f = __f' x z where
 *
 * where
 *      __f' x z = __f x (__f x) z
 *)
let rec resolve_letrecs (m: (string list * Ast.expr) StringMap.t) e =
    let rec upd_args m l =
        match l with
        | h :: t ->
                let (m, h) = resolve_letrecs m h in
                let m, t = upd_args m t in
                (m, h :: t)
        | [] -> (m, [])
    in
    let rec split_lst l m res =
        let left, right = res in
        match (l, m) with
        | ([], []) -> res
        | (h::hs, m::ms) ->
                if m then
                    (left, h::hs)
                else
                    split_lst hs ms (left @ [h], right)
        | _ -> failwith "shouldn't happen"
    in
    let rec mkargs lst n =
        match lst with
        | [] -> []
        | h::t -> let x = fresh_var () in x :: (mkargs t (n+1))
    in
    match e with
    | { expr_kind = ELetRec (x, { expr_kind = EApply (e1, e2) }, e3) } ->
            let applst = flatten_apply e1 @ [e2] in
            let m, applst = upd_args m applst in
            let f = List.hd applst in
            (*Printf.printf "--- resolving letrec %s = " x;
            print_expr_lst applst;*)
            let m, applst = match expr_is_global_fun m f with
            | Some (fname) ->
                    (*let fparams, fbody = StringMap.find fname m in*)
                    let fargs = List.tl applst in
                    let mask = List.map (fun e ->
                                         match e with
                                         | { expr_kind = EVar (x') } ->
                                                 x = x'
                                         | _ -> false) fargs in

                    if List.exists (fun t -> t) mask then
                        (* split fargs into two lists according to mask *)
                        let largs, rargs = split_lst fargs mask ([], []) in
                        let rargs = List.tl rargs in

                        let lparams = mkargs largs 1 in
                        let rparams = mkargs rargs 1 in


                        let newname = fresh_fun_name () in
                        let newbody = lst_to_eapply
                                      @@ [mk_evar fname]
                                         @ (List.map mk_evar lparams)
                                         @ [lst_to_eapply @@ [mk_evar newname] @ (List.map mk_evar lparams)]
                                         @ (List.map mk_evar rparams) in
                        let m = StringMap.add newname (lparams @ rparams, newbody) m in
                        (m, [mk_evar newname] @ largs @ rargs)

                    else (m, applst)
            | None ->
                    (m, applst)
            in
            assert (List.length applst >= 1);
            print_expr_lst applst;
            let app = lst_to_eapply applst in
            (m, mk_eletrec x app e3)

    | _ ->  Traversal.topdown resolve_letrecs m e


(* XXX Should we put it into a module?  *)
type pattern = {
    f1: string;
    params: string list;
    f2: string;
    f3: string
}

let print_pat pat =
    let params_str =
        if pat.params = [] then ""
        else (Print.expr_to_str @@ lst_to_eapply @@ List.map mk_evar pat.params)
    in
    Printf.printf "pat: %s %s %s -> %s\n"
                  pat.f1 params_str pat.f2 pat.f3


let print_pats pats =
    List.fold_left (fun () pat -> print_pat pat) () pats

let newpat_and_replace m applst =
    let rec split lst el =
        match lst with
        | h::t ->
                if Ast.cmp_ast_noloc h el then
                    (0, [], h, t)
                else
                    let n, pairs, f, tl = split t el in
                    let x = Printf.sprintf "__x%d" (n+1) in
                    (n+1, (x,h)::pairs, f,  tl)

        | [] -> failwith "element not found"
    in

    match expr_is_global_fun m (List.hd applst) with
    | Some (f1_name) ->
        begin
            let applst = List.tl applst in
            try
                let f2 = List.find (fun e -> expr_is_global_fun m e <> None) applst in
                let _, pairs, f2, rargs = split applst f2 in
                let f2_name = match expr_get_var_name f2 with
                              | Some (x) -> x | None -> failwith "can't be" in
                let params, fargs = List.split pairs in
                let f3_name = fresh_fun_name () in
                let pat = {f1=f1_name; f2=f2_name; params=params; f3=f3_name} in
                let new_applst = [mk_evar f3_name] @ fargs @ rargs in
                Some (pat, new_applst)
            with
                Not_found -> None
        end
    | _ -> None

let apply_pat m pat applst =
    let rec split lst n =
        match (n, lst) with
        | (0, h::t) ->
                ([], h, t)
        | (n, h::t) ->
                let l, m, r = split t (n-1) in
                (h::l, m ,r)
        | _ -> failwith "can't happen"
    in

    (*Printf.printf "--- trying to match ";
    print_pat pat;
    Printf.printf "--- with %s\n" (Print.expr_to_str @@ lst_to_eapply applst);*)
    let f = List.hd applst in
    let applst =
    match expr_is_global_fun m f with
    | Some (f1_name) when f1_name = pat.f1 ->
            let argc = List.length pat.params in
            if List.length applst >= argc + 2 then
                let args, f2, rargs = split (List.tl applst) argc in
                match expr_is_global_fun m f2 with
                | Some (f2_name) when f2_name = pat.f2 ->
                        [mk_evar pat.f3] @ args @ rargs
                | _ -> applst
            else
                applst
    | _ -> applst
    in
    (*Printf.printf "--- res %s\n\n" (Print.expr_to_str @@ lst_to_eapply applst);*)
    applst

let pat_in_pats pat pats =
    try
        let _ = List.find (fun p ->
                           p.f1 = pat.f1
                           && p.f2 = pat.f2
                           && (List.length p.params) = (List.length pat.params))
                   pats in
        true
    with
        Not_found -> false

(*
 * Find a pattern like
 *      __f e1 e2 __g
 *
 * and abstract it away into new function that is defined as
 *      __f' x1 x2 = __f x1 x2 __g
 *
 * replace the original application with __f' and keep the
 * pattern for further substitutions.
 *)

let rec resolve_fun_app mpats e =
    let rec upd_args mpats l =
        match l with
        | h :: t ->
                let (mpats, h) = resolve_fun_app mpats h in
                let mpats, t = upd_args mpats t in
                (mpats, h :: t)
        | [] -> (mpats, [])
    in
    match e with
    | { expr_kind = EApply (e1, e2) } ->
            let applst = flatten_apply e in
            let (m, pats), applst = upd_args mpats applst in
            (* Apply existing patterns first.  *)
            (*let applst = apply_pats m pats applst in*)
            let applst, m, pats =
                match newpat_and_replace m applst with
                | Some (pat, applst)
                  when not @@ pat_in_pats pat pats ->
                        (* Add a new function *)
                        let fbody = lst_to_eapply
                                    @@ [mk_evar pat.f1]
                                       @ (List.map mk_evar pat.params)
                                       @ [mk_evar pat.f2] in
                        let m = StringMap.add pat.f3 (pat.params, fbody) m in
                        let pats = pat :: pats in
                        (applst, m, pats)

                | _ ->
                        (applst, m, pats)

            in ((m, pats), lst_to_eapply applst)

    | _ ->  Traversal.topdown resolve_fun_app mpats e


let rec apply_pats mpats e =
    let rec upd_args mpats l =
        match l with
        | h :: t ->
                let (mpats, h) = apply_pats mpats h in
                let mpats, t = upd_args mpats t in
                (mpats, h :: t)
        | [] -> (mpats, [])
    in
    match e with
    | { expr_kind = EApply (e1, e2) } ->
            let applst = flatten_apply e in
            let (m, pats), applst = upd_args mpats applst in
            let applst = List.fold_left
                         (fun applst pat -> apply_pat m pat applst)
                         applst pats in
            ((m,pats), lst_to_eapply applst)

    | _ ->  Traversal.topdown apply_pats mpats e


(*
 * For a given function F that is defined like this:
 *      F a b c = G e1 e2
 *
 * where G is a global function defined like:
 *      G x y z = e
 *
 * partially apply G in F as:
 *      F a b c = Λ z. e[e1/x][e2/y]
 *
 * and rewrite this into:
 *      F a b c z = e[e1/x][e2/y]
 *)
let uneta m fname =
    let rec split ps args =
        match (ps, args) with
        | ([], aa) -> ([], [], aa)
        | (pp, []) -> ([], pp, [])
        | (h1::t1, h2::t2) -> let (pairs, remps,  remas) = split t1 t2 in
                              ((h1, h2) :: pairs, remps, remas)
    in
    let fparams, fbody = StringMap.find fname m in
    match fbody with
    | {expr_kind = EApply (e1, e2) } ->
            let applst = flatten_apply e1 @ [e2] in
            let g = List.hd applst in
            (match expr_is_global_fun m g with
            | Some (gname) when gname <> fname ->
                let gparams, gbody = StringMap.find gname m in
                (*
                 * rename arguments of g to unique variable names to
                 * avoid parasitic bindings.
                 *)
                let pairs = List.map (fun x ->
                                      let x' = fresh_var () in (x, x'))
                                     gparams in
                let _, gparams = List.split pairs in
                let subst_map = List.fold_left
                                (fun m p ->
                                 let oldx, newx = p in
                                 StringMap.add oldx (mk_evar newx) m)
                                StringMap.empty
                                pairs in
                let _, gbody = subst subst_map gbody in

                (* Now we have a version of 'g' where all the arguments
                 * are fresh, but we do not update the global mapping.
                 *)
                let gargs = List.tl applst in
                let gparams_gargs, rparams, rargs = split gparams gargs in
                let subst_map = List.fold_left
                                (fun m param_arg ->
                                 let param, arg = param_arg in
                                 StringMap.add param arg m)
                                StringMap.empty
                                gparams_gargs in
                let _, gbody' = subst subst_map gbody in
                let m = StringMap.remove fname m in
                let m = StringMap.add fname (fparams @ rparams,
                                             lst_to_eapply @@ [gbody'] @ rargs) m in
                m

            | _ ->
                    m)
    | _ ->
            m



let func_mappings_equal m1 m2 =
    if StringMap.cardinal m1 <> StringMap.cardinal m2 then
        false
    else
         StringMap.fold (fun var varlist_expr res ->
                         if not res then
                             false
                         else if not @@ StringMap.mem var m2 then
                             false
                         else
                             let varlist1, expr1 = varlist_expr in
                             let varlist2, expr2 = StringMap.find var m2 in
                             varlist1 = varlist2
                             && Ast.cmp_ast_noloc expr1 expr2)
                         m1
                         true

let resolve_letrecs_globfuns m =
    let vars = StringMap.fold (fun var _ l -> var :: l) m [] in
    List.fold_left (fun m var ->
                    let varlst, expr = StringMap.find var m in
                    let m, expr = resolve_letrecs m expr in
                    let m = StringMap.remove var m in
                    StringMap.add var (varlst, expr) m) m vars


let rec uneta_globalfuns m e =
    let vars = StringMap.fold (fun var _ l -> var :: l) m [] in
    let m1 = List.fold_left uneta m vars in

    (* XXX we can try to get rid of local fixpoint and
     *     rely on the one in flaten how, but we have to
     *     check whether this is possible.
     *)
    if func_mappings_equal m m1 then
        m1
    else
        uneta_globalfuns m1 e


let rec mk_global_pats m pats =
    let vars = StringMap.fold (fun var _ l -> var :: l) m [] in
    List.fold_left (fun mpats var ->
                             let varlst, expr = StringMap.find var m in
                             let (m, pats), expr' = resolve_fun_app mpats expr in
                             let m = StringMap.remove var m in
                             let m = StringMap.add var (varlst, expr') m in
                             (m, pats))
                            (m, pats) vars



let rec apply_global_pats m pats =
    let vars = StringMap.fold (fun var _ l -> var :: l) m [] in
    let m1 = List.fold_left (fun m var ->
                             let varlst, expr = StringMap.find var m in
                             let _, expr' = apply_pats (m, pats) expr in
                             let idcall = lst_to_eapply @@ List.map mk_evar (var :: varlst) in
                             (* If we substitute a pattern definition we endup with id.  *)
                             if not @@ Ast.cmp_ast_noloc expr' idcall then
                                 let m = StringMap.remove var m in
                                 StringMap.add var (varlst, expr') m
                             else
                                 m) m vars in
    if func_mappings_equal m m1 then
        m1
    else
         apply_global_pats m1 pats




let rec flatten_hof m pats e =
    let mold = m in

    let _, e1 = propagate () e in

    let (m, pats), e1 = resolve_fun_app (m, pats) e1 in
    let (m, pats), e1 = apply_pats (m, pats) e1 in
    let m = apply_global_pats m pats in
    let m, pats = mk_global_pats m pats in
    let (m, pats), e1 = apply_pats (m, pats) e1 in

    let (_, s), _ = reachable_funs (m, StringSet.empty) e1 in
    let m = StringSet.fold
            (fun var m' ->
             StringMap.add var (StringMap.find var m) m')
            s
            StringMap.empty in
    let m, e1 = resolve_letrecs m e1 in

    let _, e1 = propagate () e1 in

    let m = uneta_globalfuns m e1 in
    let _, e1 = propagate () e1 in

    (* Fixpoint over goal expression and global functions.  *)
    if Ast.cmp_ast_noloc e e1
       && func_mappings_equal mold m then
        (m, e1)
    else
        flatten_hof m pats e1


(* inline applications when all the parameters are given.  *)
let rec inline_full_apps m e =
    let rec upd_args mpats l =
        match l with
        | h :: t ->
                let (mpats, h) = inline_full_apps mpats h in
                let mpats, t = upd_args mpats t in
                (mpats, h :: t)
        | [] -> (mpats, [])
    in
    match e with
    | { expr_kind = EApply (e1, e2) } ->
            let applst = flatten_apply e1 @ [e2] in
            let m, applst = upd_args m applst in
            let g = List.hd applst in
            let e = match expr_is_global_fun m g with
             | Some (fname) ->
                 let fparams, fbody = StringMap.find fname m in
                 let (_, s), _ = reachable_funs (m, StringSet.empty) fbody in
                 if (* Non-recursive function.  *)
                    not @@ StringSet.mem fname s
                    (* Number of arguments matches the number of parameters.  *)
                    && List.length fparams = List.length applst - 1 then
                        List.fold_left2
                            (fun e arg exp ->
                                let v = fresh_var () in
                                let ve = mk_evar v in
                                let _, e' = subst (StringMap.add arg ve StringMap.empty) e in
                                mk_eletrec v exp e')
                            fbody
                            fparams
                            (List.tl applst)
                 else
                    e
             | _ -> e in
            (m, e)

    | _ ->  Traversal.topdown inline_full_apps m e

let rec inline_globalfuns m =
    let vars = StringMap.fold (fun var _ l -> var :: l) m [] in
    let m1 = List.fold_left (fun m var ->
                    let varlst, expr = StringMap.find var m in
                    let m, expr = inline_full_apps m expr in
                    (* let m, expr = propagate_glob m expr in *)
                    let m = StringMap.remove var m in
                    StringMap.add var (varlst, expr) m) m vars in
    if func_mappings_equal m m1 then
        m1
    else
        inline_globalfuns m1



let lift_lambdas e =
    let (m, _), e = lift (StringMap.empty, []) e in
    (*let m, e = lift1 (StringMap.empty) e in*)
    Printf.printf "--- lifting lambdas into global functions and updating the expression\n";
    let m,  e = flatten_hof m [] e in
    Printf.printf "--- done flattening\n";
    (*print_mapping m;*)

    let m = inline_globalfuns m in
    print_mapping m;
    (*
     * Create an environment for all the functions, using the naming
     * scheme for the pointers __p + <fun-name>.
     *)
    let env = Env.env_new () in
    let env = StringMap.fold (fun var valist_expr env ->
                              Env.env_add env var ("__p" ^ var))
                             m
                             env in
    (*
     * Create pointers for global functions.
     *)
    let st = Storage.st_new () in
    let st = StringMap.fold (fun var varlist_expr st ->
                             let varlist, expr = varlist_expr in
                             Storage.st_add st ("__p" ^ var)
                                            (* Include `env` in all the function closures
                                             * so that they have access to all the global
                                             * functions.
                                             *)
                                            @@ Value.VClosure ((wrap_lambda varlist expr), env))
                            m
                            st in
    (m, st, env, e)
