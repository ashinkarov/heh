
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


let rec lst_print l =
    match l with
    | [] -> ""
    | x :: xs -> Printf.sprintf "%s %s" x (lst_print xs)

let print_mapping m =
    let xprint var varlist_expr =
        let varlist, expr = varlist_expr in
        Printf.printf "%s: Λ%s.%s\n" var (lst_print varlist) (Print.expr_to_str expr)
    in
    StringMap.iter xprint m



let var_count = ref 0

(* Generate a fresh variable name.  *)
let fresh_var () =
    var_count := !var_count + 1;
    Printf.sprintf "f%d" !var_count


let rec lift m e =
    match e with
    | {expr_kind = ELambda (x1, e1) } ->
            let fv = free_vars StringSet.empty e in
            if StringSet.cardinal fv = 0 then
                let m, e1' = lift m e1 in
                Printf.printf "=1= lifting body %s into %s\n" (Print.expr_to_str e1) (Print.expr_to_str e1');
                (* XXX this avoids eta-extended functions, but maybe they can be useful.  *)
                match e1' with
                | {expr_kind = EApply (e', {expr_kind = EVar (x1)}) } ->
                        (m, e')
                | _ ->
                    let fresh = fresh_var () in
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
                let m, e1' = lift m e1 in
                Printf.printf "=2= lifting body %s into %s\n" (Print.expr_to_str e1) (Print.expr_to_str e1');
                let fresh = fresh_var () in
                let fvlist = StringSet.fold (fun var lst -> var :: lst) fv [] in
                Printf.printf "=2= fvlist = %s\n" (lst_print fvlist);

                let m = StringMap.add fresh ((List.append fvlist [x1]),  e1') m  in
                (*let fresh1 = fresh_var () in
                let m = StringMap.add fresh1 (fvlist, (mk_app fvlist (mk_evar fresh))) m in*)
                (* FIXME location. *)
                (m, mk_app fvlist (mk_evar fresh))
    | _ ->
            Traversal.topdown lift m e


let rec propagate glob m e =
    match e with
    | {expr_kind = EVar x1 } ->
            if StringMap.mem x1 m then
                (m, StringMap.find x1 m)
            else
                (m, e)
    | {expr_kind = ELambda (x1, e1) } ->
            if StringMap.mem x1 m then
                let v = StringMap.find x1 m in
                let m = StringMap.remove x1 m in
                let m, e1' = propagate glob m e1 in
                (StringMap.add x1 v m, mk_elambda x1 e1')
            else
                let m, e1' = propagate glob m e1 in
                (m, mk_elambda x1 e1')
    | {expr_kind = ELetRec (x1, e1, e2) } ->
            if (match e1.expr_kind with
                | EFalse | ETrue | EVar _ | ENum _  -> true
                | _ -> false)
            then begin
                if StringMap.mem x1 m then
                    let m = StringMap.remove x1 m in
                    (* Add new mapping *)
                    let m = StringMap.add x1 e1 m in
                    (* Substitute e1 in the body of the letrec.  *)
                    let m, e2' = propagate glob m e2 in
                    (m, e2')
                else
                    let m = StringMap.add x1 e1 m in
                    let m, e2' = propagate glob m e2 in
                    (m, e2')
            end else
                let m, e1' = propagate glob m e1 in
                let m, e2' = propagate glob m e2 in
                (m, mk_eletrec x1 e1' e2')
    | _ ->
            Traversal.topdown (propagate glob) m e


let xlift e =
    let m, e1 = lift StringMap.empty e in
    Printf.printf "globals\n";
    print_mapping m;
    Printf.printf "\n%s\n" (Print.expr_to_str e1);
    let _, e1 = propagate [] StringMap.empty e1 in
    Printf.printf "\n%s\n" (Print.expr_to_str e1)
