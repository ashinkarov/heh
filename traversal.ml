open Ast

(* This traversal reconstructs the tree as it goes along and accumulates
 * additional information in `m'.
 *
 * FIXME: implement traversal that avoids tree reconstruction.
 *        something that can be used to count something in a tree, or similar.
 *)
let rec topdown f m e =
    match e with
    | {expr_kind = EFalse }
    | {expr_kind = ETrue }
    | {expr_kind = ENum _ }
    | {expr_kind = EVar _ } ->
            (m, e)

    | {expr_kind = ELambda (x1, e1); loc = l} ->
            let m, e1' = f m e1 in
            (m, mk_elambda x1 e1' ~loc:l)

    | {expr_kind = EBinOp (op, e1, e2)} ->
            let m, e1' = f m e1 in
            let m, e2' = f m e2 in
            (m, mk_ebinop op e1' e2')

    | {expr_kind = EApply (e1, e2);} ->
            let m, e1' = f m e1 in
            let m, e2' = f m e2 in
            (m, mk_eapply e1' e2')

    | {expr_kind = ESel (e1, e2)} ->
            let m, e1' = f m e1 in
            let m, e2' = f m e2 in
            (m, mk_esel e1' e2')

    | {expr_kind = EFilter (e1, e2); loc=l } ->
            let m, e1' = f m e1 in
            let m, e2' = f m e2 in
            (m, mk_efilter e1' e2' ~loc:l)

    | {expr_kind = ELetRec (x, e1, e2); loc=l } ->
            let m, e1' = f m e1 in
            let m, e2' = f m e2 in
            (m, mk_eletrec x e1' e2' ~loc:l)

    | {expr_kind = EUnary (op, e1); loc=l} ->
            let m, e1' = f m e1 in
            (m, mk_eunary op e1' ~loc:l)

    | {expr_kind = ECond (e1, e2, e3); loc=l} ->
            let m, e1' = f m e1 in
            let m, e2' = f m e2 in
            let m, e3' = f m e3 in
            (m, mk_econd e1' e2' e3' ~loc:l)

    | {expr_kind = EReduce (e1, e2, e3); loc=l} ->
            let m, e1' = f m e1 in
            let m, e2' = f m e2 in
            let m, e3' = f m e3 in
            (m, mk_ereduce e1' e2' e3' ~loc:l)

    | {expr_kind = EImap (e1, e2, gelst); loc = l} ->
            let m, e1' = f m e1 in
            let m, e2' = f m e2 in
            let rec iter m gelst =
                match gelst with
                | [] -> (m, [])
                | g :: gs ->
                        let (lb, x, ub), eb = g in
                        let m, lb' = f m lb in
                        let m, ub' = f m ub in
                        let m, eb' = f m eb in
                        let m, gs' = iter m gs in
                        (m, ((lb', x, ub'), eb') :: gs')
            in
            let m, gelst' = iter m gelst in
            (m, mk_eimap e1' e2' gelst' ~loc:l)

    | {expr_kind = EArray exprlst; loc=l} ->
            let rec iter m lst =
                match lst with
                | [] -> (m, [])
                | e :: es ->
                        let m, es' = iter m es in
                        let m, e' = f m e in
                        (m, e' :: es')
            in
            let m, lst = iter m exprlst in
            (m, mk_earray lst ~loc:l)

