open Ast;;


(* Change applications of "reduce" and "filters" that were parsed as EApply
   into EReduce and EFilter constructs. *)
let rec app_to_hof e =
    match e with
    | EApply (EApply (EApply (EVar ("reduce"), e1), e2), e3) ->
        EReduce (e1, e2, e3)
    | EApply (EApply (EVar ("filter"), e1), e2) ->
        EFilter (e1, e2)
    | EVar ("reduce") ->
        raise (ImapFailure "reduce found with less than three arguments")
    | EVar ("filter") ->
        raise (ImapFailure "filter found with less than two arguments")
    | EApply (e1, e2) ->
        EApply (app_to_hof e1, app_to_hof e2)
    | EArray (lst) ->
        EArray (List.map app_to_hof lst)
    | EBinOp (bop, e1, e2) ->
        EBinOp (bop, app_to_hof e1, app_to_hof e2)
    | EUnary (uop, e1) ->
        EUnary (uop, app_to_hof e1)
    | ELambda (x, e1) ->
        ELambda (x, app_to_hof e1)
    | ECond (e1, e2, e3) ->
        ECond (app_to_hof e1, app_to_hof e2, app_to_hof e3)
    | ELetRec (x, e1, e2) ->
        ELetRec (x, app_to_hof e1, app_to_hof e2)
    | EImap (e1, e2, gelst) ->
        EImap (app_to_hof e1, app_to_hof e2,
               (List.map (fun ge -> let (g, e) = ge in
                                    let (lb, var, ub) = g in
                                    ((app_to_hof lb, var, app_to_hof ub), app_to_hof e))
                         gelst))
    | _ -> e
;;