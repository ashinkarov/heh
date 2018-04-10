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

type apl_function = {name: string;
                     body: apl_stmt list;
                     comment: string }

and apl_stmt =
    | AplAssign of (string list option) * apl_expr
    | AplFundef of apl_function

and apl_expr =
    | AplNum of int
    | AplVar of string
    | AplFuncall of string * (apl_expr list)
    | AplBinop of string * apl_expr * apl_expr
    | AplUnop of string * apl_expr

(* Helper mk_ functions.  *)
let mk_apl_function ?(comment="") name stmts =
    { name = name; body = stmts; comment = comment }

(* Print sac program.  *)
open Printf

let prind oc n =
    for i = 1 to n do
        fprintf oc "    "
    done

let rec print_sep_list ?(sep=", ") oc f args =
    match args with
    | [] -> ()
    | x :: [] -> f x;
    | x :: t  -> f x; fprintf oc "%s" sep; print_sep_list ~sep:sep oc f t

let rec varlst_to_str vars =
    match vars with
    | [] -> ""
    | h :: [] -> Printf.sprintf "%s" h
    | h :: t -> Printf.sprintf "%s %s" h @@ varlst_to_str t

let rec print_apl_expr oc level e =
    match e with
    | AplNum n ->
            fprintf oc "%d" n

    | AplVar x ->
            fprintf oc "%s" x

    | AplFuncall (f, args) ->

            fprintf oc "%s " f;
            print_sep_list oc
                ~sep:" "
                (fun e ->
                    fprintf oc "(";
                    print_apl_expr oc level e;
                    fprintf oc ")")
                args

    | AplBinop (op, a, b) ->
            fprintf oc "(" ;
            print_apl_expr oc level a;
            fprintf oc ") %s (" op ;
            print_apl_expr oc level b;
            fprintf oc ")"

    | AplUnop (op, a) ->
            fprintf oc "%s(" op;
            print_apl_expr oc level a;
            fprintf oc ")"


and print_apl_stmt oc level s =
    match s with
    | AplAssign (s, e) ->
            prind oc level;
            (match s with
             | None -> ()
             | Some vars -> fprintf oc "(%s) ← " @@ varlst_to_str vars);
            print_apl_expr oc level e; fprintf oc "\n"

    | AplFundef (f) ->
            print_apl_fun oc level f;
            fprintf oc "\n"


and print_apl_stmts oc level stmts =
    fprintf oc "{\n";
    List.fold_left (fun () s -> print_apl_stmt oc (level+1) s) () stmts;
    prind oc level; fprintf oc "}"

and print_apl_fun oc level f =
    if f.comment <> "" then begin
        prind oc level;
        fprintf oc "⍝ %s\n" f.comment
    end;

    if level = 0 then
        fprintf oc "∇ ";

    prind oc level;
    fprintf oc "%s ← " f.name;
    print_apl_stmts oc level f.body;

    if level = 0 then
        fprintf oc " ∇\n"


let print_apl_prog oc p =
    List.fold_left (fun () f -> print_apl_fun oc 0 f; fprintf oc "\n\n") () p


let var_count = ref 0

(* Generate a fresh pointer name.  *)
let fresh_var_name () =
    var_count := !var_count + 1;
    Printf.sprintf "x_%d" !var_count



let rec compile_stmts stmts e =
    let open Ast in
    match e with
    | { expr_kind = EFalse } ->
            let res_var = fresh_var_name () in
            (stmts @ [AplAssign (Some [res_var], AplNum 0)], res_var)

    | { expr_kind = ETrue } ->
            let res_var = fresh_var_name () in
            (stmts @ [AplAssign (Some [res_var], AplNum 1)], res_var)

    | { expr_kind = ENum n } ->
            let n = Ordinals.ord_to_nat n in
            let res_var = fresh_var_name () in
            (stmts @ [AplAssign (Some [res_var], AplNum n)], res_var)

    | { expr_kind = EVar (x) } ->
            (stmts, x)

    | { expr_kind = EArray (lst) } ->
            let res_var = fresh_var_name () in
            if lst = [] then
                (stmts @ [AplAssign (Some [res_var], AplVar "⍬")], res_var)
            else
                let stmts_lst, vars =
                    List.split @@ List.map (compile_stmts []) lst in

                let shp = AplBinop (",", AplNum (List.length vars),
                                    AplUnop ("⍴", AplVar (List.hd vars))) in
                let vec = List.fold_left
                          (fun l v ->
                              AplBinop (",", l, AplUnop (",", AplVar v)))
                          (AplVar "⍬")
                          vars in
                let exp = AplBinop ("⍴", shp, vec) in

                let stmts = stmts @ List.flatten stmts_lst
                                  @ [AplAssign (Some [res_var], exp)] in
            (stmts, res_var)

    | { expr_kind = EBinOp (op, e1, e2) } ->
            let stmts, var1 = compile_stmts stmts e1 in
            let stmts, var2 = compile_stmts stmts e2 in
            let res_var = fresh_var_name () in
            let oper =
                if op = OpDiv then
                    AplUnop ("⌊", AplBinop ("÷", AplVar var1, AplVar var2))
                else if op = OpMod then
                    AplBinop ("|", AplVar var2, AplVar var1)
                else
                    let opname =
                        match op with
                        | OpPlus  -> "+"
                        | OpMinus -> "-"
                        | OpMult  -> "×"
                        | OpLt    -> "<"
                        | OpLe    -> "≤"
                        | OpGt    -> ">"
                        | OpGe    -> "≥"
                        | OpEq    -> "≡"
                        | OpNe    -> "≢"
                        | _ -> failwith "Cannot happen"
                    in
                    AplBinop (opname, AplVar var1, AplVar var2) in
            (stmts @ [AplAssign (Some [res_var], oper)], res_var)

    | { expr_kind = EUnary (op, e1) } ->
            let stmts, var1 = compile_stmts stmts e1 in
            let opname =
                match op with
                | OpShape -> "⍴"
                | OpIsLim -> "is_limit_ordinal" in
            let res_var = fresh_var_name () in
            let funcall = AplUnop (opname, AplVar var1) in
            (stmts @ [AplAssign (Some [res_var], funcall)], res_var)

    | { expr_kind = ELambda (x, e) } ->
            failwith "Lambdas are not supported, they should have been lifted."

    | { expr_kind = EApply (e1, e2) } ->
            let res_var = fresh_var_name () in
            (* XXX we assume that there are no higher-order
             *     functions anymore.  If there are, we are in
             *     trouble.
             *)
            let fargs = Lifting.flatten_apply e in
            let argstmts_vars = List.map (compile_stmts []) fargs in
            let argstmts, vars = List.split argstmts_vars in
            let argstmts = List.flatten argstmts in
            let fname = List.hd vars in
            let fargs = List.map (fun x -> AplVar x) @@ List.tl vars in
            let funcall = AplFuncall (fname, fargs) in
            (stmts @ argstmts @ [AplAssign (Some [res_var], funcall)], res_var)

    | { expr_kind = ESel (e1, e2) } ->
            let stmts, var1 = compile_stmts stmts e1 in
            let stmts, var2 = compile_stmts stmts e2 in
            let res_var = fresh_var_name () in
            let funcall = AplBinop ("⌷", AplVar var2, AplVar var1) in
            (stmts @ [AplAssign (Some [res_var], funcall)], res_var)

    | { expr_kind = ECond (e1, e2, e3) } ->
            let stmts1, var1 = compile_stmts stmts e1 in
            let stmts2, var2 = compile_stmts [] e2 in
            let stmts3, var3 = compile_stmts [] e3 in

            let tr_br_name = "tr_br_" ^ fresh_var_name () in
            let tr_br_fun = mk_apl_function tr_br_name (stmts2 @ [AplAssign (None, AplVar var2)]) in

            let fl_br_name = "fl_br_" ^ fresh_var_name () in
            let fl_br_fun = mk_apl_function fl_br_name (stmts3 @ [AplAssign (None, AplVar var3)]) in

            let cond_f_name = "cond_" ^ fresh_var_name () in
            let pred_name = "pred_" ^ fresh_var_name () in
            let cond_f = mk_apl_function
                            cond_f_name
                            [AplAssign (Some [pred_name], AplVar "⍵");
                             AplFundef (tr_br_fun);
                             AplFundef (fl_br_fun);
                             AplAssign (None, AplBinop (":", AplVar pred_name,
                                                             AplFuncall (tr_br_name, [AplNum 0])));
                             AplAssign (None, AplFuncall (fl_br_name, [AplNum 0]))] in

            let res_var = fresh_var_name () in
            (stmts1 @ [AplFundef (cond_f);
                       AplAssign (Some [res_var], AplFuncall (cond_f_name, [AplVar var1]))],
             res_var)

    | { expr_kind = ELetRec (s, e1, e2) } ->
            let stmts1, var1 = compile_stmts [] e1 in
            let stmts1 = stmts1 @ [AplAssign (Some [s], AplVar var1)] in
            let stmts2, var2 = compile_stmts [] e2 in
            (stmts @ stmts1 @ stmts2, var2)

    | { expr_kind = EImap (e_out, e_in, ge_lst) } ->
            let stmts, var1 = compile_stmts stmts e_out in
            let stmts, var2 = compile_stmts stmts e_in in
            (* Concat shape vectors into shp_var *)
            let shp_var = fresh_var_name () in
            let funcall =  AplBinop (",", AplVar var1, AplVar var2) in
            let stmts = stmts @ [AplAssign (Some [shp_var], funcall)] in
            (* Emit code for all the generator expressions.  *)
            let gen_code = List.map
                           (fun ge ->
                            let gen, e = ge in
                            let lb, x, ub = gen in
                            let stmts, var_lb = compile_stmts [] lb in
                            let stmts, var_ub = compile_stmts stmts ub in
                            (stmts, (var_lb, x, var_ub, e)))
                           ge_lst in

            (* FIXME if we have more partitions, how do we combine then? *)
            assert (List.length ge_lst <= 1);

            let stmts_lst_gens, var_gen_expr_lst = List.split gen_code in
            let stmts = stmts @ List.flatten stmts_lst_gens in

            let parts = List.map
                        (fun var_gen_expr ->
                        let var_lb, x, var_ub, e = var_gen_expr in
                        let stmts, part_res_var = compile_stmts [] e in
                        let iter =  AplBinop ("indexset", AplVar var_lb, AplVar var_ub) in
                        let iter_var = fresh_var_name () in
                        let iter_assign = AplAssign (Some [iter_var], iter) in
                        let part_fun_name = fresh_var_name () in
                        let part_fun =
                            mk_apl_function part_fun_name
                                            ([AplAssign (Some [x], AplVar "⍵")]
                                             @ stmts
                                             @ [AplAssign (None, AplVar part_res_var)]) in
                        let res = fresh_var_name () in
                        (res, [iter_assign;
                               AplFundef (part_fun);
                               AplAssign (Some [res],
                                          (* XXX some cheating here.  *)
                                          AplBinop ("⍤1 ⊢", AplVar part_fun_name, AplVar iter_var))]))
                        var_gen_expr_lst in

            (* FIXME does not support multiple partitions yet! *)
            let res_var, p_stmts = List.hd parts in
            (stmts @ p_stmts, res_var)

    | { expr_kind = EReduce (e_fun, e_neut, e_arg) } ->
            let stmts, fname = compile_stmts stmts e_fun in
            let stmts, neut  = compile_stmts stmts e_neut in
            let stmts, arg   = compile_stmts stmts e_arg in

            let red_fun_name = "red_" ^ fresh_var_name () in
            let red_stmts = [
                AplAssign (Some ["a"], AplVar "⍵");
                AplAssign (Some ["empty_p"], AplBinop ("≡", AplVar "a", AplVar "⍬"));
                AplAssign (None, AplBinop (":", AplVar "empty_p", AplVar neut));
                AplAssign (Some ["unit_p"],
                           AplBinop ("=", AplBinop ("/", AplVar "×",
                                                         AplUnop ("⍴", AplVar "a")),
                                          AplNum 1));
                AplFundef (mk_apl_function
                               "ff"
                               [AplAssign (None,
                                           AplFuncall (fname, [AplVar "⍺"; AplVar "⍵"]))]);
                AplAssign (None,
                           AplBinop (":", AplVar "unit_p",
                                          AplFuncall (fname, [AplVar neut;
                                                              AplBinop ("⌷", AplNum 0, AplVar "a")])));
                AplAssign (None, AplBinop ("/", AplVar "ff", AplVar "a"))] in

            let red_fun = mk_apl_function red_fun_name red_stmts in

            (* get the shape of the argument *)
            let res_var = fresh_var_name () in
            let stmt = AplAssign (Some [res_var],
                                  AplFuncall (red_fun_name, [AplUnop (",", AplVar arg)])) in
            (stmts @ [AplFundef red_fun; stmt], res_var)

    | { expr_kind = EFilter (e_fun, e_arg) } ->
            let stmts, fname = compile_stmts stmts e_fun in
            let stmts, arg   = compile_stmts stmts e_arg in

            (* get the shape of the argument *)
            let res_var = fresh_var_name () in
            let stmt = AplAssign (Some [res_var],
                                  AplBinop ("/", AplBinop ("¨", AplVar fname, AplVar arg),
                                                 AplVar arg)) in
            (stmts @ [stmt], res_var)


let compile_main (e: Ast.expr) =
    let stmts, var = compile_stmts [] e in
    (* Think how do we present final result.  *)
    let comment = Printf.sprintf "%s" (Print.expr_to_str e) in
    let stmts = stmts @ [AplAssign (None, AplVar var)] in
    mk_apl_function "main" stmts ~comment:comment

let compile_apl_function name varlst expr =

    let comment = Printf.sprintf "Λ%s . %s"
                  (varlst_to_str varlst)
                  (Print.expr_to_str expr) in
    let stmts, var = compile_stmts [] expr in
    let stmts = [AplAssign (Some varlst, AplVar "⍵")]
                @ stmts @ [AplAssign (None, AplVar var)] in
    mk_apl_function name stmts ~comment:comment

let apl_header =
  "⎕ml←3\n"
^ "⎕io←0\n"
^ "\n"
(*^ "indexset ← {⍺ +⍤1 ⊢ ⊃(⍳⍵-⍺)}\n"*)
^ "indexset ← { ⊃(⊂⍺) + ⍳⍵-⍺ }\n"
^ "is_limit_ordinal ← { 0 }\n"
^ "\n"
^ "\n"

let apl_footer =
    "main ⍬"
^ "\n"
^ "\n"

let compile e m =
    let p = Lifting.StringMap.fold
               (fun var varlist_expr p ->
                let varlst, expr = varlist_expr in
                let apl_fun = compile_apl_function var varlst expr in
                apl_fun :: p)
               m
               [] in

    let p = p @ [compile_main e] in
    let out = open_out !Globals.apl_out_file in
    fprintf out "%s" apl_header;
    fprintf out "⍝ --- apl-code ---\n";
    print_apl_prog out p;
    fprintf out "%s" apl_footer;
    close_out out
