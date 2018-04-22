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

(* TODO
 * 1. Explain design decisions and describe optimisation oportunities.
 * 2. Deal with partial applications.
 * 3. Insert assertions like range checks, partitioning etc.
 *)

type py_type =
    | PyInt
    | PyBool

type py_prog =
    py_function list

and py_function = { name: string;
                    params: string list;
                    body: py_stmt list;
                    comment: string }

and py_stmt =
    | PyAssign of string * py_expr
    | PyReturn of py_expr
    | PyCond of py_expr * (py_stmt list) * (py_stmt list)
    | PyCond1 of py_expr * (py_stmt list)
    | PyFundef of py_function
    | PyForeach of string * py_expr * (py_stmt list)

and py_expr =
    | PyNone
    | PyFalse
    | PyTrue
    | PyNum of int
    | PyArray of py_expr list
    (* array, index *)
    | PySel of py_expr * py_expr
    | PyBinop of py_expr * string * py_expr
    | PyVar of string
    | PyFuncall of string * (py_expr list)

(* Helper mk_ functions.  *)
let mk_py_function ?(comment="") name params stmts =
    { name = name; params = params; body = stmts; comment = comment }

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
    | x :: t  -> f x; fprintf oc "%s" sep; print_sep_list oc f t

let rec print_py_expr oc level e =
    match e with
    | PyNone ->
            fprintf oc "None"

    | PyTrue ->
            fprintf oc "True"

    | PyFalse ->
            fprintf oc "False"

    | PyNum n ->
            fprintf oc "np.array (%d)" n

    | PyArray lst ->
            fprintf oc "np.array ([";
            print_sep_list oc (print_py_expr oc level) lst;
            fprintf oc "])"

    | PySel (a, idx) ->
            fprintf oc "np.array (";
            print_py_expr oc level a;
            fprintf oc "[tuple (";
            print_py_expr oc level idx;
            fprintf oc ")]";
            fprintf oc ")"

    | PyBinop (a, op, b) ->
            fprintf oc "(";
            print_py_expr oc level a;
            fprintf oc " %s " op;
            print_py_expr oc level b;
            fprintf oc ")";

    | PyVar x ->
            fprintf oc "%s" x

    | PyFuncall (f, args) ->
            fprintf oc "%s (" f; print_sep_list oc (print_py_expr oc level) args; fprintf oc ")"

and print_py_stmt oc level s =
    match s with
    | PyAssign (s, e) ->
            prind oc level; fprintf oc "%s = " s;
            print_py_expr oc level e; fprintf oc "\n"

    | PyCond (e, stmts1, stmts2) ->
            prind oc level;
            fprintf oc "if ("; print_py_expr oc level e; fprintf oc "):\n";
            print_py_stmts oc level stmts1;
            prind oc level;
            fprintf oc "else:\n";
            print_py_stmts oc level stmts2;

    | PyCond1 (e, stmts1) ->
            prind oc level;
            fprintf oc "if ("; print_py_expr oc level e; fprintf oc "):\n";
            print_py_stmts oc level stmts1;

    | PyForeach (var, init, stmts) ->
            prind oc level;
            fprintf oc "for %s in (" var;
            print_py_expr oc level init; fprintf oc "):\n";
            print_py_stmts oc level stmts;

    | PyReturn (e) ->
            prind oc level;
            fprintf oc "return ";
            print_py_expr oc level e;
            fprintf oc "\n"

    | PyFundef (f) ->
            prind oc level;
            print_py_fun oc level f;
            fprintf oc "\n"

and print_py_stmts oc level stmts =
    List.fold_left (fun () s -> print_py_stmt oc (level+1) s) () stmts

and print_py_params oc params =
    fprintf oc "(";
    print_sep_list oc
                   (fun (param: string) -> fprintf oc "%s" param)
                   params;
    fprintf oc ")"


and print_py_fun oc level f =
    if f.comment <> "" then
        fprintf oc "# %s\n" f.comment;

    fprintf oc "def %s " f.name;
    print_py_params oc f.params;
    fprintf oc ":\n";
    print_py_stmts oc level f.body


let print_py_prog oc p =
    List.fold_left (fun () f -> print_py_fun oc 0 f; fprintf oc "\n\n") () p


let var_count = ref 0

(* Generate a fresh variable name.  *)
let fresh_var_name () =
    var_count := !var_count + 1;
    sprintf "x_%d" !var_count


let rec compile_stmts stmts e =
    let open Ast in
    match e with
    | { expr_kind = EFalse } ->
            let res_var = fresh_var_name () in
            (stmts @ [PyAssign (res_var, PyFalse)], res_var)

    | { expr_kind = ETrue } ->
            let res_var = fresh_var_name () in
            (stmts @ [PyAssign (res_var, PyTrue)], res_var)

    | { expr_kind = ENum n } ->
            let n = Ordinals.ord_to_nat n in
            let res_var = fresh_var_name () in
            (stmts @ [PyAssign (res_var, PyNum n)], res_var)

    | { expr_kind = EVar (x) } ->
            (stmts, x)

    | { expr_kind = EArray (lst) } ->
            let stmts_lst, vars =
                List.split @@ List.map (compile_stmts []) lst in
            let res_var = fresh_var_name () in
            let res_arr = PyArray (List.map (fun x -> PyVar x) vars) in
            (stmts @ List.flatten stmts_lst @ [PyAssign (res_var, res_arr)],
             res_var)

    | { expr_kind = EBinOp (op, e1, e2) } ->
            let stmts, var1 = compile_stmts stmts e1 in
            let stmts, var2 = compile_stmts stmts e2 in
            let res_var = fresh_var_name () in
            let opname =
                match op with
                | OpPlus  -> "+"
                | OpMinus -> "-"
                | OpDiv   -> "//"
                | OpMod   -> "%"
                | OpMult  -> "*"
                | OpLt    -> "<"
                | OpLe    -> "<="
                | OpGt    -> ">"
                | OpGe    -> ">="
                | OpEq    -> "=="
                | OpNe    -> "!="
            in
            let binop = PyBinop (PyVar var1, opname,  PyVar var2) in
            (stmts @ [PyAssign (res_var, binop)], res_var)

    | { expr_kind = EUnary (op, e1) } ->
            let stmts, var1 = compile_stmts stmts e1 in
            let opname =
                match op with
                | OpShape -> "heh_shape"
                | OpIsLim -> "heh_islim" in
            let res_var = fresh_var_name () in
            let funcall = PyFuncall (opname, [PyVar var1]) in
            (stmts @ [PyAssign (res_var, funcall)], res_var)

    | { expr_kind = ELambda (x, e) } ->
            failwith "All lambdas should have been lifted!"

    | { expr_kind = EApply (e1, e2) } ->
            let res_var = fresh_var_name () in
            (* FIXME Check for higher-order functions and make partial application.
             *       For now we assume full applications only.
             *)
            let fargs = Lifting.flatten_apply e in
            let argstmts_vars = List.map (compile_stmts []) fargs in
            let argstmts, vars = List.split argstmts_vars in
            let argstmts = List.flatten argstmts in
            let fname = List.hd vars in
            let fargs = List.map (fun x -> PyVar x) @@ List.tl vars in
            let funcall = PyFuncall (fname, fargs) in
            (stmts @ argstmts @ [PyAssign (res_var, funcall)], res_var)

    | { expr_kind = ESel (e1, e2) } ->
            let stmts, var1 = compile_stmts stmts e1 in
            let stmts, var2 = compile_stmts stmts e2 in
            let res_var = fresh_var_name () in
            let sel = PySel (PyVar var1, PyVar var2) in
            (stmts @ [PyAssign (res_var, sel)], res_var)

    | { expr_kind = ECond (e1, e2, e3) } ->
            let stmts1, var1 = compile_stmts stmts e1 in
            let stmts2, var2 = compile_stmts [] e2 in
            let stmts3, var3 = compile_stmts [] e3 in
            let res_var = fresh_var_name () in
            let stmts2 = stmts2 @ [PyAssign (res_var, PyVar var2)] in
            let stmts3 = stmts3 @ [PyAssign (res_var, PyVar var3)] in
            (stmts1 @ [PyCond (PyVar var1, stmts2, stmts3)], res_var)

    | { expr_kind = ELetRec (s, e1, e2) } ->
            let stmts1, var1 = compile_stmts [] e1 in
            let stmts1 = stmts1 @ [PyAssign (s, PyVar var1)] in
            let stmts2, var2 = compile_stmts [] e2 in
            (stmts @ stmts1 @ stmts2, var2)

    | { expr_kind = EReduce (e_fun, e_neut, e_arg) } ->
            let stmts, fname = compile_stmts stmts e_fun in
            let stmts, neut  = compile_stmts stmts e_neut in
            let stmts, arg   = compile_stmts stmts e_arg in

            let res_var = fresh_var_name () in
            let funcall = PyFuncall ("heh_reduce", [PyVar fname; PyVar neut; PyVar arg]) in
            (stmts @ [PyAssign (res_var, funcall)], res_var)

    | { expr_kind = EFilter (e_fun, e_arg) } ->
            let stmts, fname = compile_stmts stmts e_fun in
            let stmts, arg   = compile_stmts stmts e_arg in

            let res_var = fresh_var_name () in
            let funcall = PyFuncall ("heh_filter", [PyVar fname; PyVar arg]) in
            (stmts @ [PyAssign (res_var, funcall)], res_var)

    | { expr_kind = EImap (e_out, e_in, ge_lst) } ->
            let stmts, var1 = compile_stmts stmts e_out in
            let stmts, var2 = compile_stmts stmts e_in in
            (* Emit code for all the generator expressions.
             *
             * lb1 <= iv1 < ub1: e1, ... =>
             *
             * def f(idx):
             *    if lb1 <= idx < ub1:
             *       iv1 = idx
             *       e1
             *    else
             *       die (cannot happen)
             *)
            let gen_code = List.map
                           (fun ge ->
                            let gen, e = ge in
                            let lb, x, ub = gen in
                            let stmts, var_lb = compile_stmts [] lb in
                            let stmts, var_ub = compile_stmts stmts ub in
                            (stmts, (var_lb, x, var_ub, e)))
                           ge_lst in

            let stmts_lst_gens, var_gen_expr_lst = List.split gen_code in
            let stmts = stmts @ List.flatten stmts_lst_gens in

            (*let idx_var = fresh_var_name () in

            let fstmts = List.map
                           (fun var_gen_expr ->
                            let var_lb, x, var_ub, e = var_gen_expr in
                            let stmts, res_var = compile_stmts [PyAssign (x, PyVar idx_var)] e in
                            let fcall = PyFuncall ("heh_inrange", [PyVar idx_var; PyVar var_lb; PyVar var_ub]) in
                            PyCond1 (fcall, stmts @ [PyReturn (PyVar res_var)]))
                           var_gen_expr_lst in

            let fun_name = fresh_var_name () in
            let fstmts = fstmts @ [PyReturn PyNone] in
            let stmts = stmts @ [PyFundef (mk_py_function fun_name [idx_var] fstmts)] in

            let res_var = fresh_var_name () in
            let imap = PyFuncall ("heh_imap", [PyVar var1; PyVar var2; PyVar fun_name]) in
            (stmts @ [PyAssign (res_var, imap)], res_var) *)

            let res_var = fresh_var_name () in
            let res_sh = PyFuncall ("tuple",
                                    [PyBinop (PyFuncall ("list", [PyVar var1]),
                                              "+",
                                              PyFuncall ("list", [PyVar var2]))]) in
            let res_stmt = PyAssign (res_var,
                                     PyFuncall ("np.empty",
                                                [res_sh; PyVar "dtype=int" (* HACK *)])) in
            let fstmts = List.map
                         (fun var_gen_expr ->
                          let var_lb, x, var_ub, e = var_gen_expr in
                          let stmts, part_res = compile_stmts [] e in
                          let idx_var = "idx_" ^ fresh_var_name () in
                          let stmts = [PyAssign (x, PyBinop (PyVar idx_var, "+", PyVar (var_lb)))]
                                      @ stmts
                                      @ [PyAssign ((sprintf "%s[tuple (%s)]" res_var x),
                                                   PyVar part_res)] in
                          PyForeach (idx_var,
                                     PyFuncall ("np.ndindex",
                                                [PyFuncall ("*tuple",
                                                            [PyBinop (PyVar var_ub,
                                                             "-", PyVar var_lb)])]),
                                     stmts))
                         var_gen_expr_lst in

            (stmts @ [res_stmt] @ fstmts, res_var)

let compile_main (e: Ast.expr) =
    let stmts, var = compile_stmts [] e in
    (* Think how do we present final result.  *)
    let comment = sprintf "%s" (Print.expr_to_str e) in
    let stmts = stmts @ [PyReturn (PyVar var)] in
    mk_py_function "main" [] stmts ~comment:comment

let compile_py_function name varlst expr =
    let rec vars_to_str vars =
        match vars with
        | [] -> ""
        | h :: t -> sprintf "%s %s" h @@ vars_to_str t
    in
    let comment = sprintf "Λ%s . %s"
                  (vars_to_str varlst)
                  (Print.expr_to_str expr) in
    let stmts, var = compile_stmts [] expr in
    let stmts = stmts @ [PyReturn (PyVar var)] in
    mk_py_function name varlst stmts ~comment:comment

let py_funs =
  "import numpy as np\n"
^ "\n"
^ "\n"
^ "def heh_imap (s1, s2, f):\n"
^ "    res_sh = tuple (list (s1) + list (s2))\n"
^ "    res = np.empty (res_sh, dtype=int)\n"
^ "\n"
^ "    for idx in np.ndindex (*tuple (s1)):\n"
^ "        res[idx] = f (np.array (idx))\n"
^ "\n"
^ "    return res\n"
^ "\n"
^ "\n"
^ "def heh_reduce (f, neut, a):\n"
^ "    res = neut\n"
^ "    # Here we assume that all arrays are created in standard\n"
^ "    # Row-Major ('C' in numpy terminology) layout.\n"
^ "    for x in np.nditer (a):\n"
^ "        res = f (x, res)\n"
^ "\n"
^ "    return res\n"
^ "\n"
^ "# Straight-forward implementation of filter.\n"
^ "# We can be smarter later.\n"
^ "def heh_filter (p, a):\n"
^ "    return np.array ([x for x in np.nditer (a) if p (x)])\n"
^ "\n"
^ "def heh_shape (a):\n"
^ "    return np.array (a.shape)\n"
^ "\n"
^ "def heh_islim (a):\n"
^ "    return False\n"
^ "\n"
^ "def heh_inrange (x, lb, ub):\n"
^ "    return np.all (lb <= x) and np.all (x < ub)\n"
^ "\n"
^ "\n"
^ "\n"


let call_py_main =
  "if __name__ == \"__main__\":\n"
^ "    print (main ())\n"
^ "\n"
^ "\n"
^ "\n"

let compile e m =
    let p = Lifting.StringMap.fold
               (fun var varlist_expr p ->
                let varlst, expr = varlist_expr in
                let py_fun = compile_py_function var varlst expr in
                py_fun :: p)
               m
               [] in

    let p = p @ [compile_main e] in
    let out = open_out !Globals.py_out_file in
    fprintf out "%s" py_funs;
    fprintf out "# --- python-code ---\n";
    print_py_prog out p;
    Printf.fprintf out "%s" call_py_main;
    close_out out
