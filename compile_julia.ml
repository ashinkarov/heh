(*
 * Copyright (c) 2017-2018, Artem Shinkarov <artyom.shinkaroff@gmail.com>
 *               2018,      Hans-Nikolai Viessmann <hans AT viess.mn>
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

(* This file provides a backend to generate Julia code *)

type jl_type =
    | JlInt
    | JlBool

type jl_prog =
    jl_function list

(* TODO for performance reasons we should think about adding
 *      types to the fundef paramters.
 *)
and jl_function = { name: string;
                    params: string list;
                    body: jl_stmt list;
                    comment: string }

and jl_stmt =
    | JlAssign of string * jl_expr
    | JlVoid of jl_expr
    | JlReturn of jl_expr
    | JlCond of jl_expr * (jl_stmt list) * (jl_stmt list)
    | JlCond1 of jl_expr * (jl_stmt list)
    | JlFundef of jl_function
    | JlForeach of string * jl_expr * (jl_stmt list)

and jl_expr =
    | JlNull
    | JlFalse
    | JlTrue
    | JlNum of int
    | JlArray of jl_expr list
    (* array, index *)
    | JlSel of jl_expr * jl_expr
    | JlBinop of jl_expr * string * jl_expr * bool
    | JlVar of string
    | JlExpand of jl_expr
    | JlFuncall of string * (jl_expr list)

(* Helper mk_ functions.  *)
let mk_jl_function ?(comment="") name params stmts =
    { name = name; params = params; body = stmts; comment = comment }

(* Print Julia program.  *)
open Printf

let prind oc n =
    for i = 1 to n do
        fprintf oc "    "
    done

let rec print_sep_list ?(sep=", ") oc f args =
    match args with
    | [] -> ()
    | x :: [] -> f x;
    | x :: t  -> f x; fprintf oc "%s" sep; print_sep_list oc f t ~sep:sep

let rec print_jl_expr oc level e =
    match e with
    | JlNull ->
            fprintf oc "Nullable{Int}()"

    | JlTrue ->
            fprintf oc "true"

    | JlFalse ->
            fprintf oc "false"

    | JlNum n ->
            fprintf oc "heh_create_num(%d)" n

    | JlArray lst ->
            fprintf oc "heh_create_array(";
            print_sep_list oc (print_jl_expr oc level) lst;
            fprintf oc ")";

    | JlSel (a, idx) ->
            (* assume that shape is already an array *)
            fprintf oc "heh_access_array(";
            print_jl_expr oc level a;
            fprintf oc ", ";
            print_jl_expr oc level idx;
            fprintf oc ")";

    | JlBinop (a, op, b, comp) ->
            if comp then
                fprintf oc "all(";
            print_jl_expr oc level a;
            fprintf oc " %s " op;
            print_jl_expr oc level b;
            if comp then
                fprintf oc ")";

    | JlVar x ->
            fprintf oc "%s" x

    | JlExpand (e) ->
            print_jl_expr oc level e;
            fprintf oc "...";

    | JlFuncall (f, args) ->
            fprintf oc "%s(" f; print_sep_list oc (print_jl_expr oc level) args; fprintf oc ")"

and print_jl_stmt oc level s =
    match s with
    | JlAssign (s, e) ->
            prind oc level; fprintf oc "%s = " s;
            print_jl_expr oc level e; fprintf oc "\n"

    | JlVoid (e) ->
            prind oc level; print_jl_expr oc level e; fprintf oc "\n"

    | JlCond (e, stmts1, stmts2) ->
            prind oc level;
            fprintf oc "if ("; print_jl_expr oc level e; fprintf oc ")\n";
            print_jl_stmts oc level stmts1;
            prind oc level;
            fprintf oc "else\n";
            print_jl_stmts oc level stmts2;
            prind oc level;
            fprintf oc "end\n";

    | JlCond1 (e, stmts1) ->
            prind oc level;
            fprintf oc "if ("; print_jl_expr oc level e; fprintf oc ")\n";
            print_jl_stmts oc level stmts1;
            prind oc level;
            fprintf oc "end\n";

    | JlForeach (s, e, stmts1) ->
            prind oc level;
            fprintf oc "for %s in " s; print_jl_expr oc level e; fprintf oc "\n";
            print_jl_stmts oc level stmts1;
            prind oc level;
            fprintf oc "end\n";

    | JlReturn (e) ->
            prind oc level;
            fprintf oc "return ";
            print_jl_expr oc level e;
            fprintf oc "\n"

    | JlFundef (f) ->
            prind oc level;
            print_jl_fun oc level f;
            fprintf oc "\n"

and print_jl_stmts oc level stmts =
    List.fold_left (fun () s -> print_jl_stmt oc (level+1) s) () stmts

and print_jl_params oc params =
    fprintf oc "(";
    print_sep_list oc
                   (fun (param: string) -> fprintf oc "%s" param)
                   params;
    fprintf oc ")"


and print_jl_fun oc level f =
    if f.comment <> "" then
        prind oc level;
        fprintf oc "# %s\n" f.comment;

    prind oc level;
    fprintf oc "@inline function %s" f.name;
    print_jl_params oc f.params;
    fprintf oc "\n";
    print_jl_stmts oc level f.body;
    prind oc level;
    fprintf oc "end\n"

let print_jl_prog oc p =
    List.fold_left (fun () f -> print_jl_fun oc 0 f; fprintf oc "\n\n") () p


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
            (stmts @ [JlAssign (res_var, JlFalse)], res_var)

    | { expr_kind = ETrue } ->
            let res_var = fresh_var_name () in
            (stmts @ [JlAssign (res_var, JlTrue)], res_var)

    | { expr_kind = ENum n } ->
            let n = Ordinals.ord_to_nat n in
            let res_var = fresh_var_name () in
            (stmts @ [JlAssign (res_var, JlNum n)], res_var)

    | { expr_kind = EVar (x) } ->
            (stmts, x)

    | { expr_kind = EArray (lst) } ->
            let stmts_lst, vars =
                List.split @@ List.map (compile_stmts []) lst in
            let res_var = fresh_var_name () in
            let res_arr = JlArray (List.map (fun x -> JlVar x) vars) in
            (stmts @ List.flatten stmts_lst @ [JlAssign (res_var, res_arr)],
             res_var)

    | { expr_kind = EBinOp (op, e1, e2) } ->
            let stmts, var1 = compile_stmts stmts e1 in
            let stmts, var2 = compile_stmts stmts e2 in
            let res_var = fresh_var_name () in
            let (opname, iscomp) =
                match op with
                | OpPlus  -> (".+", false)
                | OpMinus -> (".-", false)
                | OpDiv   -> ("./", false)
                | OpMod   -> (".%", false)
                | OpMult  -> (".*", false)
                | OpLt    -> (".<", true)
                | OpLe    -> (".<=", true)
                | OpGt    -> (".>", true)
                | OpGe    -> (".>=", true)
                | OpEq    -> (".==", true)
                | OpNe    -> (".!=", true)
            in
            let binop = JlBinop (JlVar var1, opname,  JlVar var2, iscomp) in
            (stmts @ [JlAssign (res_var, binop)], res_var)

    | { expr_kind = EUnary (op, e1) } ->
            let stmts, var1 = compile_stmts stmts e1 in
            let opname =
                match op with
                | OpShape -> "heh_shape"
                | OpIsLim -> "heh_islim" in
            let res_var = fresh_var_name () in
            let funcall = JlFuncall (opname, [JlVar var1]) in
            (stmts @ [JlAssign (res_var, funcall)], res_var)

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
            let fargs = List.map (fun x -> JlVar x) @@ List.tl vars in
            let funcall = JlFuncall (fname, fargs) in
            (stmts @ argstmts @ [JlAssign (res_var, funcall)], res_var)

    | { expr_kind = ESel (e1, e2) } ->
            let stmts, var1 = compile_stmts stmts e1 in
            let stmts, var2 = compile_stmts stmts e2 in
            let res_var = fresh_var_name () in
            let sel = JlSel (JlVar var1, JlVar var2) in
            (stmts @ [JlAssign (res_var, sel)], res_var)

    | { expr_kind = ECond (e1, e2, e3) } ->
            let stmts1, var1 = compile_stmts stmts e1 in
            let stmts2, var2 = compile_stmts [] e2 in
            let stmts3, var3 = compile_stmts [] e3 in
            let res_var = fresh_var_name () in
            let stmts2 = stmts2 @ [JlAssign (res_var, JlVar var2)] in
            let stmts3 = stmts3 @ [JlAssign (res_var, JlVar var3)] in
            (stmts1 @ [JlCond (JlVar var1, stmts2, stmts3)], res_var)

    | { expr_kind = ELetRec (s, e1, e2) } ->
            let stmts1, var1 = compile_stmts [] e1 in
            let stmts1 = stmts1 @ [JlAssign (s, JlVar var1)] in
            let stmts2, var2 = compile_stmts [] e2 in
            (stmts @ stmts1 @ stmts2, var2)

    | { expr_kind = EReduce (e_fun, e_neut, e_arg) } ->
            let stmts, fname = compile_stmts stmts e_fun in
            let stmts, neut  = compile_stmts stmts e_neut in
            let stmts, arg   = compile_stmts stmts e_arg in

            (* TODO FIXME *)
            let res_var = fresh_var_name () in
            let funcall = JlFuncall ("heh_reduce", [JlVar fname; JlVar neut; JlVar arg]) in
            (stmts @ [JlAssign (res_var, funcall)], res_var)

    | { expr_kind = EFilter (e_fun, e_arg) } ->
            let stmts, fname = compile_stmts stmts e_fun in
            let stmts, arg   = compile_stmts stmts e_arg in

            let res_var = fresh_var_name () in
            let funcall = JlFuncall ("heh_filter", [JlVar fname; JlVar arg]) in
            (stmts @ [JlAssign (res_var, funcall)], res_var)

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

            (* introduce HO function *)
            (*
            let idx_var = fresh_var_name () in

            let fstmts = List.map
                           (fun var_gen_expr ->
                            let var_lb, x, var_ub, e = var_gen_expr in
                            let stmts, res_var = compile_stmts [JlAssign (x, JlVar idx_var)] e in
                            let fcall = JlFuncall ("heh_inrange", [JlVar idx_var; JlVar var_lb; JlVar var_ub]) in
                            JlCond1 (fcall, stmts @ [JlReturn (JlVar res_var)]))
                           var_gen_expr_lst in

            let fun_name = fresh_var_name () in
            let fstmts = fstmts @ [JlReturn (JlNum 0)] in
            let stmts = stmts @ [JlFundef (mk_jl_function fun_name [idx_var] fstmts)] in

            let res_var = fresh_var_name () in
            let imap = JlFuncall ("heh_imap", [JlVar var1; JlVar var2; JlVar fun_name]) in
            (stmts @ [JlAssign (res_var, imap)], res_var)
            *)

            (* introduce inline for-each loops *)
            let res_var = fresh_var_name () in
            let res_shp = JlFuncall("heh_add_arrays", [JlVar var1; JlVar var2]) in
            let res_stmt = JlAssign(res_var, JlFuncall("Array{Int}", [JlExpand res_shp])) in

            let fstmts = List.map
                    (fun var_gen_expr ->
                        let var_lb, x, var_ub, e = var_gen_expr in
                        let stmts, part_res = compile_stmts [] e in
                        let idx_var = "idx_" ^ fresh_var_name () in
                        let stmts = [JlAssign(x,
                            JlBinop(
                                JlFuncall("heh_tup2arr", [JlFuncall(
                                    "ind2sub", [JlVar res_var; JlVar idx_var])]),
                            "+", JlBinop(
                                JlVar var_lb, "-", JlVar "1", false),
                            false))]
                            @ stmts
                            @ [JlVoid (JlFuncall("setindex!",
                                [JlVar res_var; JlExpand (JlVar part_res);
                                JlExpand (
                                    JlBinop(
                                        JlVar x, "+", JlVar "1", false))]))] in
                        JlForeach (idx_var,
                                     JlFuncall("1:_length",
                                        [JlExpand (JlBinop(
                                            JlVar var_ub, ".-", JlVar var_lb, false))]),
                                   stmts))
                        var_gen_expr_lst in

            (stmts @ [res_stmt] @ fstmts, res_var)

let compile_main (e: Ast.expr) =
    let stmts, var = compile_stmts [] e in
    (* Think how do we present final result.  *)
    let comment = sprintf "%s" (Print.expr_to_str e) in
    let stmts = stmts @ [JlReturn (JlVar var)] in
    mk_jl_function "main" [] stmts ~comment:comment

let compile_jl_function name varlst expr =
    let rec vars_to_str vars =
        match vars with
        | [] -> ""
        | h :: t -> sprintf "%s %s" h @@ vars_to_str t
    in
    let comment = sprintf "Λ%s . %s"
                  (vars_to_str varlst)
                  (Print.expr_to_str expr) in
    let stmts, var = compile_stmts [] expr in
    let stmts = stmts @ [JlReturn (JlVar var)] in
    mk_jl_function name varlst stmts ~comment:comment

(* we indent this by one level as this is part of the module *)
let jl_funs =
  "@inline function heh_tup2arr(t::Tuple)\n"
^ "    return heh_create_array(t...)\n"
^ "end\n"
^ "\n"
^ "@inline function heh_arr2tup(a::Array)\n"
^ "    return (a...)\n"
^ "end\n"
^ "\n"
^ "@inline function heh_access_array(a::Array, t::Array)\n"
^ "    return heh_create_num(getindex(a, t+1...))\n"
^ "end\n"
^ "\n"
^ "@inline function heh_create_array(args::Int...)\n"
^ "    return Int[args...]\n"
^ "end\n"
^ "\n"
^ "@inline function heh_create_array(args::Array...)\n"
^ "    res = Array{Array{Int, length(size(args[1]))}, 1}(length(args))\n"
^ "\n"
^ "    for idx in eachindex(res)\n"
^ "        res[idx] = args[idx]\n"
^ "    end\n"
^ "\n"
^ "    flt = collect(Iterators.flatten(res))\n"
^ "    rsh = reshape(flt, tuple(length(args)...,size(args[1])...))\n"
^ "\n"
^ "    return rsh\n"
^ "end\n"
^ "\n"
^ "@inline function heh_create_array()\n"
^ "    return Array{Int,1}()\n"
^ "end\n"
^ "\n"
^ "@inline function heh_create_num(i::Int)\n"
^ "    res = Array{Int,0}()\n"
^ "    res[] = i\n"
^ "    return res\n"
^ "end\n"
^ "\n"
^ "@inline function heh_imap(s1::Array, s2::Array, f)\n"
^ "    res = Array{Array{Int, length(heh_arr2tup(s2))}, length(heh_arr2tup(s1))}(heh_arr2tup(s1))\n"
^ "\n"
^ "    for idx in eachindex(res)\n"
^ "        res[idx] = f(heh_tup2arr(ind2sub(res, idx))-1)\n"
^ "    end\n"
^ "\n"
^ "    if all(size(res) .!= 0) # FIXME this might be too extreme (arrays of shape\n"
^ "                            #       (0,) cannot be flattened)\n"
^ "        flt = collect(Iterators.flatten(res))\n"
^ "        rsh = reshape(flt, tuple(s1..., s2...))\n"
^ "    else\n"
^ "        rsh = reshape(res, tuple(s1..., s2...))\n"
^ "    end\n"
^ "    return rsh\n"
^ "end\n"
^ "\n"
^ "@inline function heh_reduce(f, neut::Array, a::Array)\n"
^ "    res = neut\n"
^ "    for x in eachindex(a)\n"
^ "        res = f(a[x], res)\n"
^ "    end\n"
^ "\n"
^ "    return res\n"
^ "end\n"
^ "\n"
^ "@inline function heh_filter(p, a::Array)\n"
^ "    return filter(p, a)\n"
^ "end\n"
^ "\n"
^ "@inline function heh_shape(a::Array)\n"
^ "    return heh_tup2arr(size(a))\n"
^ "end\n"
^ "\n"
^ "@inline function heh_islim(a::Any)\n"
^ "    return false\n"
^ "end\n"
^ "\n"
^ "@inline function heh_inrange(iv::Array, lb::Array, ub::Array)\n"
^ "    return all(lb .<= iv) && all(iv .< ub)\n"
^ "end\n"
^ "\n"
^ "@inline function heh_add_arrays(A::Array, B::Array)\n"
^ "    if size(A) == (0,) # empty array\n"
^ "        return B\n"
^ "    elseif size(B) == (0,)\n"
^ "        return A\n"
^ "    else\n"
^ "        return A .+ B\n"
^ "    end\n"
^ "end\n"
^ "\n"
^ "@inline function _length(args::Int...)\n"
^ "    return reduce(*, args)\n"
^ "end\n"
^ "\n"

let call_jl_main =
  "println(main())\n"
^ "\n"

let compile e m =
    let p = Lifting.StringMap.fold
               (fun var varlist_expr p ->
                let varlst, expr = varlist_expr in
                let jl_fun = compile_jl_function var varlst expr in
                jl_fun :: p)
               m
               [] in

    let p = p @ [compile_main e] in
    let out = open_out !Globals.julia_out_file in
    fprintf out "%s" jl_funs;
    fprintf out "# --- generated julia-code ---\n\n";
    print_jl_prog out p;
    Printf.fprintf out "%s" call_jl_main;
    close_out out