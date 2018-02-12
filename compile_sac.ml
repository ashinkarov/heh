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

type sac_type =
    | SacInt
    | SacBool

type sac_prog =
    sac_function list

and sac_function = { name: string;
                     params: sac_params;
                     body: sac_stmt list;
                     comment: string }

and sac_params = (sac_type * string) list

and sac_stmt =
    | SacAssign of string * sac_expr
    | SacReturn of sac_expr
    | SacCond of sac_expr * (sac_stmt list) * (sac_stmt list)

and sac_expr =
    | SacFalse
    | SacTrue
    | SacNum of int
    | SacArray of sac_expr list
    | SacVar of string
    (*| SacBinop of sac_binop * sac_expr * sac_expr *)
    | SacFuncall of string * (sac_expr list)
    (* XXX only genarray withloops for now *)
    | SacWith of (sac_generator * sac_stmt list * sac_expr) list * sac_genarray

and sac_generator = sac_expr * string * sac_expr

(* Default element, size *)
and sac_genarray = sac_expr * sac_expr


(*and sac_binop =
    | SacOpPlus
    | SacOpMinus
    | SacOpMul
    | SacOpDiv*)

(* Helper mk_ functions.  *)
let mk_sac_function ?(comment="") name params stmts =
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



let rec print_sac_expr oc level e =
    match e with
    | SacTrue ->
            fprintf oc "true"

    | SacFalse ->
            fprintf oc "false"

    | SacNum n ->
            fprintf oc "%d" n

    | SacArray lst ->
            fprintf oc "[";
            print_sep_list oc (print_sac_expr oc level) lst;
            fprintf oc "]"

    | SacVar x ->
            fprintf oc "%s" x

    | SacFuncall (f, args) ->
            fprintf oc "%s (" f; print_sep_list oc (print_sac_expr oc level) args; fprintf oc ")"

    | SacWith (partlst, with_expr) ->
            fprintf oc "with {\n";
            List.fold_left (fun () part -> print_wl_part oc (level+1) part) () partlst;
            prind oc level; fprintf oc "}: ";
            let shp, def = with_expr in
            fprintf oc "genarray ("; print_sac_expr oc level shp;
            fprintf oc ", "; print_sac_expr oc level def;
            fprintf oc ")"

and print_wl_part oc level part =
    let gen, stmts, expr = part in
    prind oc level; print_gen oc level gen;
    fprintf oc "\n";
    print_sac_stmts oc level stmts;
    prind oc level; fprintf oc ": ";
    print_sac_expr oc level expr;
    fprintf oc ";\n"

and print_gen oc level gen =
    let lb, x, ub = gen in
    fprintf oc "("; print_sac_expr oc level lb;
    fprintf oc " <= %s < " x;
    print_sac_expr oc level ub;
    fprintf oc ")"

and print_sac_stmt oc level s =
    match s with
    | SacAssign (s, e) ->
            prind oc level; fprintf oc "%s = " s;
            print_sac_expr oc level e; fprintf oc ";\n"

    | SacCond (e, stmts1, stmts2) ->
            prind oc level;
            fprintf oc "if ("; print_sac_expr oc level e; fprintf oc ")\n";
            print_sac_stmts oc level stmts1;
            prind oc level;
            fprintf oc "else\n";
            print_sac_stmts oc level stmts2;

    | SacReturn (e) ->
            prind oc level;
            fprintf oc "return ";
            print_sac_expr oc level e;
            fprintf oc ";\n"

and print_sac_stmts oc level stmts =
    prind oc level; fprintf oc "{\n";
    List.fold_left (fun () s -> print_sac_stmt oc (level+1) s) () stmts;
    prind oc level; fprintf oc "}\n"

let print_sac_params oc (params: sac_params) =
    fprintf oc "(";
    print_sep_list oc (fun (param: sac_type * string) ->
                    let t, name = param in
                    match t with
                    | SacInt -> fprintf oc "int[*] %s" name
                    | SacBool -> fprintf oc "bool[*] %s" name)
                   params;
    fprintf oc ")"


let print_sac_fun oc f =
    if f.comment <> "" then
        fprintf oc "// %s\n" f.comment;

    if f.name = "main" then
        fprintf oc "int\nmain "
    else
        fprintf oc "int[*]\n%s " f.name
    ;
    print_sac_params oc f.params;
    fprintf oc "\n";
    print_sac_stmts oc 0 f.body


let print_sac_prog oc p =
    List.fold_left (fun () f -> print_sac_fun oc f; fprintf oc "\n\n") () p




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
            (stmts @ [SacAssign (res_var, SacFalse)], res_var)

    | { expr_kind = ETrue } ->
            let res_var = fresh_var_name () in
            (stmts @ [SacAssign (res_var, SacTrue)], res_var)

    | { expr_kind = ENum n } ->
            let n = Ordinals.ord_to_nat n in
            let res_var = fresh_var_name () in
            (stmts @ [SacAssign (res_var, SacNum n)], res_var)

    | { expr_kind = EVar (x) } ->
            (stmts, x)

    | { expr_kind = EArray (lst) } ->
            let stmts_lst, vars =
                List.split @@ List.map (compile_stmts []) lst in
            let res_var = fresh_var_name () in
            let res_arr = SacArray (List.map (fun x -> SacVar x) vars) in
            (stmts @ List.flatten stmts_lst @ [SacAssign (res_var, res_arr)],
             res_var)

    | { expr_kind = EBinOp (op, e1, e2) } ->
            let stmts, var1 = compile_stmts stmts e1 in
            let stmts, var2 = compile_stmts stmts e2 in
            let res_var = fresh_var_name () in
            let opname =
                match op with
                | OpPlus  -> "_add_SxS_"
                | OpMinus -> "_sub_SxS_"
                | OpDiv   -> "_div_SxS_"
                | OpMod   -> "_mod_SxS_"
                | OpMult  -> "_mul_SxS_"
                | OpLt    -> "_lt_SxS_"
                | OpLe    -> "_le_SxS_"
                | OpGt    -> "_gt_SxS_"
                | OpGe    -> "_ge_SxS_"
                | OpEq    -> "_eq_SxS_"
                | OpNe    -> "_ne_SxS_"
            in
            let funcall = SacFuncall (opname, [SacVar var1; SacVar var2]) in
            (stmts @ [SacAssign (res_var, funcall)], res_var)

    | { expr_kind = EUnary (op, e1) } ->
            let stmts, var1 = compile_stmts stmts e1 in
            let opname =
                match op with
                | OpShape -> "_shape_A_"
                | OpIsLim -> "is_limit_ordinal" in
            let res_var = fresh_var_name () in
            let funcall = SacFuncall (opname, [SacVar var1]) in
            (stmts @ [SacAssign (res_var, funcall)], res_var)

    | { expr_kind = ELambda (x, e) } ->
            failwith "Lambdas are not supported in sac, they should have been lifted."

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
            let fargs = List.map (fun x -> SacVar x) @@ List.tl vars in
            let funcall = SacFuncall (fname, fargs) in
            (stmts @ argstmts @ [SacAssign (res_var, funcall)], res_var)

    | { expr_kind = ESel (e1, e2) } ->
            let stmts, var1 = compile_stmts stmts e1 in
            let stmts, var2 = compile_stmts stmts e2 in
            let res_var = fresh_var_name () in
            let funcall = SacFuncall ("_sel_VxA_", [SacVar var2; SacVar var1]) in
            (stmts @ [SacAssign (res_var, funcall)], res_var)

    | { expr_kind = ECond (e1, e2, e3) } ->
            let stmts1, var1 = compile_stmts stmts e1 in
            let stmts2, var2 = compile_stmts [] e2 in
            let stmts3, var3 = compile_stmts [] e3 in
            let res_var = fresh_var_name () in
            let stmts2 = stmts2 @ [SacAssign (res_var, SacVar var2)] in
            let stmts3 = stmts3 @ [SacAssign (res_var, SacVar var3)] in
            (stmts1 @ [SacCond (SacVar var1, stmts2, stmts3)], res_var)

    | { expr_kind = ELetRec (s, e1, e2) } ->
            let stmts1, var1 = compile_stmts [] e1 in
            let stmts1 = stmts1 @ [SacAssign (s, SacVar var1)] in
            let stmts2, var2 = compile_stmts [] e2 in
            (stmts @ stmts1 @ stmts2, var2)

    | { expr_kind = EImap (e_out, e_in, ge_lst) } ->
            let stmts, var1 = compile_stmts stmts e_out in
            let stmts, var2 = compile_stmts stmts e_in in
            (* Concat shape vectors into shp_var *)
            let shp_var = fresh_var_name () in
            let funcall = SacFuncall ("vec_concat", [SacVar var1; SacVar var2]) in
            let stmts = stmts @ [SacAssign (shp_var, funcall)] in
            (* Emit code for all the generator expressions.  *)
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
            let wl_parts = List.map
                           (fun var_gen_expr ->
                            let var_lb, x, var_ub, e = var_gen_expr in
                            let stmts, res_var = compile_stmts [] e in
                            let sac_gen = (SacVar var_lb, x, SacVar var_ub) in
                            (sac_gen, stmts, SacVar res_var))
                           var_gen_expr_lst in

            let res_var = fresh_var_name () in
            let wl_kind = (SacVar shp_var, SacNum 0) in
            let wl = SacWith (wl_parts, wl_kind) in
            (stmts @ [SacAssign (res_var, wl)], res_var)

    (* TODO reduce and filter are still missing.  *)

    | _ -> failwith "bad statement"

let compile_main (e: Ast.expr) =
    let stmts, var = compile_stmts [] e in
    (* Think how do we present final result.  *)
    let comment = Printf.sprintf "%s" (Print.expr_to_str e) in
    let stmts = stmts @ [SacReturn (SacVar var)] in
    mk_sac_function "main" [] stmts ~comment:comment

let compile_sac_function name varlst expr =
    let rec vars_to_str vars =
        match vars with
        | [] -> ""
        | h :: t -> Printf.sprintf "%s %s" h @@ vars_to_str t
    in
    let comment = Printf.sprintf "Λ%s . %s"
                  (vars_to_str varlst)
                  (Print.expr_to_str expr) in
    let params = List.map (fun x -> (SacInt, x)) varlst in
    let stmts, var = compile_stmts [] expr in
    let stmts = stmts @ [SacReturn (SacVar var)] in
    mk_sac_function name params stmts ~comment:comment



let sac_funs =
  "// internal functions\n"
^ "bool\n"
^ "is_limit_ordinal (int[*] x)\n"
^ "{\n"
^ "    return false;\n"
^ "}\n"
^ "\n"
^ "\n"
^ "int[.]\n"
^ "vec_concat (int[.] x, int[.] y)\n"
^ "{\n"
^ "  l1 = _sel_VxA_ ([0], _shape_A_ (x));\n"
^ "  l2 = _sel_VxA_ ([0], _shape_A_ (y));\n"
^ "\n"
^ "  return with {\n"
^ "      ([0] <= iv < [l1]):     _sel_VxA_ (iv, x);\n"
^ "      ([l1] <= iv < [_add_SxS_ (l1, l2)]): _sel_VxA_ ([_sub_SxS_ (_sel_VxA_ ([0], iv), l1)], y);\n"
^ "  }: genarray ([_add_SxS_ (l1, l2)], 0);\n"
^ "}\n\n\n"



let compile e m =
    let p = Lifting.StringMap.fold
               (fun var varlist_expr p ->
                let varlst, expr = varlist_expr in
                let sac_fun = compile_sac_function var varlst expr in
                sac_fun :: p)
               m
               [] in

    let p = p @ [compile_main e] in
    let out = open_out !Globals.sac_out_file in
    fprintf out "%s" sac_funs;
    fprintf out "// --- sac-code ---\n";
    print_sac_prog out p;
    close_out out
