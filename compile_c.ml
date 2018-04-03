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

type c_type =
    | CInt
    | CValue

and c_function = { name: string;
                   rettype: c_type;
                   params: c_params;
                   body: c_stmt list;
                   comment: string }

and c_params = (c_type * string) list

and c_stmt =
    | CAssign of (string option) * c_expr
    | CReturn of c_expr
    | CCond of c_expr * (c_stmt list) * (c_stmt list)
    | CIterLoop of c_expr * (c_stmt list)
    | CDecl of string * c_expr option

and c_expr =
    | CNum of int
    | CVar of string
    (*| SacBinop of sac_binop * sac_expr * sac_expr *)
    | CFuncall of string * (c_expr list)

(* Helper mk_ functions.  *)
let mk_c_function ?(comment="") name rettype params stmts =
    { name = name; rettype = rettype;
      params = params; body = stmts; comment = comment }

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



let rec print_c_expr oc level e =
    match e with
    | CNum n ->
            fprintf oc "%d" n

    | CVar x ->
            fprintf oc "%s" x

    | CFuncall (f, args) ->
            fprintf oc "%s (" f; print_sep_list oc (print_c_expr oc level) args; fprintf oc ")"

and print_c_stmt oc level s =
    match s with
    | CAssign (s, e) ->
            prind oc level;
            (match s with
             | None -> ()
             | Some v -> fprintf oc "%s = " v);
            print_c_expr oc level e; fprintf oc ";\n"

    | CCond (e, stmts1, stmts2) ->
            prind oc level;
            fprintf oc "if ("; print_c_expr oc level e; fprintf oc ")\n";
            print_c_stmts oc level stmts1;
            prind oc level;
            fprintf oc "else\n";
            print_c_stmts oc level stmts2;

    | CReturn (e) ->
            prind oc level;
            fprintf oc "return ";
            print_c_expr oc level e;
            fprintf oc ";\n"

    | CIterLoop (e, stmts) ->
            prind oc level;
            print_c_expr oc level e;
            fprintf oc "\n";
            print_c_stmts oc level stmts;
            fprintf oc "\n"


    | CDecl (s, eopt) ->
            prind oc level;
            fprintf oc "value %s" s;
            (match eopt with
             | None -> ()
             | Some e -> fprintf oc " = "; print_c_expr oc level e);
            fprintf oc ";\n"


and print_c_stmts oc level stmts =
    prind oc level; fprintf oc "{\n";
    List.fold_left (fun () s -> print_c_stmt oc (level+1) s) () stmts;
    prind oc level; fprintf oc "}\n"


let print_c_type oc t =
    let s = match t with
    | CInt -> "int"
    | CValue -> "value" in
    fprintf oc "%s" s

let print_c_params oc (params: c_params) =
    fprintf oc "(";
    print_sep_list oc (fun (param: c_type * string) ->
                    let t, name = param in
                    print_c_type oc t;
                    fprintf oc " %s" name)
                   params;
    fprintf oc ")"


let print_c_fun_header oc f =
    if f.name <> "main" then
        fprintf oc "static inline ";
    print_c_type oc f.rettype;
    fprintf oc "\n%s " f.name;
    print_c_params oc f.params

let print_c_fun oc f =
    if f.comment <> "" then
        fprintf oc "// %s\n" f.comment;

    print_c_fun_header oc f;
    fprintf oc "\n";
    print_c_stmts oc 0 f.body


let print_c_prog oc p =
    List.fold_left (fun () f -> 
                    if f.name <> "main" then
                    begin
                        print_c_fun_header oc f;
                        fprintf oc ";\n"
                    end) () p;
    List.fold_left (fun () f -> print_c_fun oc f; fprintf oc "\n\n") () p


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
            let fcall = CFuncall ("mk_scalar", [CNum 0]) in
            (stmts @ [CDecl (res_var, Some fcall)], res_var)

    | { expr_kind = ETrue } ->
            let res_var = fresh_var_name () in
            let fcall = CFuncall ("mk_scalar", [CNum 1]) in
            (stmts @ [CDecl (res_var, Some fcall)], res_var)

    | { expr_kind = ENum n } ->
            let n = Ordinals.ord_to_nat n in
            let res_var = fresh_var_name () in
            let fcall = CFuncall ("mk_scalar", [CNum n]) in
            (stmts @ [CDecl (res_var, Some fcall)], res_var)

    | { expr_kind = EVar (x) } ->
            (stmts, x)

    | { expr_kind = EArray (lst) } ->
            let res_var = fresh_var_name () in
            if lst = [] then
                let fcall = CFuncall ("MK_EMPTY_VECTOR", []) in
                (stmts @ [CDecl (res_var, Some fcall)], res_var)
            else
                let stmts_lst, vars =
                    List.split @@ List.map (compile_stmts []) lst in

                let shp0 = CFuncall ("shape", [CVar (List.hd vars)]) in
                let dim0 = CFuncall ("VALUE_DIM", [CVar (List.hd vars)]) in
                let sh = CFuncall ("shape_concat",
                                   [CFuncall ("mk_array_val",
                                              [CNum 1;
                                               CFuncall ("CONST_VEC", [CNum 1]);
                                               CFuncall ("CONST_VEC", [CNum (List.length lst)])]);
                                    shp0]) in
                let dim = CFuncall ("PLUS", [dim0; CNum 1]) in
                let sh_var = fresh_var_name () in
                let res = CFuncall ("mk_array",
                                    [dim;
                                     CFuncall ("ARRAY_VALUE", [CVar sh_var])]) in

                let stmts = stmts @ List.flatten stmts_lst
                                  @ [CDecl (sh_var, Some sh);
                                     CDecl (res_var, Some res)] in

                let mod_stmt_lst =
                    List.mapi
                        (fun idx v ->
                         let fc = CFuncall ("modarray",
                                            [CVar res_var;
                                             CNum 1;
                                             CFuncall ("CONST_VEC", [CNum idx]);
                                             CVar v]) in
                         CAssign (None, fc))
                    vars in

            (stmts @ mod_stmt_lst, res_var)

    | { expr_kind = EBinOp (op, e1, e2) } ->
            let stmts, var1 = compile_stmts stmts e1 in
            let stmts, var2 = compile_stmts stmts e2 in
            let res_var = fresh_var_name () in
            let opname =
                match op with
                | OpPlus  -> "eval_plus"
                | OpMinus -> "eval_minus"
                | OpDiv   -> "eval_div"
                | OpMod   -> "eval_mod"
                | OpMult  -> "eval_mult"
                | OpLt    -> "eval_lt"
                | OpLe    -> "eval_le"
                | OpGt    -> "eval_gt"
                | OpGe    -> "eval_ge"
                | OpEq    -> "eval_eq"
                | OpNe    -> "eval_ne"
            in
            let funcall = CFuncall (opname, [CVar var1; CVar var2]) in
            (stmts @ [CDecl (res_var, Some funcall)], res_var)

    | { expr_kind = EUnary (op, e1) } ->
            let stmts, var1 = compile_stmts stmts e1 in
            let opname =
                match op with
                | OpShape -> "shape"
                | OpIsLim -> "is_limit_ordinal" in
            let res_var = fresh_var_name () in
            let funcall = CFuncall (opname, [CVar var1]) in
            (stmts @ [CDecl (res_var, Some funcall)], res_var)

    | { expr_kind = ELambda (x, e) } ->
            failwith "Lambdas are not supported in C, they should have been lifted."

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
            let fargs = List.map (fun x -> CVar x) @@ List.tl vars in
            let funcall = CFuncall (fname, fargs) in
            (stmts @ argstmts @ [CDecl (res_var, Some funcall)], res_var)

    | { expr_kind = ESel (e1, e2) } ->
            let stmts, var1 = compile_stmts stmts e1 in
            let stmts, var2 = compile_stmts stmts e2 in
            let res_var = fresh_var_name () in
            let funcall = CFuncall ("eval_sel", [CVar var1; CVar var2]) in
            (stmts @ [CDecl (res_var, Some funcall)], res_var)

    | { expr_kind = ECond (e1, e2, e3) } ->
            let stmts1, var1 = compile_stmts stmts e1 in
            let stmts2, var2 = compile_stmts [] e2 in
            let stmts3, var3 = compile_stmts [] e3 in
            let res_var = fresh_var_name () in
            let stmts2 = stmts2 @ [CAssign (Some res_var, CVar var2)] in
            let stmts3 = stmts3 @ [CAssign (Some res_var, CVar var3)] in
            let pred = CFuncall ("val_true", [CVar var1]) in
            (stmts1 @ [CDecl (res_var, None);
                       CCond (pred, stmts2, stmts3)], res_var)

    | { expr_kind = ELetRec (s, e1, e2) } ->
            let stmts1, var1 = compile_stmts [] e1 in
            let stmts1 = stmts1 @ [CDecl (s, Some (CVar var1))] in
            let stmts2, var2 = compile_stmts [] e2 in
            (stmts @ stmts1 @ stmts2, var2)

    | { expr_kind = EImap (e_out, e_in, ge_lst) } ->
            let stmts, var1 = compile_stmts stmts e_out in
            let stmts, var2 = compile_stmts stmts e_in in
            (* Concat shape vectors into shp_var *)
            let shp_var = fresh_var_name () in
            let funcall =  CFuncall ("shape_concat", [CVar var1; CVar var2]) in
            let stmts = stmts @ [CDecl (shp_var, Some funcall)] in
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

            let dim_var = fresh_var_name () in
            let it_val_var = fresh_var_name () in
            let empty_var = fresh_var_name () in
            let res_var = fresh_var_name () in

            let parts = List.map
                        (fun var_gen_expr ->
                        let var_lb, x, var_ub, e = var_gen_expr in
                        let stmts, part_res_var = compile_stmts [] e in
                        let set_it =
                            CAssign (None,
                                     CFuncall ("COPY_VEC_FROM_VAL",
                                               [CVar dim_var;
                                                CVar it_val_var;
                                                CVar var_lb])) in
                        let empty_fcall =
                            CFuncall ("iterator_empty",
                                      [CVar dim_var;
                                       CVar it_val_var;
                                       CFuncall ("ARRAY_VALUE", [CVar var_ub])]) in

                        let set_empt =
                            CAssign (Some empty_var, empty_fcall) in
                        let it_var = fresh_var_name () in
                        let iter_call =
                            CFuncall ("ITERATOR_LOOP",
                                      [CVar it_var;
                                       CVar empty_var;
                                       CVar dim_var;
                                       CFuncall ("ARRAY_VALUE", [CVar var_lb]);
                                       CVar it_val_var;
                                       CFuncall ("ARRAY_VALUE", [CVar var_ub])]) in

                        let idx_stmt =
                            CDecl (x, Some (CFuncall ("ITERATOR_TO_IDX",
                                                      [CVar it_var]))) in

                        let mod_call =
                            CAssign (None,
                                     CFuncall ("modarray",
                                               [CVar res_var;
                                                CVar dim_var;
                                                CFuncall ("ITERATOR_VALUE", [CVar it_var]);
                                                CVar part_res_var])) in
                        let iterloop =
                            CIterLoop (iter_call, [idx_stmt] @ stmts @ [mod_call]) in

                        [set_it; set_empt; iterloop])
                        var_gen_expr_lst in

            let res_decl = CDecl (res_var,
                                  Some (CFuncall ("mk_array_or_scal", [CVar shp_var]))) in

            let alloc_call = CAssign (None,
                                      CFuncall ("ALLOC_ITERATOR_PARTS",
                                                [CVar dim_var;
                                                 CVar empty_var;
                                                 CVar it_val_var;
                                                 CFuncall ("VALUE_DIM", [CVar res_var])])) in

            let stmts = stmts @ [res_decl; alloc_call] @ List.flatten parts in
            (stmts, res_var)

    | { expr_kind = EReduce (e_fun, e_neut, e_arg) } ->
            let stmts, fname = compile_stmts stmts e_fun in
            let stmts, neut  = compile_stmts stmts e_neut in
            let stmts, arg   = compile_stmts stmts e_arg in

            (* get the shape of the argument *)
            let res_var = fresh_var_name () in
            let stmt = CAssign (None, CFuncall ("REDUCE_LOOP",
                                                [CVar arg; CVar neut;
                                                 CVar fname; CVar res_var])) in
            (stmts @ [CDecl (res_var, None); stmt], res_var)

    | { expr_kind = EFilter (e_fun, e_arg) } ->
            let stmts, fname = compile_stmts stmts e_fun in
            let stmts, arg   = compile_stmts stmts e_arg in

            (* get the shape of the argument *)
            let res_var = fresh_var_name () in
            let stmt = CAssign (None, CFuncall ("FILTER_LOOP",
                                                [CVar arg; CVar fname;
                                                 CVar res_var])) in
            (stmts @ [CDecl (res_var, None); stmt], res_var)


let compile_main (e: Ast.expr) =
    let stmts, var = compile_stmts [] e in
    (* Think how do we present final result.  *)
    let comment = Printf.sprintf "%s" (Print.expr_to_str e) in
    let funcall = CFuncall ("print_value", [CVar var]) in
    let stmts = stmts @ [CAssign (None, funcall); CReturn (CNum 0)] in
    mk_c_function "main" CInt [] stmts ~comment:comment

let compile_c_function name varlst expr =
    let rec vars_to_str vars =
        match vars with
        | [] -> ""
        | h :: t -> Printf.sprintf "%s %s" h @@ vars_to_str t
    in
    let comment = Printf.sprintf "Λ%s . %s"
                  (vars_to_str varlst)
                  (Print.expr_to_str expr) in
    let params = List.map (fun x -> (CValue, x)) varlst in
    let stmts, var = compile_stmts [] expr in
    let stmts = stmts @ [CReturn (CVar var)] in
    mk_c_function name CValue params stmts ~comment:comment

let c_funs =
  "#include \"runtime.h\"\n"
^ "\n"
^ "\n"
^ "\n"

let compile e m =
    let p = Lifting.StringMap.fold
               (fun var varlist_expr p ->
                let varlst, expr = varlist_expr in
                let c_fun = compile_c_function var varlst expr in
                c_fun :: p)
               m
               [] in

    let p = p @ [compile_main e] in
    let out = open_out !Globals.c_out_file in
    fprintf out "%s" c_funs;
    fprintf out "// --- c-code ---\n";
    print_c_prog out p;
    close_out out
