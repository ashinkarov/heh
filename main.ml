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


open Printf
open Ast
open Globals
open Lexer

let arglist = [
    ("-d",
        Arg.Set (debug_on),
        ": enable debug output");

    ("-nomemo",
        Arg.Clear (memo_on),
        ": disable memoization when computing lazy imaps");

    ("-finite-imap-strict",
        Arg.Set (finite_imap_strict_on),
        ": enable strict evaluation of imaps of finite shapes");

    ("-show-storage",
        Arg.Set (print_storage_on),
        ": print storage at the end of evaluation");

    ("-force-letrec-imap",
        Arg.Set (force_letrec_imap),
        ": force finite imap closures when evaluating letercs");

    ("-lift-lambdas",
        Arg.Set (flag_lift_lambdas),
        ": lift local functions and use them in the evaluation");

    ("-compile-sac",
        Arg.Set_string (sac_out_file),
        "<fname> : generate sac code and save it to <fname>");

    ("-compile-c",
        Arg.Set_string (c_out_file),
        "<fname> : generate c code and save it to <fname>");
  ]


let compile_sac e =
    let m, st, env, e = Lifting.lift_lambdas e in
    try 
        Compile_sac.compile e m
    with 
        | _ -> Printf.printf "error: sac backend is a wee bit shite, sorre, pal :(\n"

let compile_c e =
    let m, st, env, e = Lifting.lift_lambdas e in
    try 
        Compile_c.compile e m
    with 
        | _ -> Printf.printf "error: c backend is a wee bit shite, sorre, pal :(\n"

let eval_prog e =
    let st, env, e =
        if !flag_lift_lambdas then
            let m, st, env, e = Lifting.lift_lambdas e in
            (st, env, e)
        else
            (Storage.st_new (), Env.env_new (), e)
    in
    printf "%s\n" (Print.expr_to_str e);
    flush stdout;
    let st, p = Eval.eval st env e in
    if !print_storage_on then
        printf "%s\n" (Storage.st_to_str st);
    printf "res: %s = %s\n\n"  p (Print.value_to_str @@ Storage.st_lookup st p)


let main () =
    Arg.parse
        arglist
        (fun x -> if !fname_set then
                    raise (ImapFailure "Multiple input files found on command line")
                  else begin
                      fname := x; fname_set := true
                  end)
        usage;

    (* If no input files are passed as arguments, assume that
     * we are reading from stdin.
     *)
    let file = if !fname_set
               then open_in !fname
               else (fname := "<stdin>"; fname_set := true; stdin) in
    
    let open Lexing in
    let lexbuf = from_channel file in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = !fname };
    let e = Parser.prog lexbuf in
    let _, e = Traverse.app_to_hof () e in
    if !sac_out_file <> "" then
        compile_sac e
    else if !c_out_file <> "" then
        compile_c e
    else begin
        eval_prog e
    end
    ;
    close_in file

let _ = main ()

