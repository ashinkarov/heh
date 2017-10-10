(*
 * Copyright (c) 2017, Artem Shinkarov <artyom.shinkaroff@gmail.com>
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

  ]

let main =
    Arg.parse_argv
        Sys.argv
        arglist
        (fun x -> if !fname <> "" then
                    raise (ImapFailure "Multiple input files found on command line")
                  else
                    fname := x)
        usage;

    let file = open_in !fname in
    let open Lexing in
    let lexbuf = from_channel file in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = !fname };
    let e = Parser.prog lexbuf in
    let e = Traverse.app_to_hof e in
    printf "%s\n" (Print.expr_to_str e);
    (*let st, p = Eval.eval (Storage.st_new ()) (Env.env_new ()) e in
    if !print_storage_on then
        printf "%s\n" (Storage.st_to_str st);
    printf "res: %s = %s\n\n"  p (Print.value_to_str @@ Storage.st_lookup st p);*)
    close_in file

let () = main
