(*
 * ISC License
 *
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

(* XXX this is an example on how to handel command-line arguments.  *)
let arglist = [
    ("-s",
        Arg.String (fun s -> somestr := s),
        ": follows -s sets some string");

    ("-d",
        Arg.Set (debug_on),
        ": enable debug output");

    ("-nomemo",
        Arg.Clear (memo_on),
        ": disable memoization when computing lazy imaps");

    ("-finite-imap-strict",
        Arg.Set (finite_imap_strict_on),
        ": enable strict evaluation of imaps of finite shapes");
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
    let lexbuf = Lexing.from_channel file in
    let e = Parser.prog Lexer.token lexbuf in
    let e = Traverse.app_to_hof e in
    printf "%s\n" (Print.expr_to_str e);
    let st, p = Eval.eval (Storage.st_new ()) (Env.env_new ()) e in
    printf "%s\nres: %s = %s\n\n" (Storage.st_to_str st) p (Print.value_to_str @@ Storage.st_lookup st p);
    close_in file

let () = main
