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


(* XXX these variables are not in use and serve an example on how to handle
   command line arguments.  *)
let somestr = ref ""

(* Whether debug output is on.  *)
let debug_on = ref false

(* Whether we memoize values when evaluating imaps.  *)
let memo_on = ref true

(* Whether we evaluate imaps of finite shape strictly.  *)
let finite_imap_strict_on = ref false

(* Force imap closures when evaluating letrecs, given that
 * the imap is finite.  That is if in expression `letrec x = e in ...`
 * `e` evaluates to an imap closure and its shape is finite,
 * turn `e` into strict array.  *)
let force_letrec_imap = ref false

(* Whether we print the storage after the result has been evaluated.  *)
let print_storage_on = ref false

(* Whether we lift lambdas and use them in evaluation.  *)
let flag_lift_lambdas = ref false


(* The name of the file we parse.  *)
let fname = ref ""
let fname_set = ref false

(* Helper string that will be printed at the begining of the help message
   triggered by --help flag.  *)
let usage = "usage: "

let debug msg =
    if !debug_on then
        Printf.printf "%s\n" msg

