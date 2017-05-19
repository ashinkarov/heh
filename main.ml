
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
