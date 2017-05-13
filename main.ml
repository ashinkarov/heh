
open Printf
open Ast

(* XXX these variables are not in use and serve an example on how to handle
   command line arguments.  *)
let somestr = ref ""
let someint = ref 0

(* The name of the file we parse.  *)
let fname = ref ""

(* Helper string that will be printed at the begining of the help message
   triggered by --help flag.  *)
let usage = "usage: "


(* XXX this is an example on how to handel command-line arguments.  *)
let arglist = [
    ("-s", Arg.String (fun s -> somestr := s), ": follows -s sets some string");
    ("-d", Arg.Int    (fun d -> someint := d), ": some int parameter");
  ]


(* TODO factor this out into a separate module and compilation target, e.g. tests.  *)
let run_tests () =
    Ordinals.test_ordinals ();
    Storage.test_storage ();
    Env.test_env ()
;;


let main =
    Arg.parse_argv
        Sys.argv
        arglist
        (fun x -> if !fname <> "" then
                    raise (ImapFailure "Multiple input files found on command line")
                  else
                    fname := x)
        usage;

    (* run_tests (); *)
    let file = open_in !fname in
    let lexbuf = Lexing.from_channel file in
    let e = Parser.prog Lexer.token lexbuf in
    printf "%s\n" (Ast.expr_to_str (Traverse.app_to_hof e));
    let st, p = Eval.eval (Storage.st_new ()) (Env.env_new ()) e in
    printf "%s\n%s\n\n" (Storage.st_to_str st) p;
    close_in file

let () = main
