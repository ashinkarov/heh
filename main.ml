
open Printf;;
open Ast;;
open Traverse;;
open Ordinals;;

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

let main =
    Arg.parse_argv
        Sys.argv
        arglist
        (fun x -> if !fname <> "" then
                    raise (ImapFailure "Multiple input files found on command line")
                  else
                    fname := x)
        usage;
    
    test_ordinals ();
   
    let file = open_in !fname in
    let lexbuf = Lexing.from_channel file in
    let e = Parser.prog Lexer.token lexbuf in
    printf "%s" (expr_to_str (app_to_hof e));
    close_in file

let () = main
