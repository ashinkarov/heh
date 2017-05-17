
(* XXX these variables are not in use and serve an example on how to handle
   command line arguments.  *)
let somestr = ref ""

(* Whether debug output is on.  *)
let debug_on = ref false

(* The name of the file we parse.  *)
let fname = ref ""

(* Helper string that will be printed at the begining of the help message
   triggered by --help flag.  *)
let usage = "usage: "

let debug msg = 
    if !debug_on then
        Printf.printf "%s\n" msg
;;
