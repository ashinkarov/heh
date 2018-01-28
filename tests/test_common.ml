(*
   Generic functions used in tests.
*)

let eval_prog prg =
    let lexbuf = Lexing.from_string prg in
    Globals.fname := Printf.sprintf "prog: `%s'" prg;
    let e = Parser.prog lexbuf in
    let _, e = Traverse.app_to_hof () e in
    Eval.eval (Storage.st_new ()) (Env.env_new ()) e


