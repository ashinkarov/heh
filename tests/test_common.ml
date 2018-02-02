(*
   Generic functions used in tests.
*)

let parse_prog prg =
    let lexbuf = Lexing.from_string prg in
    Globals.fname := Printf.sprintf "prog: `%s'" prg;
    let e = Parser.prog lexbuf in
    let _, e = Traverse.app_to_hof () e in
    e

let eval_prog prg =
    let e = parse_prog prg in
    Eval.eval (Storage.st_new ()) (Env.env_new ()) e


