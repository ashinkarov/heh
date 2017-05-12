
exception EnvFailure of string

type env = (string * string) list;;

let env_new: unit -> env = fun () ->
    []
;;

let env_add e v p =
    (v, p) :: e
;;

let rec env_lookup e v =
    match e with
    | [] -> raise (EnvFailure
                   (Printf.sprintf "lookup of variable `%s' failed" v))
    | (v', p') :: tl ->
        if v' = v then
            p'
        else
            env_lookup tl v
;;

let env_to_str e =
    if List.length e = 0 then
        "[]"
    else
        String.concat ", " (List.map (fun vp ->
                                      let v, p = vp in
                                      Printf.sprintf "%s |-> %s" v p) e)
;;


let test_env () =
    let e = env_new () in
    let e = env_add e "x" "p1" in
    let e = match env_lookup e "x" with
            | "p1" -> e
            | _ -> failwith "environment lookup is broken" in
    let e = env_add e "x" "p2" in
    let e = try
               let _ = env_lookup e "y" in
               failwith "environment lookup expected to fail on non-existing variable"
            with
                EnvFailure _ -> e in
    if List.length e = 2 then
        Printf.printf "env tests passed\n"
    else
        Printf.printf "env tests failed\n"
;;

