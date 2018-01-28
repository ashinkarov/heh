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

exception EnvFailure of string

type env = (string * string) list;;

let env_new: unit -> env = fun () ->
    []

let env_add e v p =
    (v, p) :: e

let rec env_lookup e v =
    match e with
    | [] -> raise (EnvFailure
                   (Printf.sprintf "lookup of variable `%s' failed" v))
    | (v', p') :: tl ->
        if v' = v then
            p'
        else
            env_lookup tl v

let env_to_str e =
    if List.length e = 0 then
        "[]"
    else
        String.concat ", " (List.map (fun vp ->
                                      let v, p = vp in
                                      Printf.sprintf "%s |-> %s" v p) e)

