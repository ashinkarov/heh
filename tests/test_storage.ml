open OUnit
open Ast
open Value
open Ordinals
open Storage

open Test_common

let test_storage _ =
    let s = st_new () in
    let s = st_add s "p1" 1 (VNum (int_to_ord 1)) in
    let s = st_add s "p2" 1 (VNum (int_to_ord 2)) in
    let s = st_update s "p1" (VNum (int_to_ord 42)) in
    assert_equal ~msg:"storage lookup p1"
                 (st_lookup s "p1") (VNum (int_to_ord 42));
    let try_add () =
        st_add s "p1" 1 (VNum (int_to_ord 10)) in
    assert_raises (StorageFailure "pointer `p1': already exists")
                  try_add;
    let s = st_remove s "p1" in
    let s = st_remove s "p2" in
    let try_remove () =
         st_remove s "p3" in
    assert_raises (StorageFailure "pointer `p3': doesn't exist --- cannot remove")
                  try_remove;
    let try_update () =
        st_update s "p1" (VNum (int_to_ord 22)) in
    assert_raises (StorageFailure "pointer `p1': doesn't exist --- cannot update")
                  try_update;
    assert_equal ~msg:"storage length expected to be 0"
                 (Hashtbl.length s) 0


let rec print_list = function
[] -> print_string "\n"
| e::l -> print_string e ; print_string ", " ; print_list l


let test_fv prog fv =
    let e = parse_prog prog in
    let lst = Ast.free_vars_lst e in
    assert_equal ~msg:(Printf.sprintf "testing free vars for '%s'" prog)
                 (lst) fv

let test_free_vars _ =
    test_fv "1" [];
    test_fv "x-1" ["x"];
    test_fv "(\\x.x) x" ["x"];
    test_fv "x (\\x.1)" ["x"; ];
    test_fv "(\\x.\\y.x y) x" ["x"];
    test_fv "false" [];
    test_fv "[1,2,3]" [];
    test_fv "[x,2,\\y.y]" ["x"];
    test_fv "\\x.x + 1" [];
    test_fv "\\x.x y z" ["z"; "y"];
    test_fv "letrec f = \\x.f x in f 1" [];
    test_fv "letrec f = z in f 1" ["z"];
    test_fv "if x then 0 else 1" ["x"];
    test_fv "if x then x else y" ["y"; "x"; "x"];
    test_fv "if x = 0 then 0 else x-1" ["x"; "x"];
    test_fv "if x then (\\x.\\y.x y) f (x-1) else 0" ["x"; "f"; "x"];
    test_fv "\\x.if x then x else y" ["y"];
    test_fv "imap [10] {_(iv): a.[iv.[0] - 1]" ["a"];
    test_fv "imap [10] {x <= iv < y: 1" ["x"; "y"];
    test_fv "imap [10] {[0] <= iv < [1]: x, [1] <= jv < [10]: y" ["x"; "y"];
    ()

let test_rc_prog prog =
    let st, p = eval_prog prog in
    assert_equal ~msg:(Printf.sprintf "testing reference count for '%s'" prog)
                 (Storage.final_storage_consistent st p) ()

let rc_progs = [  "1"

(*let prog01 =*); "2 + 3"

(*let prog02 =*); "\\x.x"

(*let prog03 =*); "(\\x.x) 2"

(*let prog04 =*); "(\\x.\\y.x) 2"

(*let prog05 =*); "(\\f.(f 1) + (f 1)) ((\\x.\\y.x) 2)"

(*let prog06 =*); "(\\f.(\\x.f (\\v.((x x) v))) (\\x.f (\\v.((x x) v)))) "
                  ^ "(\\f.\\x.if x = 0 then 0 else x + f (x-1)) 2"

(*let prog07 =*); "letrec f = 1 in f"

(*let prog08 =*); "letrec f = \\x.if x = 0 then x else f (x-1) in f 4"

(*let prog09 =*); "(\\x.\\y.\\z.\\w.x + x + x) 2 3 4"

(*let prog10 =*); "(\\x.\\y.x + (\\z.1) (\\w.x+x+x)) 2 3"

(*let prog11 =*); "(\\f.\\x.f 1) ((\\f.\\x.f 1) ((\\x.\\y.x) 2))"

(*let prog12 =*); "(\\x.\\y. if (x+x+x) = 0 then x + x + x else x) 1 2"

(*let prog13 =*); "(\\x.\\y. if x = 0 then (\\z.y) (x + x + x) else x) 0 2"

(*let prog14 =*); "(\\x.\\y. if x = 0 then if x = 0 then x + x + x else 0 else x) 0 2"

(*let prog15 =*); "(letrec f = \\x.if x = 0 then 5 else f (x-1) in \\x.f x) 0"

(*let prog16 =*); "letrec f = \\x.f x in (\\x.1) f "

(*let prog17 =*); "(\\z.letrec f = \\x.f x in (\\x.1) f) 3"

(*let prog18 =*); "letrec f = \\x.x+1 in f  3"

(*let prog19 =*); "(\\g.\\x.g x) (letrec f = \\x.x+1 in f)  3"

(*let prog20 =*); "(\\g.\\x.g x) (letrec f = \\x.if x = 0 then x else x + (f (x-1)) in f)  3"

(*let prog21 =*); "letrec f = \\x.f (f x) in 5"

(*let prog22 =*); "letrec f = \\x.if x = 0 then x else f (x-1) in f 1 + f 1"
(*let prog23 =*); "(\\f.(f 1)) ((\\x.\\y.x = 0) 2)"

(*let prog24 =*); "(\\x.letrec f = \\y.x in (f x) + x) 1"

(*let prog25 =*); "(\\x.letrec f = x in f + x + x) 1"

(*let prog26 =*); "letrec odd = \\x.if x = 0 then 0 else x + odd (x - 1) in "
                 ^"             letrec even = \\x.if (x-1) = 0 then 1 else even (x-1) + odd x in "
                 ^"             even 3"

(*let prog27 =*); "(\\x.letrec f = \\y.if x = 0 then f (x-1) else 42 in "
                 ^"                letrec g = \\z.x + (f z) in  g (x + 1) + f (2)) 11 "

(*let prog28 =*); "(\\x.letrec f = \\y.x + y in f (f 1)) 11"

(*let prog29 =*); "letrec f = \\x.if x = 0 then 1 else (letrec g = (\\x.\\y.x y) f in g) (x-1) in f 3"

(*let prog30 =*); "(\\x.letrec f = 1 in x + x + x) 1"

(*let prog31 =*); "(\\x.letrec f = \\y.1 in x + x + x) 1"

(*let prog32 =*); "(\\x.letrec f = \\y.x+x+x in f x + x + x) 1"

(*let prog33 =*); "(\\x.letrec f = \\y.x+x+x in 1) 1"

                ; "letrec f = (\\g.\\x.if x = 0 then g x else 1) "
                 ^"           (letrec g = (\\h.\\x.h x) (letrec h = \\x.x + (g x)  in h) in g) in "
                 ^"\\x.f (f (f 1))"

                ; "letrec _odd = \\even.\\x.even (x - 1) in "
                 ^"letrec _even = \\odd.\\x.if x = 0 then 0 else odd (x - 1) in "
                 ^"letrec odd = _odd (_even odd) in "
                 ^"letrec even = _even odd in "
                 ^"odd 3"

                ; "letrec g = \\F.\\x.if x = 0 then x else (F (x-1)) in "
                 ^"letrec f = g (g f) in f 2"

                ; "letrec fix = \\f.f (\\x.(fix f) x) in "
                 ^"fix (\\fac.\\n.if n = 0 then 1 else n + (fac (n-1))) 3"

                ; "(\\f.(\\x.f (\\v.((x x) v))) (\\x.f (\\v.((x x) v)))) "
                 ^"(\\f.\\x.if x = 0 then 0 else x + f (x-1)) 2"

                ; "letrec g = \\F.\\x.if x = 0 then 0 else (F (x-1)) + (F (x-1)) + 1 in "
                 ^"letrec f = g (g f) in f 3"
]

let test_rc _ =
    List.fold_left (fun () prog -> test_rc_prog prog) () rc_progs
