open Printf

(* We are going to represent ordinals in Cantor Normal Form.
   For every ordinal a

       CNF(a) = w^b1*c1 + ... + w^bn*cn

   where:
       1. each bk is an ordinal;
       2. b1 > b2 > ... > bn >= 0;
       3. each ck is an integer;
       4. each ck > 0.
*)


exception OrdinalFailure of string


(* A type for ordinals. *)
type
    term = { exp: ordinal; coeff: int }
and
    ordinal = term list
;;


(* zero is an sum with no terms.  *)
let zero: ordinal = []

(* ordinal one just for convenience.  *)
let one: ordinal = [{exp = zero; coeff = 1}]

(* omega is a term with exponent 1 and coefficient one.  *)
let omega: ordinal = [{exp = one; coeff = 1}]

(* convert an integer to an ordinal.  *)
let int_to_ord x =
    if x > 0 then
        [{exp = zero; coeff = x}]
    else if x == 0 then
        zero
    else
        raise (OrdinalFailure
               (sprintf "Attempt to convert number %d to ordinal" x))
;;


let rec ord_to_str o =
    if o = zero then
        "0"
    else
        String.concat " + " (List.map term_to_str o)

and term_to_str t =
    match t with
    | {exp = []; coeff = n} -> (sprintf "%d" n)
    | {exp = [{exp = []; coeff = 1}]; coeff = 1} -> "ω"
    | {exp = [{exp = []; coeff = 1}]; coeff = n} -> sprintf "ω*%d" n
    | {exp = [{exp = []; coeff = n}]; coeff = 1} -> sprintf "ω^%d" n
    | {exp = [{exp = []; coeff = n}]; coeff = m} -> sprintf "ω^%d*%d" n m
    | {exp = a; coeff = 1} -> sprintf "ω^(%s)" (ord_to_str a)
    | {exp = a; coeff = n} -> sprintf "ω^(%s)*%d" (ord_to_str a) n
;;


(* function that tests whether the ordinal is a natural number < w  *)
let isnat o =
    match o with
    | [] -> true
    | [{ exp = []; coeff = _ }] -> true
    | _ -> false
;;

let ord_to_nat o =
    match o with
    | [] -> 0
    | [{exp = []; coeff = n}] -> n
    | _ -> raise (OrdinalFailure
                  (sprintf "attempt to convert %s to integer" (ord_to_str o)))
;;

(* compare two ordinals *)
let rec compare o1 o2 =
    (* printf "comparing (%s) and (%s)" (ord_to_str o1) (ord_to_str o2);*)
    if isnat o1 && isnat o2 then
        Pervasives.compare (ord_to_nat o1) (ord_to_nat o2)
    else if isnat o1 then
        -1  (* lt *)
    else if isnat o2 then
         1  (* gt *)
    else let expcomp = compare (List.hd o1).exp (List.hd o2).exp in
         if expcomp <> 0 then expcomp
         else let coeffcomp = Pervasives.compare (List.hd o1).coeff (List.hd o2).coeff in
         if coeffcomp <> 0 then coeffcomp
         else
             compare (List.tl o1) (List.tl o2)
;;

(* ordinal addition.  *)
let rec add  o1 o2 =
    if isnat o1 && isnat o2 then
        int_to_ord ((ord_to_nat o1) + (ord_to_nat o2))
    else
        let expcomp = compare (List.hd o1).exp (List.hd o2).exp in
        if expcomp = -1 (* lt *) then
            o2
        else if expcomp = 0 then
            {exp = (List.hd o1).exp; coeff = (List.hd o1).coeff + (List.hd o2).coeff}
            :: (List.tl o2)
        else
            {exp = (List.hd o1).exp; coeff = (List.hd o1).coeff }
            :: (add (List.tl o1) o2)
;;


(* ordinal multiplication.  *)
(* XXX this is not the most efficient multiplication algorithm, but it is simple.
   For a better implementation see PANAGIOTIS MANOLIOS and DARON VROON paper.  *)
let rec mult o1 o2 =
    if o1 = zero || o2 = zero then
        zero
    else if isnat o1 && isnat o2 then
        int_to_ord ((ord_to_nat o1) * (ord_to_nat o2))
    else if isnat o2 then
        { exp = (List.hd o1).exp; coeff = (List.hd o1).coeff * (ord_to_nat o2) }
        :: (List.tl o1)
    else
        { exp = add (List.hd o1).exp (List.hd o2).exp; coeff = (List.hd o2).coeff}
        :: mult o1 (List.tl o2)
;;

let rec sub o1 o2 =
    if compare o1 o2 = -1 then
        raise (OrdinalFailure
               (sprintf "attempt to evaluate (%s) - (%s)" (ord_to_str o1) (ord_to_str o2)))
    else if isnat o1 && isnat o2 then
        int_to_ord ((ord_to_nat o1) - (ord_to_nat o2))
    else if (compare (List.hd o1).exp (List.hd o2).exp) = 1 (* gt *) then
        o1
    (* exponent of o1 cannot be less than exponent of o2 because of the first case, so
       it can be only equal here.  *)
    else if (List.hd o1).coeff > (List.hd o2).coeff then
        { exp = (List.hd o1).exp; coeff = (List.hd o1).coeff - (List.hd o2).coeff }
        :: (List.tl o1)
    (* as previously, the coefficient of o1 cannot be less than the coefficient of o2,
       therefore they are equal.  *)
    else
        sub (List.tl o1) (List.tl o2)
;;


let test_ordinals () =
    printf "ord w = %s\n" (ord_to_str [{exp = [{exp = []; coeff = 1}]; coeff = 1}]);
    printf "ord w = %s\n" (ord_to_str omega);
    printf "ord w = %s\n" (ord_to_str [{exp = one; coeff = 1}]);
    printf "ord 44 = %s\n" (ord_to_str [{exp = zero; coeff = 44}]);
    printf "ord w^w = %s\n" (ord_to_str [{exp = omega; coeff = 1}]);
    printf "ord w^w + w*2 = %s\n" (ord_to_str [{exp = omega; coeff = 1};{exp = one; coeff = 2}]);
    printf "ord w^w + 33 = %s\n" (ord_to_str [{exp = omega; coeff = 1};{exp = zero; coeff = 33}]);
    printf "comparisons\n";
    printf "1 ? 3 = %d\n" (compare one (int_to_ord  3));
    printf "w ? 1 = %d\n" (compare omega (int_to_ord  1));
    printf "w +1 ? w = %d\n" (compare [{exp = one; coeff = 1}; {exp = []; coeff = 1}] omega);
    printf "w*2 + 1 ? w*2 = %d\n" (compare [{exp = one; coeff = 1}; {exp = []; coeff = 1}]
                                           [{exp = one; coeff = 2} ]);
    printf "w^w + 1 ? w = %d\n" (compare [{exp = omega; coeff = 1}; {exp = []; coeff = 1}]
                                         omega);
    printf "addition\n";
    printf "1 + 1 = %s\n" (ord_to_str (add one one));
    printf "w + 1 = %s\n" (ord_to_str (add omega one));
    printf "1 + w = %s\n" (ord_to_str (add one omega));
    printf "w + w = %s\n" (ord_to_str (add omega omega));
    printf "w + w + 1 = %s\n" (ord_to_str (add (add omega omega) one));
    printf "multiplication\n";
    printf "1 * 1 = %s\n" (ord_to_str (mult one one));
    printf "w * 1 = %s\n" (ord_to_str (mult omega one));
    printf "w * w = %s\n" (ord_to_str (mult omega omega));
    printf "(w+1) * 2 = %s\n" (ord_to_str (mult (add omega one) [{exp = []; coeff = 2}]));
    printf "(w*w+1) * 2 = %s\n" (ord_to_str (mult (add (mult omega omega) one) [{exp = []; coeff = 2}]));
    printf "subtraction\n";
    printf "1 - 1 = %s\n" (ord_to_str (sub one one));
    printf "w - 1 = %s\n" (ord_to_str (sub omega one));
    printf "w - w = %s\n" (ord_to_str (sub omega omega));
    printf "(w + w) - 1 = %s\n" (ord_to_str (sub (add omega omega) one));
    printf "(w + 1) - 1 = %s\n" (ord_to_str (sub (add omega one) one));

    ()
;;


