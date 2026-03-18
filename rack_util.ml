(* rack_util.ml — shared helpers for extracted RACK OCaml code.
   Provides Coq<->OCaml string and list conversions used by
   rack_cli.ml, test_rack.ml, and test_rack_prop.ml.
*)

open Rack

let string_of_coq s =
  let buf = Buffer.create 64 in
  let rec go = function
    | EmptyString -> ()
    | String (Ascii (b0,b1,b2,b3,b4,b5,b6,b7), rest) ->
      let n =
        (if b0 then 1 else 0) lor
        (if b1 then 2 else 0) lor
        (if b2 then 4 else 0) lor
        (if b3 then 8 else 0) lor
        (if b4 then 16 else 0) lor
        (if b5 then 32 else 0) lor
        (if b6 then 64 else 0) lor
        (if b7 then 128 else 0)
      in
      Buffer.add_char buf (Char.chr n);
      go rest
  in
  go s;
  Buffer.contents buf

let coq_of_string s =
  let len = String.length s in
  let rec go i =
    if i >= len then EmptyString
    else
      let c = Char.code s.[i] in
      let bit n = if c land (1 lsl n) <> 0 then True else False in
      String (Ascii (bit 0, bit 1, bit 2, bit 3,
                     bit 4, bit 5, bit 6, bit 7),
              go (i + 1))
  in
  go 0

let rec list_of_coq = function
  | Nil -> []
  | Cons (x, rest) -> x :: list_of_coq rest

let rec coq_list_of = function
  | [] -> Nil
  | x :: xs -> Cons (x, coq_list_of xs)
