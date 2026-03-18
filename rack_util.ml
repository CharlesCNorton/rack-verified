(* rack_util.ml — shared helpers for extracted RACK OCaml code.
   Provides Coq<->OCaml string and list conversions used by
   rack_cli.ml, test_rack.ml, and test_rack_prop.ml.
*)

open Rack

let coq_bool_to_bool = function True -> true | False -> false

let string_of_coq s =
  let buf = Buffer.create 64 in
  let rec go = function
    | EmptyString -> ()
    | String (Ascii (b0,b1,b2,b3,b4,b5,b6,b7), rest) ->
      let b x = if coq_bool_to_bool x then 1 else 0 in
      let n =
        (b b0) lor (b b1 lsl 1) lor (b b2 lsl 2) lor (b b3 lsl 3) lor
        (b b4 lsl 4) lor (b b5 lsl 5) lor (b b6 lsl 6) lor (b b7 lsl 7)
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
      let bit n = if c land (1 lsl n) <> 0 then Rack.True else Rack.False in
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

(* ------------------------------------------------------------------ *)
(* FNV-1a hash-based evidence validator                                *)
(* ------------------------------------------------------------------ *)

(* FNV-1a 32-bit hash (non-cryptographic; demonstrates the pattern.
   In production, replace with HMAC-SHA256 via an external library.) *)
let fnv1a s =
  let h = ref 0x811c9dc5 in
  String.iter (fun c ->
    h := !h lxor (Char.code c);
    h := !h * 0x01000193;
    h := !h land 0x3FFFFFFF
  ) s;
  Printf.sprintf "%08x" !h

(* Build a Certificate validator keyed by a shared secret.
   The blob format is "payload:fnv1a(secret+payload)".
   Returns a (coq_string -> bool) suitable for the Certificate constructor. *)
let make_keyed_validator secret =
  fun coq_blob ->
    let blob = string_of_coq coq_blob in
    let ok = match String.rindex_opt blob ':' with
    | None -> false
    | Some i ->
      let payload = String.sub blob 0 i in
      let sig_ = String.sub blob (i + 1) (String.length blob - i - 1) in
      let expected = fnv1a (secret ^ payload) in
      sig_ = expected
    in
    if ok then Rack.True else Rack.False

(* Create a signed blob: "payload:fnv1a(secret+payload)" *)
let sign_blob secret payload =
  let sig_ = fnv1a (secret ^ payload) in
  payload ^ ":" ^ sig_
