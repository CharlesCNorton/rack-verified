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
(* SHA-256 and HMAC-SHA256 via digestif (audited pure-OCaml library)   *)
(* ------------------------------------------------------------------ *)

let sha256 msg = Digestif.SHA256.(digest_string msg |> to_raw_string)

let hex_of_string s =
  let buf = Buffer.create (String.length s * 2) in
  String.iter (fun c -> Buffer.add_string buf (Printf.sprintf "%02x" (Char.code c))) s;
  Buffer.contents buf

let sha256_hex msg = hex_of_string (sha256 msg)

let hmac_sha256 ~key msg =
  Digestif.SHA256.(hmac_string ~key msg |> to_raw_string)

let hmac_sha256_hex ~key msg = hex_of_string (hmac_sha256 ~key msg)

(* ------------------------------------------------------------------ *)
(* HMAC-SHA256-based evidence validator                                *)
(* ------------------------------------------------------------------ *)

(* Build a Certificate validator keyed by a shared secret.
   The blob format is "payload:hmac_sha256_hex(secret, payload)".
   Returns a (coq_string -> bool) suitable for the Certificate constructor. *)
let make_keyed_validator secret =
  fun coq_blob ->
    let blob = string_of_coq coq_blob in
    let ok = match String.rindex_opt blob ':' with
    | None -> false
    | Some i ->
      let payload = String.sub blob 0 i in
      let sig_ = String.sub blob (i + 1) (String.length blob - i - 1) in
      let expected = hmac_sha256_hex ~key:secret payload in
      sig_ = expected
    in
    if ok then Rack.True else Rack.False

(* Create a signed blob: "payload:hmac_sha256_hex(secret, payload)" *)
let sign_blob secret payload =
  let sig_ = hmac_sha256_hex ~key:secret payload in
  payload ^ ":" ^ sig_
