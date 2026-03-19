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
(* SHA-256 (pure OCaml, no external dependencies)                      *)
(* ------------------------------------------------------------------ *)

let sha256_k = [|
  0x428a2f98l; 0x71374491l; 0xb5c0fbcfl; 0xe9b5dba5l;
  0x3956c25bl; 0x59f111f1l; 0x923f82a4l; 0xab1c5ed5l;
  0xd807aa98l; 0x12835b01l; 0x243185bel; 0x550c7dc3l;
  0x72be5d74l; 0x80deb1fel; 0x9bdc06a7l; 0xc19bf174l;
  0xe49b69c1l; 0xefbe4786l; 0x0fc19dc6l; 0x240ca1ccl;
  0x2de92c6fl; 0x4a7484aal; 0x5cb0a9dcl; 0x76f988dal;
  0x983e5152l; 0xa831c66dl; 0xb00327c8l; 0xbf597fc7l;
  0xc6e00bf3l; 0xd5a79147l; 0x06ca6351l; 0x14292967l;
  0x27b70a85l; 0x2e1b2138l; 0x4d2c6dfcl; 0x53380d13l;
  0x650a7354l; 0x766a0abbl; 0x81c2c92el; 0x92722c85l;
  0xa2bfe8a1l; 0xa81a664bl; 0xc24b8b70l; 0xc76c51a3l;
  0xd192e819l; 0xd6990624l; 0xf40e3585l; 0x106aa070l;
  0x19a4c116l; 0x1e376c08l; 0x2748774cl; 0x34b0bcb5l;
  0x391c0cb3l; 0x4ed8aa4al; 0x5b9cca4fl; 0x682e6ff3l;
  0x748f82eel; 0x78a5636fl; 0x84c87814l; 0x8cc70208l;
  0x90befffal; 0xa4506cebl; 0xbef9a3f7l; 0xc67178f2l;
|]

let ( +: ) = Int32.add
let ( ^: ) = Int32.logxor
let ( &: ) = Int32.logand
let ( ~: ) = Int32.lognot
let shr n x = Int32.shift_right_logical x n
let rotr n x = Int32.logor (Int32.shift_right_logical x n) (Int32.shift_left x (32 - n))

let sha256_compress block h =
  let w = Array.make 64 0l in
  for i = 0 to 15 do
    let off = i * 4 in
    w.(i) <- Int32.logor (Int32.logor
      (Int32.shift_left (Int32.of_int (Char.code block.[off])) 24)
      (Int32.shift_left (Int32.of_int (Char.code block.[off+1])) 16))
      (Int32.logor
        (Int32.shift_left (Int32.of_int (Char.code block.[off+2])) 8)
        (Int32.of_int (Char.code block.[off+3])))
  done;
  for i = 16 to 63 do
    let s0 = (rotr 7 w.(i-15)) ^: (rotr 18 w.(i-15)) ^: (shr 3 w.(i-15)) in
    let s1 = (rotr 17 w.(i-2)) ^: (rotr 19 w.(i-2)) ^: (shr 10 w.(i-2)) in
    w.(i) <- w.(i-16) +: s0 +: w.(i-7) +: s1
  done;
  let a = ref h.(0) and b = ref h.(1) and c = ref h.(2) and d = ref h.(3)
  and e = ref h.(4) and f = ref h.(5) and g = ref h.(6) and hh = ref h.(7) in
  for i = 0 to 63 do
    let s1 = (rotr 6 !e) ^: (rotr 11 !e) ^: (rotr 25 !e) in
    let ch = (!e &: !f) ^: ((~: !e) &: !g) in
    let temp1 = !hh +: s1 +: ch +: sha256_k.(i) +: w.(i) in
    let s0 = (rotr 2 !a) ^: (rotr 13 !a) ^: (rotr 22 !a) in
    let maj = (!a &: !b) ^: (!a &: !c) ^: (!b &: !c) in
    let temp2 = s0 +: maj in
    hh := !g; g := !f; f := !e; e := !d +: temp1;
    d := !c; c := !b; b := !a; a := temp1 +: temp2
  done;
  h.(0) <- h.(0) +: !a; h.(1) <- h.(1) +: !b;
  h.(2) <- h.(2) +: !c; h.(3) <- h.(3) +: !d;
  h.(4) <- h.(4) +: !e; h.(5) <- h.(5) +: !f;
  h.(6) <- h.(6) +: !g; h.(7) <- h.(7) +: !hh

let sha256 msg =
  let len = String.length msg in
  let bit_len = len * 8 in
  (* pad: append 0x80, zeros, then 64-bit big-endian length *)
  let pad_len = (56 - (len + 1) mod 64 + 64) mod 64 in
  let padded = Bytes.create (len + 1 + pad_len + 8) in
  Bytes.blit_string msg 0 padded 0 len;
  Bytes.set padded len '\x80';
  for i = 0 to pad_len - 1 do Bytes.set padded (len + 1 + i) '\x00' done;
  let total = len + 1 + pad_len in
  for i = 0 to 7 do
    Bytes.set padded (total + i)
      (Char.chr ((bit_len lsr ((7 - i) * 8)) land 0xff))
  done;
  let h = [| 0x6a09e667l; 0xbb67ae85l; 0x3c6ef372l; 0xa54ff53al;
             0x510e527fl; 0x9b05688cl; 0x1f83d9abl; 0x5be0cd19l |] in
  let padded_s = Bytes.to_string padded in
  let n_blocks = String.length padded_s / 64 in
  for i = 0 to n_blocks - 1 do
    sha256_compress (String.sub padded_s (i * 64) 64) h
  done;
  let buf = Buffer.create 32 in
  Array.iter (fun w ->
    for i = 3 downto 0 do
      Buffer.add_char buf
        (Char.chr (Int32.to_int (Int32.logand (shr (i*8) w) 0xffl)))
    done) h;
  Buffer.contents buf

let hex_of_string s =
  let buf = Buffer.create (String.length s * 2) in
  String.iter (fun c -> Buffer.add_string buf (Printf.sprintf "%02x" (Char.code c))) s;
  Buffer.contents buf

let sha256_hex msg = hex_of_string (sha256 msg)

(* ------------------------------------------------------------------ *)
(* HMAC-SHA256                                                         *)
(* ------------------------------------------------------------------ *)

let hmac_sha256 ~key msg =
  let block_size = 64 in
  let key' =
    if String.length key > block_size then sha256 key
    else key
  in
  let key_padded = Bytes.make block_size '\x00' in
  Bytes.blit_string key' 0 key_padded 0 (String.length key');
  let o_key_pad = Bytes.create block_size in
  let i_key_pad = Bytes.create block_size in
  for i = 0 to block_size - 1 do
    Bytes.set o_key_pad i (Char.chr (Char.code (Bytes.get key_padded i) lxor 0x5c));
    Bytes.set i_key_pad i (Char.chr (Char.code (Bytes.get key_padded i) lxor 0x36))
  done;
  sha256 (Bytes.to_string o_key_pad ^ sha256 (Bytes.to_string i_key_pad ^ msg))

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
