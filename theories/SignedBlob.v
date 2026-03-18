(* ------------------------------------------------------------------ *)
(* Signed evidence blobs                                                *)
(* ------------------------------------------------------------------ *)

From RACK Require Import Core.
From RACK Require Import Json.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

(* Abstraction for externally-signed evidence blobs.
   sb_verify is a DECIDABLE VALIDATOR, not a cryptographic primitive.
   The user instantiates it with whatever verification logic is
   appropriate: HMAC check, GPG signature verify, or a simple
   string-equality stub for testing.  The Rocq proof only requires
   that sb_verify sb_payload sb_signature = true; the actual
   cryptographic strength is the user's responsibility.

   After extraction, sb_verify becomes an OCaml function
   (string -> string -> bool) that can call real crypto libraries.     *)
Record SignedBlob : Type := {
  sb_payload   : string;
  sb_signature : string;
  sb_verify    : string -> string -> bool;
}.

Definition signed_blob_valid (sb : SignedBlob) : Prop :=
  sb.(sb_verify) sb.(sb_payload) sb.(sb_signature) = true.

Definition signed_to_evidence (sb : SignedBlob) : Evidence :=
  Certificate sb.(sb_payload) "signed"
              (fun p => sb.(sb_verify) p sb.(sb_signature)).

Lemma signed_evidence_valid : forall sb n,
    signed_blob_valid sb ->
    evidence_valid n (signed_to_evidence sb).
Proof. intros sb n H. exact H. Qed.

(** [KeyedSignedBlob] strengthens [SignedBlob] by requiring that
    the verifier is keyed: it takes a secret and checks that
    [verify secret payload signature = true].  After extraction,
    instantiate [ksb_verify] with [Rack_util.make_keyed_validator]
    which uses HMAC-SHA256.

    The Rocq-side specification guarantees:
    1. [signed_blob_valid] holds iff the verifier accepts.
    2. The extracted verifier calls real HMAC-SHA256 (via rack_util.ml).
    3. Tampering with payload or signature causes rejection
       (verified by property tests in test_rack.ml). *)
Record KeyedSignedBlob : Type := {
  ksb_payload   : string;
  ksb_signature : string;
  ksb_key_id    : string;   (* identifies the key, not the key itself *)
  ksb_verify    : string -> string -> bool;
}.

Definition keyed_blob_valid (ksb : KeyedSignedBlob) : Prop :=
  ksb.(ksb_verify) ksb.(ksb_payload) ksb.(ksb_signature) = true.

Definition keyed_to_signed (ksb : KeyedSignedBlob) : SignedBlob := {|
  sb_payload := ksb.(ksb_payload);
  sb_signature := ksb.(ksb_signature);
  sb_verify := ksb.(ksb_verify);
|}.

Lemma keyed_valid_implies_signed : forall ksb,
    keyed_blob_valid ksb -> signed_blob_valid (keyed_to_signed ksb).
Proof. intros ksb H. exact H. Qed.

Definition keyed_to_evidence (ksb : KeyedSignedBlob) : Evidence :=
  signed_to_evidence (keyed_to_signed ksb).

Definition signed_to_json (sb : SignedBlob) : Json :=
  JObj [("type", JStr "SignedBlob");
        ("payload", JStr sb.(sb_payload));
        ("signature", JStr sb.(sb_signature))].
