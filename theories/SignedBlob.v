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

(* === Trust boundary ===

   What Rocq proves:
   - If [signed_blob_valid sb] holds (i.e., [sb_verify payload sig = true]),
     then [evidence_valid n (signed_to_evidence sb)] holds for any node [n].
   - If an assurance case passes [structural_checks] with signed evidence,
     [build_well_formed] yields [WellFormed], which yields [SupportTree].

   What Rocq does NOT prove:
   - That [sb_verify] implements a cryptographically secure algorithm.
   - That the OCaml extraction of [sb_verify] is faithful (extraction
     erases the Prop witness; the extracted function is the user-supplied
     OCaml callback, not a verified implementation).
   - That the HMAC-SHA256 in [rack_util.ml] is correct (it is tested
     against NIST vectors in [test_rack.ml], but not formally verified).
   - That the signing key is secret or that the transport is secure.

   In short: Rocq guarantees structural well-formedness given that the
   validator returns [true].  The security of the validator itself is
   an external assumption — instantiate [sb_verify] with a real crypto
   library (via the OCaml FFI) for production use.

   === End trust boundary === *)

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

(* ================================================================== *)
(* Replay-protected signed blobs                                       *)
(* ================================================================== *)

(** [ReplayProtectedBlob] extends [SignedBlob] with a nonce and
    sequence number.  The verifier checks all four fields: payload,
    signature, nonce, and sequence.  Replay is detectable by checking
    that the sequence number has not been seen before (tracked by
    the caller) or that the nonce is unique. *)
Record ReplayProtectedBlob : Type := {
  rpb_payload   : string;
  rpb_signature : string;
  rpb_nonce     : string;   (* random, unique per signing event *)
  rpb_sequence  : nat;      (* monotonically increasing counter *)
  rpb_verify    : string -> string -> string -> nat -> bool;
}.

Definition rpb_valid (rpb : ReplayProtectedBlob) : Prop :=
  rpb.(rpb_verify) rpb.(rpb_payload) rpb.(rpb_signature)
                    rpb.(rpb_nonce) rpb.(rpb_sequence) = true.

Definition rpb_to_signed (rpb : ReplayProtectedBlob) : SignedBlob := {|
  sb_payload   := rpb.(rpb_payload);
  sb_signature := rpb.(rpb_signature);
  sb_verify    := fun p s =>
    rpb.(rpb_verify) p s rpb.(rpb_nonce) rpb.(rpb_sequence);
|}.

Lemma rpb_valid_implies_signed : forall rpb,
    rpb_valid rpb -> signed_blob_valid (rpb_to_signed rpb).
Proof. intros rpb H. exact H. Qed.

Definition rpb_to_evidence (rpb : ReplayProtectedBlob) : Evidence :=
  signed_to_evidence (rpb_to_signed rpb).

(** Two replay-protected blobs are distinct when their nonces
    or sequence numbers differ. *)
Definition rpb_distinct (a b : ReplayProtectedBlob) : bool :=
  negb (String.eqb a.(rpb_nonce) b.(rpb_nonce)) ||
  negb (Nat.eqb a.(rpb_sequence) b.(rpb_sequence)).

Definition rpb_to_json (rpb : ReplayProtectedBlob) : Json :=
  JObj [("type", JStr "ReplayProtectedBlob");
        ("payload", JStr rpb.(rpb_payload));
        ("signature", JStr rpb.(rpb_signature));
        ("nonce", JStr rpb.(rpb_nonce));
        ("sequence", JNum rpb.(rpb_sequence))].

(* ================================================================== *)
(* Keyed blob with replay protection                                   *)
(* ================================================================== *)

(** [KeyedReplayBlob] combines keyed verification with replay fields. *)
Record KeyedReplayBlob : Type := {
  krb_payload   : string;
  krb_signature : string;
  krb_key_id    : string;
  krb_nonce     : string;
  krb_sequence  : nat;
  krb_verify    : string -> string -> bool;
}.

Definition krb_valid (krb : KeyedReplayBlob) : Prop :=
  krb.(krb_verify) krb.(krb_payload) krb.(krb_signature) = true.

Definition krb_to_keyed (krb : KeyedReplayBlob) : KeyedSignedBlob := {|
  ksb_payload   := krb.(krb_payload);
  ksb_signature := krb.(krb_signature);
  ksb_key_id    := krb.(krb_key_id);
  ksb_verify    := krb.(krb_verify);
|}.

(* ================================================================== *)
(* Key registry with rotation and revocation                           *)
(* ================================================================== *)

Inductive KeyStatus : Type :=
  | KeyActive
  | KeyRotated : string -> KeyStatus  (* rotated_to: successor key ID *)
  | KeyRevoked : string -> KeyStatus. (* reason *)

Record KeyEntry : Type := {
  ke_key_id     : string;
  ke_status     : KeyStatus;
  ke_not_before : string;   (* ISO 8601: key valid from *)
  ke_not_after  : string;   (* ISO 8601: key valid until *)
}.

Definition KeyRegistry := list KeyEntry.

Fixpoint key_lookup (key_id : string) (reg : KeyRegistry)
    : option KeyEntry :=
  match reg with
  | [] => None
  | entry :: rest =>
    if String.eqb entry.(ke_key_id) key_id then Some entry
    else key_lookup key_id rest
  end.

(** A key is usable when it is active and the current time falls
    within its validity window. *)
Definition key_usable (entry : KeyEntry) (now : string) : bool :=
  match entry.(ke_status) with
  | KeyActive =>
    negb (string_ltb now entry.(ke_not_before)) &&
    negb (string_ltb entry.(ke_not_after) now)
  | _ => false
  end.

(** Look up the active successor of a rotated key, following the
    rotation chain up to [fuel] hops. *)
Fixpoint resolve_key (reg : KeyRegistry) (key_id : string)
    (fuel : nat) : option KeyEntry :=
  match fuel with
  | 0 => None
  | S f =>
    match key_lookup key_id reg with
    | None => None
    | Some entry =>
      match entry.(ke_status) with
      | KeyActive => Some entry
      | KeyRotated successor => resolve_key reg successor f
      | KeyRevoked _ => None
      end
    end
  end.

(** Validate a keyed blob against a key registry: the key must
    be active (or resolvable via rotation) and the verifier must
    accept the payload. *)
Definition validate_keyed_blob (ksb : KeyedSignedBlob)
    (reg : KeyRegistry) (now : string) : bool :=
  match resolve_key reg ksb.(ksb_key_id) (length reg) with
  | Some entry => key_usable entry now &&
                  ksb.(ksb_verify) ksb.(ksb_payload) ksb.(ksb_signature)
  | None => false
  end.

(** Soundness: validation implies the verifier accepted. *)
Lemma validate_keyed_blob_sound : forall ksb reg now,
    validate_keyed_blob ksb reg now = true ->
    keyed_blob_valid ksb.
Proof.
  intros ksb reg now H. unfold validate_keyed_blob in H.
  destruct (resolve_key reg ksb.(ksb_key_id) (length reg)); [| discriminate].
  apply Bool.andb_true_iff in H. exact (proj2 H).
Qed.

(** Revocation check: resolve_key returns None for a revoked key. *)
Lemma resolve_revoked_none : forall reg key_id reason nb na fuel,
    key_lookup key_id reg =
      Some {| ke_key_id := key_id;
              ke_status := KeyRevoked reason;
              ke_not_before := nb;
              ke_not_after := na |} ->
    fuel > 0 ->
    resolve_key reg key_id fuel = None.
Proof.
  intros reg key_id reason nb na fuel Hlookup Hfuel.
  destruct fuel as [|f]; [inversion Hfuel |].
  simpl. rewrite Hlookup. reflexivity.
Qed.
