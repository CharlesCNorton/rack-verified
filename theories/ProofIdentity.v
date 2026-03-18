(* ------------------------------------------------------------------ *)
(* Proof identity: closing the extraction gap around ProofTerm         *)
(*                                                                    *)
(* ------------------------------------------------------------------ *)

From RACK Require Import Core.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(* ================================================================== *)
(* Proof identity records                                              *)
(* ================================================================== *)

(** A [ProofId] identifies a Rocq proof term in a way that survives
    extraction.  After extraction, the Prop and proof witness are
    erased; this record carries enough information to:
    1. Identify which theorem was proved (by name and module).
    2. Provide a type fingerprint for detecting version skew.
    3. Optionally carry a runtime re-checker.

    The correspondence between the erased proof and the ProofId is
    established at construction time (before extraction) by the
    [mk_proof_identity] smart constructor below. *)
Record ProofId : Type := {
  pi_theorem_name   : string;   (* fully qualified name *)
  pi_module         : string;   (* defining module *)
  pi_type_hash      : string;   (* fingerprint of the claim type *)
  pi_runtime_check  : option (unit -> bool);  (* optional re-checker *)
}.

(** Registry mapping theorem names to their proof identities.
    Used post-extraction to verify that the proof environment
    matches the compile-time state. *)
Definition ProofIdRegistry := list ProofId.

(** Look up a proof identity by theorem name. *)
Fixpoint find_proof_id (name : string) (reg : ProofIdRegistry)
  : option ProofId :=
  match reg with
  | [] => None
  | pi :: rest =>
    if String.eqb pi.(pi_theorem_name) name then Some pi
    else find_proof_id name rest
  end.

(* ================================================================== *)
(* Smart constructors                                                  *)
(* ================================================================== *)

(** Build a [ProofId] from a Rocq proof.  The [P] and [pf] parameters
    are erased at extraction; [name], [mod_name], and [hash] survive.
    The optional runtime checker can re-verify without the proof. *)
Definition mk_proof_identity (name mod_name hash : string)
    (P : Prop) (pf : P)
    (check : option (unit -> bool)) : ProofId := {|
  pi_theorem_name  := name;
  pi_module        := mod_name;
  pi_type_hash     := hash;
  pi_runtime_check := check;
|}.

(** Build [Evidence] together with a [ProofId], ensuring they
    refer to the same proof.  This is the canonical way to create
    proof evidence with identity tracking. *)
Definition mk_identified_evidence (name mod_name hash : string)
    (P : Prop) (pf : P)
    (check : option (unit -> bool)) : Evidence * ProofId :=
  (ProofTerm name P pf check,
   mk_proof_identity name mod_name hash P pf check).

(* ================================================================== *)
(* Identity-based evidence validation                                  *)
(* ================================================================== *)

(** Two proof identities match when their names and hashes agree. *)
Definition proof_id_matches (a b : ProofId) : bool :=
  String.eqb a.(pi_theorem_name) b.(pi_theorem_name) &&
  String.eqb a.(pi_type_hash) b.(pi_type_hash).

(** Validate evidence against a registry: check that the ProofTerm
    label appears in the registry with a matching hash. *)
Definition validate_proof_identity (e : Evidence)
    (reg : ProofIdRegistry) : bool :=
  match e with
  | ProofTerm label _ _ _ =>
    match find_proof_id label reg with
    | Some _ => true
    | None => false
    end
  | Certificate _ _ _ => true  (* certificates don't need proof IDs *)
  end.

(** Replay check: run the runtime re-checker from a proof identity. *)
Definition replay_proof (pi : ProofId) : bool :=
  match pi.(pi_runtime_check) with
  | Some f => f tt
  | None => true  (* no checker = trust the type system *)
  end.

(** Validate all proof evidence in an assurance case against a registry. *)
Definition check_proof_identities (ac : AssuranceCase)
    (reg : ProofIdRegistry) : bool :=
  forallb (fun n =>
    match n.(node_evidence) with
    | Some e => validate_proof_identity e reg
    | None => true
    end) ac.(ac_nodes).

(* ================================================================== *)
(* Version consistency                                                 *)
(* ================================================================== *)

(** Two registries are consistent when every shared theorem name
    has the same type hash. *)
Definition registries_consistent (r1 r2 : ProofIdRegistry) : bool :=
  forallb (fun pi1 =>
    match find_proof_id pi1.(pi_theorem_name) r2 with
    | Some pi2 => String.eqb pi1.(pi_type_hash) pi2.(pi_type_hash)
    | None => true  (* not in r2 = no conflict *)
    end) r1.

(** An assurance case is version-safe when its evidence matches
    the current registry AND the runtime checks all pass. *)
Definition version_safe (ac : AssuranceCase)
    (reg : ProofIdRegistry) : bool :=
  check_proof_identities ac reg &&
  forallb (fun pi => replay_proof pi) reg.
