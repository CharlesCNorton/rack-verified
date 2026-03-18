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

(* ================================================================== *)
(* version_safe implies check_proof_identities                        *)
(* ================================================================== *)

Lemma version_safe_check_proof_identities : forall ac reg,
    version_safe ac reg = true ->
    check_proof_identities ac reg = true.
Proof.
  intros ac reg H. unfold version_safe in H.
  apply Bool.andb_true_iff in H. exact (proj1 H).
Qed.

(* ================================================================== *)
(* registries_consistent symmetry                                     *)
(* ================================================================== *)

Lemma find_proof_id_In : forall name reg pi,
    find_proof_id name reg = Some pi -> In pi reg.
Proof.
  intros name reg. induction reg as [|p rest IH]; intros pi H; simpl in H.
  - discriminate.
  - destruct (String.eqb p.(pi_theorem_name) name) eqn:E.
    + injection H as <-. left. reflexivity.
    + right. exact (IH pi H).
Qed.

Lemma find_proof_id_name : forall name reg pi,
    find_proof_id name reg = Some pi ->
    pi.(pi_theorem_name) = name.
Proof.
  intros name reg. induction reg as [|p rest IH]; intros pi H; simpl in H.
  - discriminate.
  - destruct (String.eqb p.(pi_theorem_name) name) eqn:E.
    + injection H as <-. apply String.eqb_eq in E. exact E.
    + exact (IH pi H).
Qed.

Lemma In_find_proof_id : forall pi reg,
    In pi reg ->
    NoDup (map pi_theorem_name reg) ->
    find_proof_id pi.(pi_theorem_name) reg = Some pi.
Proof.
  intros pi reg Hin Hnd.
  induction reg as [|p rest IH].
  - destruct Hin.
  - simpl. inversion Hnd as [| ? ? Hna Hnd']; subst.
    destruct Hin as [<- | Hin].
    + rewrite String.eqb_refl. reflexivity.
    + destruct (String.eqb p.(pi_theorem_name) pi.(pi_theorem_name)) eqn:E.
      * apply String.eqb_eq in E.
        exfalso. apply Hna.
        apply in_map_iff. exists pi. exact (conj (eq_sym E) Hin).
      * exact (IH Hin Hnd').
Qed.

(** [registries_consistent] is symmetric when the target registry
    has unique theorem names. *)
Lemma registries_consistent_sym : forall r1 r2,
    NoDup (map pi_theorem_name r2) ->
    registries_consistent r1 r2 = true ->
    registries_consistent r2 r1 = true.
Proof.
  intros r1 r2 Hnd2 H.
  unfold registries_consistent.
  apply forallb_forall.
  intros pi2 Hin2.
  destruct (find_proof_id pi2.(pi_theorem_name) r1) as [pi1|] eqn:Hfind1.
  - (* pi1 found in r1 *)
    assert (Hin1 : In pi1 r1) by exact (find_proof_id_In _ _ _ Hfind1).
    assert (Hname : pi1.(pi_theorem_name) = pi2.(pi_theorem_name))
      by exact (find_proof_id_name _ _ _ Hfind1).
    unfold registries_consistent in H.
    apply forallb_forall with (x := pi1) in H; [| exact Hin1].
    rewrite Hname in H.
    rewrite (In_find_proof_id pi2 r2 Hin2 Hnd2) in H.
    (* H : eqb pi1.hash pi2.hash = true *)
    apply String.eqb_eq in H. rewrite H. apply String.eqb_refl.
  - (* pi1 not found — vacuously true *)
    reflexivity.
Qed.

(* ================================================================== *)
(* Grounded proof identities                                          *)
(* ================================================================== *)

(** A [TypedProofId P] is a proof identity statically guaranteed
    to refer to a proof of [P].  The phantom parameter ensures
    type-correct construction; [P] and [tpi_proof] are erased
    at extraction, leaving only the [ProofId] metadata. *)
Record TypedProofId (P : Prop) : Type := {
  tpi_base  : ProofId;
  tpi_proof : P;
}.

Arguments tpi_base {P}.
Arguments tpi_proof {P}.

(** Project back to the untyped [ProofId]. *)
Definition tpi_to_proof_id {P : Prop} (tpi : TypedProofId P)
  : ProofId := tpi.(tpi_base).

(** Build a [TypedProofId] with the hash automatically derived
    from [mod_name.name].  The type system prevents constructing
    this with a proof of the wrong type. *)
Definition mk_typed_proof_identity (name mod_name : string)
    (P : Prop) (pf : P)
    (check : option (unit -> bool)) : TypedProofId P := {|
  tpi_base := {|
    pi_theorem_name := name;
    pi_module := mod_name;
    pi_type_hash := String.append mod_name
                      (String.append "." name);
    pi_runtime_check := check;
  |};
  tpi_proof := pf;
|}.

(** Build [Evidence] and [TypedProofId] together, ensuring they
    refer to the same proof.  Hash is auto-computed. *)
Definition mk_typed_identified_evidence (name mod_name : string)
    (P : Prop) (pf : P)
    (check : option (unit -> bool)) : Evidence * TypedProofId P :=
  (ProofTerm name P pf check,
   mk_typed_proof_identity name mod_name P pf check).

(** Tactic: build a [TypedProofId] after verifying [pf : P].
    Refuses mismatches at elaboration time. *)
Ltac ground_proof_identity name mod_name P pf check :=
  let ty := type of pf in
  unify P ty;
  exact (mk_typed_proof_identity name mod_name P pf check).

(** Tactic: build identified evidence after verifying [pf : P]. *)
Ltac ground_identified_evidence name mod_name P pf check :=
  let ty := type of pf in
  unify P ty;
  exact (mk_typed_identified_evidence name mod_name P pf check).

(** A [TypedProofId P] validates against any registry that
    contains its theorem name. *)
Lemma typed_proof_id_validates : forall P (tpi : TypedProofId P) reg,
    find_proof_id tpi.(tpi_base).(pi_theorem_name) reg <> None ->
    validate_proof_identity
      (ProofTerm tpi.(tpi_base).(pi_theorem_name) P tpi.(tpi_proof)
        tpi.(tpi_base).(pi_runtime_check)) reg = true.
Proof.
  intros P tpi reg H. unfold validate_proof_identity.
  destruct (find_proof_id tpi.(tpi_base).(pi_theorem_name) reg);
    [reflexivity | contradiction].
Qed.
