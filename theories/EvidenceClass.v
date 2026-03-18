(* ------------------------------------------------------------------ *)
(* Evidence classification, trust envelopes, and freshness             *)
(*                                                                    *)
(* ------------------------------------------------------------------ *)

From RACK Require Import Core.
From RACK Require Import Reflect.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(* ================================================================== *)
(* Evidence classes                                                    *)
(* ================================================================== *)

(** Semantic classification of evidence.  The core [Evidence] type
    has two constructors (ProofTerm, Certificate); this layer adds
    fine-grained classification without breaking existing proofs. *)
Inductive EvidenceClass : Type :=
  | ECTheorem       (* Rocq proof term *)
  | ECModelCheck    (* bounded model checker: CBMC, TLC, Alloy *)
  | ECTest          (* test suite or fuzzer: AFL++, QuickChick *)
  | ECSymbolic      (* symbolic analysis: SAW, Kani, Verus *)
  | ECCertificate.  (* signed external certificate *)

Definition EvidenceClass_eqb (a b : EvidenceClass) : bool :=
  match a, b with
  | ECTheorem, ECTheorem
  | ECModelCheck, ECModelCheck
  | ECTest, ECTest
  | ECSymbolic, ECSymbolic
  | ECCertificate, ECCertificate => true
  | _, _ => false
  end.

Lemma EvidenceClass_eqb_eq : forall a b,
    EvidenceClass_eqb a b = true <-> a = b.
Proof.
  destruct a, b; simpl; split; intro; try reflexivity; try discriminate.
Qed.

(** Classify existing [Evidence] values.  ProofTerm is always
    [ECTheorem].  Certificate classification uses the tool_id field:
    known tools map to their class; unknown tools default to
    [ECCertificate]. *)
Definition classify_by_tool (tool : string) : EvidenceClass :=
  if String.eqb tool "CBMC" then ECModelCheck
  else if String.eqb tool "TLC" then ECModelCheck
  else if String.eqb tool "Alloy" then ECModelCheck
  else if String.eqb tool "AFL++" then ECTest
  else if String.eqb tool "QuickChick" then ECTest
  else if String.eqb tool "fuzz-tool" then ECTest
  else if String.eqb tool "GHA" then ECTest
  else if String.eqb tool "SAW" then ECSymbolic
  else if String.eqb tool "Kani" then ECSymbolic
  else if String.eqb tool "Verus" then ECSymbolic
  else ECCertificate.

Definition classify_evidence (e : Evidence) : EvidenceClass :=
  match e with
  | ProofTerm _ _ _ _ => ECTheorem
  | Certificate _ tool _ => classify_by_tool tool
  end.

(* ================================================================== *)
(* Trust envelopes                                                     *)
(* ================================================================== *)

(** A [TrustEnvelope] captures the provenance and validity conditions
    of a piece of evidence.  After extraction, these fields survive
    as inspectable metadata for audit and freshness checking. *)
Record TrustEnvelope : Type := {
  te_tool           : string;        (* originating tool identifier *)
  te_version        : string;        (* tool version *)
  te_assumptions    : list string;   (* explicit assumptions *)
  te_valid_from     : string;        (* ISO 8601 start *)
  te_valid_until    : string;        (* ISO 8601 expiry *)
  te_replay_command : option string; (* command to re-run validation *)
  te_env_deps       : list string;   (* environmental dependencies *)
}.

Definition default_trust_envelope : TrustEnvelope := {|
  te_tool           := "";
  te_version        := "";
  te_assumptions    := [];
  te_valid_from     := "";
  te_valid_until    := "";
  te_replay_command := None;
  te_env_deps       := [];
|}.

(** Build a trust envelope from node metadata (best-effort). *)
Definition trust_envelope_of_metadata
    (md : list (string * MetadataValue)) : TrustEnvelope := {|
  te_tool := match find_metadata "tool" md with
             | Some v => mv_as_string v | None => "" end;
  te_version := match find_metadata "version" md with
                | Some v => mv_as_string v | None => "" end;
  te_assumptions := [];
  te_valid_from := match find_metadata "timestamp" md with
                   | Some v => mv_as_string v | None => "" end;
  te_valid_until := match find_metadata "valid_until" md with
                    | Some v => mv_as_string v | None => "" end;
  te_replay_command := match find_metadata "replay" md with
                       | Some v => Some (mv_as_string v) | None => None end;
  te_env_deps := [];
|}.

(** Extract trust envelope from a node. *)
Definition node_trust_envelope (n : Node) : TrustEnvelope :=
  trust_envelope_of_metadata n.(node_metadata).

(* ================================================================== *)
(* Freshness                                                           *)
(* ================================================================== *)

(** Evidence is fresh when the current date falls within the
    validity interval.  Uses lexicographic string comparison
    on ISO 8601 date strings. *)
Definition evidence_fresh (te : TrustEnvelope) (now : string) : bool :=
  let from_ok := match te.(te_valid_from) with
                 | EmptyString => true
                 | s => negb (string_ltb now s)
                 end in
  let until_ok := match te.(te_valid_until) with
                  | EmptyString => true
                  | s => negb (string_ltb s now)
                  end in
  from_ok && until_ok.

(** Evidence is expired when [valid_until] < [now]. *)
Definition evidence_expired (te : TrustEnvelope) (now : string) : bool :=
  match te.(te_valid_until) with
  | EmptyString => false
  | s => string_ltb s now
  end.

(** Node-level freshness check. *)
Definition node_evidence_fresh (n : Node) (now : string) : bool :=
  evidence_fresh (node_trust_envelope n) now.

(* ================================================================== *)
(* Extended well-formedness with freshness                             *)
(* ================================================================== *)

(** [WellFormedFresh] extends [WellFormed] with evidence freshness:
    every Solution node's evidence must be fresh as of [now]. *)
Record WellFormedFresh (ac : AssuranceCase) (now : string) : Prop := {
  wff_wf    : WellFormed ac;
  wff_fresh : forall n,
    In n ac.(ac_nodes) ->
    n.(node_kind) = Solution ->
    node_evidence_fresh n now = true;
}.

(** Boolean checker for freshness. *)
Definition check_all_fresh (ac : AssuranceCase) (now : string) : bool :=
  forallb (fun n =>
    match n.(node_kind) with
    | Solution => node_evidence_fresh n now
    | _ => true
    end) ac.(ac_nodes).

(** Combined structural + freshness check. *)
Definition check_well_formed_fresh (ac : AssuranceCase)
    (now : string) : bool :=
  structural_checks ac && check_all_fresh ac now.

(** Soundness: boolean freshness check implies the freshness property. *)
Lemma check_all_fresh_correct : forall ac now,
    check_all_fresh ac now = true ->
    forall n, In n ac.(ac_nodes) ->
    n.(node_kind) = Solution ->
    node_evidence_fresh n now = true.
Proof.
  intros ac now H n Hin Hk.
  unfold check_all_fresh in H.
  apply forallb_forall with (x := n) in H; [| exact Hin].
  rewrite Hk in H. exact H.
Qed.

(* ================================================================== *)
(* Evidence class-specific well-formedness                             *)
(* ================================================================== *)

(** Class-specific trust requirements.
    - Theorem evidence: no expiry (mathematical truth is eternal)
    - Model-check evidence: must have bounded scope in assumptions
    - Test evidence: must have replay command
    - Symbolic evidence: must have tool version
    - Certificate: must have valid_until *)
Definition class_trust_ok (ec : EvidenceClass)
    (te : TrustEnvelope) : bool :=
  match ec with
  | ECTheorem => true  (* proofs don't expire *)
  | ECModelCheck =>
    negb (match te.(te_assumptions) with [] => true | _ => false end)
  | ECTest =>
    match te.(te_replay_command) with Some _ => true | None => false end
  | ECSymbolic =>
    negb (String.eqb te.(te_version) "")
  | ECCertificate =>
    negb (String.eqb te.(te_valid_until) "")
  end.

(** Check class-specific trust for all evidence-bearing nodes. *)
Definition check_class_trust (ac : AssuranceCase) : bool :=
  forallb (fun n =>
    match n.(node_kind), n.(node_evidence) with
    | Solution, Some e =>
      class_trust_ok (classify_evidence e) (node_trust_envelope n)
    | _, _ => true
    end) ac.(ac_nodes).

(* ================================================================== *)
(* Admissibility: combining structural + freshness + class trust       *)
(* ================================================================== *)

Definition Admissible (ac : AssuranceCase) (now : string) : Prop :=
  WellFormed ac /\
  (forall n, In n ac.(ac_nodes) ->
    n.(node_kind) = Solution ->
    node_evidence_fresh n now = true) /\
  check_class_trust ac = true.

Definition check_admissible (ac : AssuranceCase) (now : string) : bool :=
  structural_checks ac &&
  check_all_fresh ac now &&
  check_class_trust ac.

(* ================================================================== *)
(* check_well_formed_fresh soundness                                  *)
(* ================================================================== *)

(** Build a [WellFormedFresh] from boolean checks plus the two
    obligations that cannot be decided: entailment and evidence
    validity (same preconditions as [build_well_formed]). *)
Lemma build_well_formed_fresh : forall ac now,
    check_well_formed_fresh ac now = true ->
    (forall id n,
      find_node ac id = Some n ->
      (n.(node_kind) = Goal \/ n.(node_kind) = Strategy) ->
      (let kids := supportedby_children ac id in
       let child_claims :=
         flat_map (fun kid =>
           match find_node ac kid with
           | Some cn => [cn.(node_claim)]
           | None     => []
           end) kids
       in fold_right and True child_claims -> n.(node_claim))) ->
    (forall n e,
      In n ac.(ac_nodes) ->
      n.(node_kind) = Solution ->
      n.(node_evidence) = Some e ->
      evidence_valid n e) ->
    WellFormedFresh ac now.
Proof.
  intros ac now Hcheck Hent Hev.
  unfold check_well_formed_fresh in Hcheck.
  apply Bool.andb_true_iff in Hcheck. destruct Hcheck as [Hstruct Hfresh].
  constructor.
  - exact (build_well_formed ac Hstruct Hent Hev).
  - exact (check_all_fresh_correct ac now Hfresh).
Qed.

(* ================================================================== *)
(* check_admissible soundness                                         *)
(* ================================================================== *)

(** Build an [Admissible] witness from boolean checks. *)
Lemma check_admissible_sound : forall ac now,
    check_admissible ac now = true ->
    (forall id n,
      find_node ac id = Some n ->
      (n.(node_kind) = Goal \/ n.(node_kind) = Strategy) ->
      (let kids := supportedby_children ac id in
       let child_claims :=
         flat_map (fun kid =>
           match find_node ac kid with
           | Some cn => [cn.(node_claim)]
           | None     => []
           end) kids
       in fold_right and True child_claims -> n.(node_claim))) ->
    (forall n e,
      In n ac.(ac_nodes) ->
      n.(node_kind) = Solution ->
      n.(node_evidence) = Some e ->
      evidence_valid n e) ->
    Admissible ac now.
Proof.
  intros ac now Hcheck Hent Hev.
  unfold check_admissible in Hcheck.
  apply Bool.andb_true_iff in Hcheck. destruct Hcheck as [Hcheck Hclass].
  apply Bool.andb_true_iff in Hcheck. destruct Hcheck as [Hstruct Hfresh].
  split; [| split].
  - exact (build_well_formed ac Hstruct Hent Hev).
  - exact (check_all_fresh_correct ac now Hfresh).
  - exact Hclass.
Qed.
