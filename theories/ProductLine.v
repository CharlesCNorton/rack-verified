(* ------------------------------------------------------------------ *)
(* Product-line reasoning                                              *)
(*                                                                    *)
(* ------------------------------------------------------------------ *)

From RACK Require Import Core.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(* ================================================================== *)
(* Feature models                                                      *)
(* ================================================================== *)

(** A feature is an atomic capability or configuration option. *)
Definition Feature := string.

(** A feature expression determines when a node/link is present. *)
Inductive FeatureExpr : Type :=
  | FEAtom   : Feature -> FeatureExpr
  | FETrue   : FeatureExpr
  | FEFalse  : FeatureExpr
  | FEAnd    : FeatureExpr -> FeatureExpr -> FeatureExpr
  | FEOr     : FeatureExpr -> FeatureExpr -> FeatureExpr
  | FENot    : FeatureExpr -> FeatureExpr.

(** A variant configuration is a set of enabled features. *)
Definition Variant := list Feature.

(** Evaluate a feature expression against a variant. *)
Fixpoint eval_feature (v : Variant) (fe : FeatureExpr) : bool :=
  match fe with
  | FEAtom f => mem_string f v
  | FETrue => true
  | FEFalse => false
  | FEAnd a b => eval_feature v a && eval_feature v b
  | FEOr a b => eval_feature v a || eval_feature v b
  | FENot a => negb (eval_feature v a)
  end.

(** A feature model constrains valid variants. *)
Record FeatureModel : Type := {
  fm_features    : list Feature;   (* all known features *)
  fm_mandatory   : list Feature;   (* must be in every variant *)
  fm_constraints : list FeatureExpr; (* all must hold *)
}.

(** A variant is valid under a feature model. *)
Definition valid_variant (fm : FeatureModel) (v : Variant) : bool :=
  forallb (fun f => mem_string f v) fm.(fm_mandatory) &&
  forallb (eval_feature v) fm.(fm_constraints) &&
  forallb (fun f => mem_string f fm.(fm_features)) v.

(* ================================================================== *)
(* Annotated assurance case                                            *)
(* ================================================================== *)

(** An annotated node carries a feature expression that determines
    when it's included in a variant. *)
Record AnnotatedNode : Type := {
  an_node    : Node;
  an_feature : FeatureExpr;
}.

Record AnnotatedLink : Type := {
  al_link    : Link;
  al_feature : FeatureExpr;
}.

Record ProductLineCase : Type := {
  plc_nodes   : list AnnotatedNode;
  plc_links   : list AnnotatedLink;
  plc_top     : Id;
  plc_fm      : FeatureModel;
}.

(* ================================================================== *)
(* Variant projection                                                  *)
(* ================================================================== *)

(** Project a product-line case to a specific variant by filtering
    out nodes and links whose feature expressions are false. *)
Definition project_variant (plc : ProductLineCase)
    (v : Variant) : AssuranceCase := {|
  ac_nodes := map an_node
    (filter (fun an => eval_feature v an.(an_feature)) plc.(plc_nodes));
  ac_links := map al_link
    (filter (fun al => eval_feature v al.(al_feature)) plc.(plc_links));
  ac_top := plc.(plc_top);
|}.

(* ================================================================== *)
(* Family-wide and variant-specific properties                         *)
(* ================================================================== *)

(** A property is family-wide when it holds for every valid variant. *)
Definition family_wide (plc : ProductLineCase)
    (P : AssuranceCase -> Prop) : Prop :=
  forall v, valid_variant plc.(plc_fm) v = true ->
    P (project_variant plc v).

(** A property is variant-specific when it holds for a particular
    variant but not necessarily all. *)
Definition variant_specific (plc : ProductLineCase)
    (v : Variant) (P : AssuranceCase -> Prop) : Prop :=
  valid_variant plc.(plc_fm) v = true /\
  P (project_variant plc v).

(** Boolean check: is a projected variant well-formed? *)
Definition check_variant_wf (plc : ProductLineCase)
    (v : Variant) : bool :=
  structural_checks (project_variant plc v).

(** A node is family-wide (present in all valid variants). *)
Definition node_family_wide (plc : ProductLineCase)
    (id : Id) : bool :=
  match find (fun an =>
    String.eqb an.(an_node).(node_id) id) plc.(plc_nodes) with
  | Some an =>
    match an.(an_feature) with
    | FETrue => true
    | _ => false
    end
  | None => false
  end.

(* ================================================================== *)
(* Compositional reuse                                                 *)
(* ================================================================== *)

(** Reuse: if a node's feature expression is [FETrue], it appears
    in every variant.  Its evidence is reusable across the family. *)
Definition reusable_nodes (plc : ProductLineCase) : list Id :=
  map (fun an => an.(an_node).(node_id))
    (filter (fun an =>
      match an.(an_feature) with FETrue => true | _ => false end)
    plc.(plc_nodes)).

(** Lift a single-variant assurance case to a product-line case
    where all nodes and links are family-wide ([FETrue]). *)
Definition lift_to_product_line (ac : AssuranceCase)
    (fm : FeatureModel) : ProductLineCase := {|
  plc_nodes := map (fun n => {|
    an_node := n; an_feature := FETrue |}) ac.(ac_nodes);
  plc_links := map (fun l => {|
    al_link := l; al_feature := FETrue |}) ac.(ac_links);
  plc_top := ac.(ac_top);
  plc_fm := fm;
|}.

(** Projecting a lifted case with any valid variant recovers
    the original case. *)
Lemma filter_true_map_node : forall v (ns : list Node),
    filter (fun an => eval_feature v an.(an_feature))
      (map (fun n => {| an_node := n; an_feature := FETrue |}) ns) =
    map (fun n => {| an_node := n; an_feature := FETrue |}) ns.
Proof.
  intros v. induction ns as [|n ns' IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma filter_true_map_link : forall v (ls : list Link),
    filter (fun al => eval_feature v al.(al_feature))
      (map (fun l => {| al_link := l; al_feature := FETrue |}) ls) =
    map (fun l => {| al_link := l; al_feature := FETrue |}) ls.
Proof.
  intros v. induction ls as [|l ls' IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma map_an_node_id : forall (ns : list Node),
    map an_node
      (map (fun n => {| an_node := n; an_feature := FETrue |}) ns) = ns.
Proof.
  induction ns as [|n ns' IH]; simpl.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Lemma map_al_link_id : forall (ls : list Link),
    map al_link
      (map (fun l => {| al_link := l; al_feature := FETrue |}) ls) = ls.
Proof.
  induction ls as [|l ls' IH]; simpl.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Theorem project_lifted : forall ac fm v,
    valid_variant fm v = true ->
    project_variant (lift_to_product_line ac fm) v = ac.
Proof.
  intros ac fm v Hv.
  unfold project_variant, lift_to_product_line. simpl.
  rewrite filter_true_map_node.
  rewrite filter_true_map_link.
  rewrite map_an_node_id.
  rewrite map_al_link_id.
  destruct ac; reflexivity.
Qed.

(* ================================================================== *)
(* Invalidation across variants                                        *)
(* ================================================================== *)

(** Which variants are affected by adding/removing a feature? *)
Definition variants_affected_by_feature (plc : ProductLineCase)
    (f : Feature) : list Id :=
  map (fun an => an.(an_node).(node_id))
    (filter (fun an =>
      (* Node's feature expression mentions f *)
      match an.(an_feature) with
      | FEAtom g => String.eqb f g
      | _ => false
      end) plc.(plc_nodes)).

(* ================================================================== *)
(* Lifted cases preserve well-formedness                              *)
(* ================================================================== *)

(** A lifted case projected to any valid variant recovers the
    original, so well-formedness is trivially preserved. *)
Theorem lift_preserves_wf : forall ac fm v,
    WellFormed ac ->
    valid_variant fm v = true ->
    WellFormed (project_variant (lift_to_product_line ac fm) v).
Proof.
  intros ac fm v Hwf Hv.
  rewrite project_lifted; [exact Hwf | exact Hv].
Qed.

(** Boolean version: structural checks pass on any valid projection
    of a lifted case. *)
Corollary lift_preserves_structural : forall ac fm v,
    structural_checks ac = true ->
    valid_variant fm v = true ->
    structural_checks (project_variant (lift_to_product_line ac fm) v) = true.
Proof.
  intros ac fm v Hsc Hv.
  rewrite project_lifted; [exact Hsc | exact Hv].
Qed.
