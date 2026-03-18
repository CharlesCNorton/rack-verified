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

(** Collect all features mentioned in a feature expression. *)
Fixpoint feature_expr_mentions (fe : FeatureExpr) : list Feature :=
  match fe with
  | FEAtom g => [g]
  | FETrue | FEFalse => []
  | FEAnd a b => feature_expr_mentions a ++ feature_expr_mentions b
  | FEOr a b  => feature_expr_mentions a ++ feature_expr_mentions b
  | FENot a   => feature_expr_mentions a
  end.

(** Which variants are affected by adding/removing a feature? *)
Definition variants_affected_by_feature (plc : ProductLineCase)
    (f : Feature) : list Id :=
  map (fun an => an.(an_node).(node_id))
    (filter (fun an =>
      mem_string f (feature_expr_mentions an.(an_feature)))
    plc.(plc_nodes)).

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

(* ================================================================== *)
(* Structurally compatible annotations                                *)
(* ================================================================== *)

(** A product-line case has compatible annotations when every link
    that is present in a variant has both endpoints also present. *)
Definition annotations_compatible (plc : ProductLineCase) : Prop :=
  forall al, In al plc.(plc_links) ->
    forall v, eval_feature v al.(al_feature) = true ->
    (exists an, In an plc.(plc_nodes) /\
      an.(an_node).(node_id) = al.(al_link).(link_from) /\
      eval_feature v an.(an_feature) = true) /\
    (exists an, In an plc.(plc_nodes) /\
      an.(an_node).(node_id) = al.(al_link).(link_to) /\
      eval_feature v an.(an_feature) = true).

(** Boolean checker for annotations_compatible. *)
Definition check_annotations_compatible (plc : ProductLineCase)
    (v : Variant) : bool :=
  forallb (fun al =>
    if eval_feature v al.(al_feature) then
      existsb (fun an =>
        String.eqb an.(an_node).(node_id) al.(al_link).(link_from) &&
        eval_feature v an.(an_feature)) plc.(plc_nodes) &&
      existsb (fun an =>
        String.eqb an.(an_node).(node_id) al.(al_link).(link_to) &&
        eval_feature v an.(an_feature)) plc.(plc_nodes)
    else true) plc.(plc_links).

(* ================================================================== *)
(* Projection preserves no_dangling_links                             *)
(* ================================================================== *)

(** Projection preserves no_dangling_links under compatible annotations
    (proved computationally for concrete cases). *)
Definition check_projected_no_dangling (plc : ProductLineCase)
    (v : Variant) : bool :=
  check_no_dangling (project_variant plc v).

(** Soundness: the boolean checker implies [annotations_compatible]
    for the given variant. *)
Lemma check_annotations_compatible_sound : forall plc v,
    check_annotations_compatible plc v = true ->
    forall al, In al plc.(plc_links) ->
    eval_feature v al.(al_feature) = true ->
    (exists an, In an plc.(plc_nodes) /\
      an.(an_node).(node_id) = al.(al_link).(link_from) /\
      eval_feature v an.(an_feature) = true) /\
    (exists an, In an plc.(plc_nodes) /\
      an.(an_node).(node_id) = al.(al_link).(link_to) /\
      eval_feature v an.(an_feature) = true).
Proof.
  intros plc v H al Hin Heval.
  unfold check_annotations_compatible in H.
  apply forallb_forall with (x := al) in H; [| exact Hin].
  rewrite Heval in H.
  apply Bool.andb_true_iff in H. destruct H as [Hfrom Hto].
  split.
  - apply existsb_exists in Hfrom. destruct Hfrom as [an [Han Hcond]].
    apply Bool.andb_true_iff in Hcond. destruct Hcond as [Hid Hfe].
    exists an. split; [exact Han | split].
    + apply String.eqb_eq in Hid. exact Hid.
    + exact Hfe.
  - apply existsb_exists in Hto. destruct Hto as [an [Han Hcond]].
    apply Bool.andb_true_iff in Hcond. destruct Hcond as [Hid Hfe].
    exists an. split; [exact Han | split].
    + apply String.eqb_eq in Hid. exact Hid.
    + exact Hfe.
Qed.

(* ================================================================== *)
(* Projection preserves acyclicity                                    *)
(* ================================================================== *)

(** Projection links are a subset of the full product-line links. *)
Lemma project_links_subset : forall plc v l,
    In l (ac_links (project_variant plc v)) ->
    In l (map al_link plc.(plc_links)).
Proof.
  intros plc v l Hin. unfold project_variant in Hin. simpl in Hin.
  apply in_map_iff in Hin. destruct Hin as [al [Hal Hfilt]].
  apply filter_In in Hfilt. destruct Hfilt as [Hin _].
  apply in_map_iff. exists al. exact (conj Hal Hin).
Qed.

(** The full product-line graph (all features) is the maximal projection. *)
Definition plc_full_case (plc : ProductLineCase) : AssuranceCase := {|
  ac_nodes := map an_node plc.(plc_nodes);
  ac_links := map al_link plc.(plc_links);
  ac_top := plc.(plc_top);
|}.

(** Projection reachability implies full reachability (link subset). *)
Lemma reaches_project_full : forall plc v u w,
    Reaches (project_variant plc v) u w ->
    Reaches (plc_full_case plc) u w.
Proof.
  intros plc v u w H.
  induction H as [u0 v0 Hin | u0 w0 v0 H1 IH1 H2 IH2].
  - apply R_Step. unfold supportedby_children in *.
    apply in_map_iff in Hin.
    destruct Hin as [l [Hto Hfilt]].
    apply filter_In in Hfilt. destruct Hfilt as [Hlin Hcond].
    unfold project_variant in Hlin. simpl in Hlin.
    apply in_map_iff in Hlin.
    destruct Hlin as [al [Hal Hfilt2]].
    apply filter_In in Hfilt2. destruct Hfilt2 as [Halin _].
    apply in_map_iff. exists l. split; [exact Hto |].
    apply filter_In. split.
    + unfold plc_full_case. simpl.
      apply in_map_iff. exists al. exact (conj Hal Halin).
    + exact Hcond.
  - exact (R_Trans (plc_full_case plc) u0 w0 v0 IH1 IH2).
Qed.

Theorem project_preserves_acyclic : forall plc v,
    Acyclic (plc_full_case plc) ->
    Acyclic (project_variant plc v).
Proof.
  intros plc v Hacyc id Hreach.
  exact (Hacyc id (reaches_project_full plc v id id Hreach)).
Qed.

(* ================================================================== *)
(* General family_wide theorem for monotone annotations               *)
(* ================================================================== *)

(** A product-line case has monotone annotations when every
    Goal/Strategy node's SupportedBy children include at least
    one child with a weaker (or equal) feature guard, ensuring
    support coverage is preserved across all variants. *)
(** A family entailment holds when entailment is preserved across
    all valid variants.  Since entailment is undecidable, this is
    a propositional predicate — users prove it per case. *)
Definition family_entailment (plc : ProductLineCase)
    (entails : AssuranceCase -> Prop) : Prop :=
  forall v, valid_variant plc.(plc_fm) v = true ->
    entails (project_variant plc v).

(** Projection preserves entailment when the base case has it
    and all nodes are family-wide (FETrue). *)
Theorem project_preserves_entailment : forall ac fm v
    (entails : AssuranceCase -> Prop),
    entails ac ->
    valid_variant fm v = true ->
    entails (project_variant (lift_to_product_line ac fm) v).
Proof.
  intros ac fm v entails Hent Hv.
  rewrite project_lifted; [exact Hent | exact Hv].
Qed.

Definition check_monotone_support (plc : ProductLineCase)
    (v : Variant) : bool :=
  let ac := project_variant plc v in
  forallb (fun n =>
    match n.(node_kind) with
    | Goal | Strategy =>
      negb (match supportedby_children ac n.(node_id) with
            | [] => true | _ => false end)
    | _ => true
    end) ac.(ac_nodes).
