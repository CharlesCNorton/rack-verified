(* ------------------------------------------------------------------ *)
(* Main theorem                                                         *)
(* ------------------------------------------------------------------ *)

From RACK Require Import Core.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(* Decomposed well-foundedness lemmas                                  *)
(* ------------------------------------------------------------------ *)

(* Height of a node in the support DAG, computed with bounded fuel.    *)
(* Fuel 0 yields 0. Fuel S f yields 0 for leaves, and                 *)
(* S(max children heights at fuel f) for internal nodes.               *)
Fixpoint height_fuel (ac : AssuranceCase) (fuel : nat) (id : Id) : nat :=
  match fuel with
  | 0 => 0
  | S f =>
    match supportedby_children ac id with
    | [] => 0
    | k :: ks => S (fold_right Nat.max 0 (map (height_fuel ac f) (k :: ks)))
    end
  end.

Arguments supportedby_children : simpl never.

Lemma height_fuel_S : forall ac f id,
    height_fuel ac (S f) id =
    match supportedby_children ac id with
    | [] => 0
    | k :: ks => S (fold_right Nat.max 0 (map (height_fuel ac f) (k :: ks)))
    end.
Proof. intros; reflexivity. Qed.

(* Reachability is transitive.                                         *)
Lemma reaches_trans : forall ac u w v,
    Reaches ac u w -> Reaches ac w v -> Reaches ac u v.
Proof.
  intros. exact (R_Trans ac u w v H H0).
Qed.

(* A child is reachable from its parent in one step.                  *)
Lemma child_reaches : forall ac parent kid,
    In kid (supportedby_children ac parent) ->
    Reaches ac parent kid.
Proof.
  intros. exact (R_Step ac parent kid H).
Qed.

(* Everything reachable from a child is reachable from parent.        *)
Lemma reachable_from_child : forall ac parent kid x,
    In kid (supportedby_children ac parent) ->
    Reaches ac kid x ->
    Reaches ac parent x.
Proof.
  intros.
  apply R_Trans with kid.
  - apply R_Step. exact H.
  - exact H0.
Qed.

(* In an acyclic graph, a parent is NOT reachable from its child.     *)
Lemma acyclic_no_back_edge : forall ac parent kid,
    Acyclic ac ->
    In kid (supportedby_children ac parent) ->
    ~ Reaches ac kid parent.
Proof.
  intros ac parent kid Hacyc Hkid Hback.
  apply (Hacyc parent).
  exact (R_Trans ac parent kid parent (R_Step ac parent kid Hkid) Hback).
Qed.

(* Auxiliary: an element's image <= fold_right max over the list.      *)
Lemma In_le_fold_max : forall (f : string -> nat) (x : string) (xs : list string),
    In x xs -> f x <= fold_right Nat.max 0 (map f xs).
Proof.
  intros f x xs Hin.
  induction xs as [|y ys IH].
  - destruct Hin.
  - simpl. destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (fold_right Nat.max 0 (map f ys)).
      * exact (IH Hin).
      * apply Nat.le_max_r.
Qed.

(* Auxiliary: fold_right max bounded when all elements bounded.       *)
Lemma fold_max_le : forall (f : string -> nat) (bound : nat) (xs : list string),
    (forall x, In x xs -> f x <= bound) ->
    fold_right Nat.max 0 (map f xs) <= bound.
Proof.
  intros f bound xs Hall.
  induction xs as [|y ys IH]; simpl.
  - apply Nat.le_0_l.
  - apply Nat.max_lub.
    + apply Hall. left. reflexivity.
    + apply IH. intros z Hz. apply Hall. right. exact Hz.
Qed.

(* height_fuel is bounded by fuel.                                     *)
Lemma height_fuel_le : forall ac fuel id,
    height_fuel ac fuel id <= fuel.
Proof.
  intros ac fuel. induction fuel as [|f IH]; intro id.
  - reflexivity.
  - rewrite height_fuel_S.
    destruct (supportedby_children ac id) as [|k ks].
    + apply Nat.le_0_l.
    + apply le_n_S. apply fold_max_le.
      intros x Hx. apply IH.
Qed.

(* A child's height at fuel f is < parent's at fuel (S f).             *)
Lemma height_child_fuel : forall ac fuel id kid,
    In kid (supportedby_children ac id) ->
    height_fuel ac fuel kid < height_fuel ac (S fuel) id.
Proof.
  intros ac fuel id kid Hkid.
  rewrite height_fuel_S.
  destruct (supportedby_children ac id) as [|k ks] eqn:Hkids.
  - destruct Hkid.
  - apply le_n_S.
    exact (In_le_fold_max (height_fuel ac fuel) kid (k :: ks) Hkid).
Qed.

Lemma children_reachable : forall ac id kid,
    (id = ac.(ac_top) \/ Reaches ac ac.(ac_top) id) ->
    In kid (supportedby_children ac id) ->
    (kid = ac.(ac_top) \/ Reaches ac ac.(ac_top) kid).
Proof.
  intros ac id kid [-> | H] Hkid.
  - right. apply R_Step. exact Hkid.
  - right. apply R_Trans with id.
    + exact H.
    + apply R_Step. exact Hkid.
Qed.

(* Acc from fuel induction — if height < fuel, then Acc.               *)
Lemma acc_by_fuel : forall ac fuel id,
    WellFormed ac ->
    (id = ac.(ac_top) \/ Reaches ac ac.(ac_top) id) ->
    height_fuel ac fuel id < fuel ->
    Acc (fun kid parent => In kid (supportedby_children ac parent)) id.
Proof.
  intros ac fuel. induction fuel as [|fuel' IH]; intros id HWF Hreach Hlt.
  - inversion Hlt.
  - constructor. intros kid Hkid.
    apply IH.
    + exact HWF.
    + exact (children_reachable ac id kid Hreach Hkid).
    + pose proof (height_child_fuel ac fuel' id kid Hkid) as H1.
      exact (Nat.lt_le_trans _ _ _ H1
              (proj1 (Nat.lt_succ_r _ _) Hlt)).
Qed.

(* ------------------------------------------------------------------ *)
(* Path-length bound (pigeonhole)                                      *)
(* ------------------------------------------------------------------ *)

(* A nonempty list's fold_right max is attained by some element.       *)
Lemma fold_max_witness : forall (f : string -> nat) (l : list string),
    l <> [] ->
    exists y, In y l /\ f y = fold_right Nat.max 0 (map f l).
Proof.
  intros f l. induction l as [|a l' IH]; intro Hne.
  - contradiction.
  - destruct l' as [|b l''].
    + exists a. simpl. split; [left; reflexivity | symmetry; apply Nat.max_0_r].
    + assert (Hne': b :: l'' <> []) by discriminate.
      destruct (IH Hne') as [y [Hy Heq]].
      destruct (Nat.le_gt_cases (f a) (fold_right Nat.max 0 (map f (b :: l'')))) as [Hle | Hgt].
      * exists y. split.
        -- right; exact Hy.
        -- change (fold_right Nat.max 0 (map f (a :: b :: l'')))
             with (Nat.max (f a) (fold_right Nat.max 0 (map f (b :: l'')))).
           rewrite (Nat.max_r _ _ Hle). exact Heq.
      * exists a. split.
        -- left; reflexivity.
        -- change (fold_right Nat.max 0 (map f (a :: b :: l'')))
             with (Nat.max (f a) (fold_right Nat.max 0 (map f (b :: l'')))).
           symmetry. apply Nat.max_l. apply Nat.lt_le_incl. exact Hgt.
Qed.

(* Extract a descending path of ids from a node with height = fuel.   *)
Fixpoint extract_path (ac : AssuranceCase) (fuel : nat) (id : Id)
  : list Id :=
  id :: match fuel with
        | 0 => []
        | S f =>
          match supportedby_children ac id with
          | [] => []
          | k :: ks =>
            let m := fold_right Nat.max 0
                       (map (height_fuel ac f) (k :: ks)) in
            match find (fun kid => Nat.eqb (height_fuel ac f kid) m)
                       (k :: ks) with
            | Some kid => extract_path ac f kid
            | None => []
            end
          end
        end.

Arguments extract_path : simpl never.

Lemma extract_path_0 : forall ac id,
    extract_path ac 0 id = [id].
Proof. intros; reflexivity. Qed.

Lemma extract_path_S : forall ac f id,
    extract_path ac (S f) id =
    id :: match supportedby_children ac id with
          | [] => []
          | k :: ks =>
            let m := fold_right Nat.max 0
                       (map (height_fuel ac f) (k :: ks)) in
            match find (fun kid => Nat.eqb (height_fuel ac f kid) m)
                       (k :: ks) with
            | Some kid => extract_path ac f kid
            | None => []
            end
          end.
Proof. intros; reflexivity. Qed.

(* Helper: the find in extract_path always succeeds when the fold     *)
(* equals the fuel (some element attains the max).                     *)
Lemma find_max_succeeds : forall ac f k ks,
    find (fun kid => Nat.eqb (height_fuel ac f kid)
            (fold_right Nat.max 0 (map (height_fuel ac f) (k :: ks))))
         (k :: ks) <> None.
Proof.
  intros ac f k ks Hnone.
  destruct (fold_max_witness (height_fuel ac f) (k :: ks) ltac:(discriminate))
    as [y [Hy Hyeq]].
  pose proof (find_none _ _ Hnone y Hy) as Hfalse.
  cbv beta in Hfalse. rewrite Hyeq, Nat.eqb_refl in Hfalse. discriminate.
Qed.

(* Helper: a child found by find_max has height = fold value.          *)
Lemma find_max_height : forall ac f k ks kid,
    find (fun kid0 => Nat.eqb (height_fuel ac f kid0)
            (fold_right Nat.max 0 (map (height_fuel ac f) (k :: ks))))
         (k :: ks) = Some kid ->
    height_fuel ac f kid = fold_right Nat.max 0 (map (height_fuel ac f) (k :: ks)).
Proof.
  intros ac f k ks kid Hfind.
  apply find_some in Hfind. destruct Hfind as [_ Hbeq].
  apply Nat.eqb_eq in Hbeq. exact Hbeq.
Qed.

(* When height = fuel, the found child has height = fuel - 1.         *)
Lemma found_child_height : forall ac f k ks kid,
    fold_right Nat.max 0 (map (height_fuel ac f) (k :: ks)) = f ->
    find (fun kid0 => Nat.eqb (height_fuel ac f kid0)
            (fold_right Nat.max 0 (map (height_fuel ac f) (k :: ks))))
         (k :: ks) = Some kid ->
    height_fuel ac f kid = f.
Proof.
  intros ac f k ks kid Hmax Hfind.
  pose proof (find_max_height ac f k ks kid Hfind) as Heq.
  pose proof (height_fuel_le ac f kid) as Hle.
  rewrite Heq, Hmax in Hle.
  rewrite Heq, Hmax.
  apply Nat.le_antisymm; [exact Hle | apply Nat.le_refl].
Qed.

(* The path has length fuel + 1 when height = fuel.                   *)
Lemma extract_path_length : forall ac fuel id,
    height_fuel ac fuel id = fuel ->
    length (extract_path ac fuel id) = S fuel.
Proof.
  intros ac fuel. induction fuel as [|f IH]; intros id Heq.
  - reflexivity.
  - rewrite extract_path_S. cbv zeta. rewrite height_fuel_S in Heq.
    remember (supportedby_children ac id) as kids eqn:Hkids.
    destruct kids as [|k ks].
    + discriminate.
    + injection Heq as Hmax.
      remember (find _ (k :: ks)) as fres eqn:Hfind.
      destruct fres as [child|].
      * simpl. f_equal. apply IH.
        exact (found_child_height ac f k ks child Hmax (eq_sym Hfind)).
      * exfalso. exact (find_max_succeeds ac f k ks (eq_sym Hfind)).
Qed.

(* Every id on the path is reachable from the head.                   *)
Lemma extract_path_reachable : forall ac fuel id x,
    In x (extract_path ac fuel id) ->
    x = id \/ Reaches ac id x.
Proof.
  intros ac fuel. induction fuel as [|f IH]; intros id x Hin.
  - rewrite extract_path_0 in Hin. destruct Hin as [<- | []]. left; reflexivity.
  - rewrite extract_path_S in Hin. cbv zeta in Hin. destruct Hin as [<- | Hin].
    + left; reflexivity.
    + right.
      remember (supportedby_children ac id) as kids eqn:Hkids.
      destruct kids as [|k ks]; [destruct Hin |].
      remember (find _ (k :: ks)) as fres eqn:Hfind.
      destruct fres as [child|]; [| destruct Hin].
      assert (Hchild_in: In child (k :: ks)).
      { symmetry in Hfind. exact (proj1 (find_some _ _ Hfind)). }
      rewrite Hkids in Hchild_in.
      destruct (IH child x Hin) as [-> | Hreach].
      * exact (R_Step ac id child Hchild_in).
      * exact (R_Trans ac id child x (R_Step ac id child Hchild_in) Hreach).
Qed.

(* Reachable nodes exist in ac_nodes.                                 *)
Lemma reachable_find_node : forall ac id,
    WellFormed ac ->
    (id = ac.(ac_top) \/ Reaches ac ac.(ac_top) id) ->
    exists n, find_node ac id = Some n.
Proof.
  intros ac id HWF Hreach.
  pose proof (wf_discharged _ HWF id Hreach) as Hdisch.
  destruct (find_node ac id) as [n|].
  - exists n; reflexivity.
  - exfalso; exact Hdisch.
Qed.

(* find_node = Some n implies n is In ac_nodes.                       *)
Lemma find_node_in : forall ac id n,
    find_node ac id = Some n -> In n ac.(ac_nodes).
Proof.
  intros ac id n H. unfold find_node in H.
  apply find_some in H. exact (proj1 H).
Qed.

(* find_node = Some n implies node_id n = id.                        *)
Lemma find_node_id : forall ac id n,
    find_node ac id = Some n -> n.(node_id) = id.
Proof.
  intros ac id n H. unfold find_node in H.
  apply find_some in H. destruct H as [_ Heqb].
  apply String.eqb_eq in Heqb. exact Heqb.
Qed.

(* Reachable ids appear in the node-id list.                          *)
Lemma reachable_in_node_ids : forall ac id,
    WellFormed ac ->
    (id = ac.(ac_top) \/ Reaches ac ac.(ac_top) id) ->
    In id (map node_id ac.(ac_nodes)).
Proof.
  intros ac id HWF Hreach.
  destruct (reachable_find_node ac id HWF Hreach) as [n Hfind].
  apply in_map_iff. exists n. split.
  - exact (find_node_id ac id n Hfind).
  - exact (find_node_in ac id n Hfind).
Qed.

(* Path nodes are all in the node-id list (when head is reachable).   *)
Lemma extract_path_in_node_ids : forall ac fuel id x,
    WellFormed ac ->
    (id = ac.(ac_top) \/ Reaches ac ac.(ac_top) id) ->
    In x (extract_path ac fuel id) ->
    In x (map node_id ac.(ac_nodes)).
Proof.
  intros ac fuel id x HWF Hreach Hin.
  destruct (extract_path_reachable ac fuel id x Hin) as [-> | Hx].
  - exact (reachable_in_node_ids ac id HWF Hreach).
  - apply reachable_in_node_ids; [exact HWF |].
    destruct Hreach as [-> | Htop].
    + right; exact Hx.
    + right; exact (R_Trans ac _ id x Htop Hx).
Qed.

(* Path ids are pairwise distinct (acyclicity).                       *)
Lemma extract_path_NoDup : forall ac fuel id,
    Acyclic ac ->
    height_fuel ac fuel id = fuel ->
    NoDup (extract_path ac fuel id).
Proof.
  intros ac fuel. induction fuel as [|f IH]; intros id Hacyc Heq.
  - rewrite extract_path_0. constructor; [exact (fun H => H) | constructor].
  - rewrite extract_path_S. cbv zeta.
    remember (supportedby_children ac id) as kids eqn:Hkids.
    destruct kids as [|k ks].
    + rewrite height_fuel_S in Heq. rewrite <- Hkids in Heq. discriminate.
    + remember (find _ (k :: ks)) as fres eqn:Hfind.
      destruct fres as [child|].
      * constructor.
        -- intro Hin.
           assert (Hchild_in: In child (k :: ks)).
           { symmetry in Hfind. exact (proj1 (find_some _ _ Hfind)). }
           rewrite Hkids in Hchild_in.
           destruct (extract_path_reachable ac f child id Hin) as [Heqid | Hreach].
           ++ subst child. exact (Hacyc id (R_Step ac id id Hchild_in)).
           ++ exact (acyclic_no_back_edge ac id child Hacyc Hchild_in Hreach).
        -- apply IH; [exact Hacyc |].
           rewrite height_fuel_S in Heq. rewrite <- Hkids in Heq.
           injection Heq as Hmax.
           exact (found_child_height ac f k ks child Hmax (eq_sym Hfind)).
      * exfalso. exact (find_max_succeeds ac f k ks (eq_sym Hfind)).
Qed.

(* Pigeonhole: NoDup list included in another has bounded length.     *)
Lemma NoDup_incl_le : forall (l1 l2 : list string),
    NoDup l1 ->
    (forall x, In x l1 -> In x l2) ->
    length l1 <= length l2.
Proof.
  intros l1. induction l1 as [|a l1' IH]; intros l2 Hnd Hincl.
  - apply Nat.le_0_l.
  - inversion Hnd as [| ? ? Hna Hnd']; subst.
    assert (Hin: In a l2) by (apply Hincl; left; reflexivity).
    apply in_split in Hin. destruct Hin as [l2a [l2b Heq]]. subst l2.
    simpl. rewrite length_app. simpl.
    rewrite Nat.add_succ_r. apply le_n_S.
    rewrite <- length_app.
    apply IH; [exact Hnd' |].
    intros x Hx.
    assert (Hx2: In x (l2a ++ a :: l2b)) by (apply Hincl; right; exact Hx).
    apply in_app_or in Hx2. apply in_or_app.
    destruct Hx2 as [Hl | Hr].
    + left; exact Hl.
    + destruct Hr as [Heqa | Hr].
      * subst x. exfalso. exact (Hna Hx).
      * right; exact Hr.
Qed.

(* height_fuel at fuel = |nodes| is strictly less than |nodes|.        *)
Lemma height_fuel_lt_nodes : forall ac id,
    WellFormed ac ->
    (id = ac.(ac_top) \/ Reaches ac ac.(ac_top) id) ->
    height_fuel ac (length (ac_nodes ac)) id < length (ac_nodes ac).
Proof.
  intros ac id HWF Hreach.
  set (N := length (ac_nodes ac)).
  pose proof (height_fuel_le ac N id) as Hle.
  destruct (Nat.eq_dec (height_fuel ac N id) N) as [Heq | Hne].
  - exfalso.
    pose proof (extract_path_length ac N id Heq) as Hplen.
    pose proof (extract_path_NoDup ac N id (wf_acyclic _ HWF) Heq) as Hnd.
    pose proof (NoDup_incl_le
                  (extract_path ac N id)
                  (map node_id ac.(ac_nodes))
                  Hnd
                  (fun x Hx => extract_path_in_node_ids ac N id x HWF Hreach Hx))
      as Hinc.
    assert (Habs: S N <= N).
    { apply Nat.le_trans with (length (map node_id ac.(ac_nodes))).
      - rewrite <- Hplen. exact Hinc.
      - rewrite length_map. unfold N. apply Nat.le_refl. }
    exact (Nat.nle_succ_diag_l N Habs).
  - apply Nat.lt_eq_cases in Hle. destruct Hle as [Hlt | Heq].
    + exact Hlt.
    + exfalso; exact (Hne Heq).
Qed.

(* Assembly: child_rel_acc follows from acc_by_fuel + height bound.   *)
Lemma child_rel_acc : forall ac id,
    WellFormed ac ->
    (id = ac.(ac_top) \/ Reaches ac ac.(ac_top) id) ->
    Acc (fun kid parent => In kid (supportedby_children ac parent)) id.
Proof.
  intros ac id HWF Hreach.
  exact (acc_by_fuel ac (length (ac_nodes ac)) id HWF Hreach
          (height_fuel_lt_nodes ac id HWF Hreach)).
Qed.

Lemma support_tree_of_reachable :
  forall ac, WellFormed ac ->
  forall id, (id = ac.(ac_top) \/ Reaches ac ac.(ac_top) id) ->
  SupportTree ac id.
Proof.
  intros ac HWF id Hreach.
  induction (child_rel_acc ac id HWF Hreach) as [id _ IH].
  pose proof (wf_discharged _ HWF id Hreach) as Hdisch.
  pose proof (wf_entailment _ HWF)           as Hent.
  destruct (find_node ac id) as [n|] eqn:Hfind.
  2: { exact (False_ind _ Hdisch). }
  destruct (n.(node_kind)) eqn:Hkind.

  - (* Goal *)
    apply ST_Internal with n (supportedby_children ac id).
    + exact Hfind.
    + rewrite Hkind; discriminate.
    + reflexivity.
    + exact Hdisch.
    + intros kid Hkid.
      apply IH; [exact Hkid | apply children_reachable with id; assumption].
    + apply Hent; [exact Hfind | left; exact Hkind].

  - (* Strategy — identical structure to Goal *)
    apply ST_Internal with n (supportedby_children ac id).
    + exact Hfind.
    + rewrite Hkind; discriminate.
    + reflexivity.
    + exact Hdisch.
    + intros kid Hkid.
      apply IH; [exact Hkid | apply children_reachable with id; assumption].
    + apply Hent; [exact Hfind | right; exact Hkind].

  - (* Solution *)
    destruct Hdisch as [e [He Hvalid]].
    exact (ST_Leaf ac id n e Hfind Hkind He Hvalid).

  - (* Context *)
    exact (ST_Annotation ac id n Hfind (or_introl Hkind)).

  - (* Assumption *)
    exact (ST_Annotation ac id n Hfind (or_intror (or_introl Hkind))).

  - (* Justification *)
    exact (ST_Annotation ac id n Hfind (or_intror (or_intror Hkind))).
Qed.

(* A well-formed assurance case has a complete, non-circular support   *)
(* tree rooted at its top goal, where every leaf carries valid         *)
(* evidence for its own claim and every internal node's claim is       *)
(* entailed by its children.                                           *)

Theorem assurance_case_supported :
  forall ac, WellFormed ac -> SupportTree ac ac.(ac_top).
Proof.
  intros ac HWF.
  apply support_tree_of_reachable; [exact HWF | left; reflexivity].
Qed.
