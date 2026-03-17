(******************************************************************************)
(*                                                                            *)
(*          Rocq Assurance Case Kernel: Topological Sorting                   *)
(*                                                                            *)
(*     Kahn's algorithm, verify_topo_order, structural_checks.               *)
(*     Completeness machinery: topo_sort_complete, topo_sort_nodup,          *)
(*     topo_sort_subset, topo_sort_length.                                   *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: March 17, 2026                                                   *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From RACK Require Import Types.
From RACK Require Import Graph.
From RACK Require Import WellFormedness.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(* ------------------------------------------------------------------ *)
(* Topological ordering for acyclicity decision                         *)
(* ------------------------------------------------------------------ *)

Fixpoint index_of (s : string) (l : list string) : option nat :=
  match l with
  | [] => None
  | x :: xs =>
    if String.eqb s x then Some 0
    else match index_of s xs with
         | Some n => Some (S n)
         | None => None
         end
  end.

(* SupportedBy in-degree restricted to a set of remaining nodes.       *)
Definition sb_in_degree (ac : AssuranceCase)
    (remaining : list Id) (id : Id) : nat :=
  length (filter (fun l =>
    match l.(link_kind) with
    | SupportedBy =>
      String.eqb l.(link_to) id && mem_string l.(link_from) remaining
    | _ => false
    end) ac.(ac_links)).

(* Kahn's algorithm: peel zero-in-degree nodes.                        *)
Fixpoint topo_sort_go (ac : AssuranceCase) (fuel : nat)
    (remaining : list Id) (acc : list Id) : list Id :=
  match fuel with
  | 0 => acc
  | S f =>
    match find (fun id => Nat.eqb (sb_in_degree ac remaining id) 0)
               remaining with
    | None => acc
    | Some id =>
      let remaining' :=
        filter (fun x => negb (String.eqb x id)) remaining in
      topo_sort_go ac f remaining' (acc ++ [id])
    end
  end.

Definition topo_sort (ac : AssuranceCase) : list Id :=
  topo_sort_go ac (length ac.(ac_nodes))
               (map node_id ac.(ac_nodes)) [].

(* Verify a candidate topological order: every SupportedBy edge goes
   from a lower to a higher index, all node IDs appear, no duplicates. *)
Definition verify_topo_order (ac : AssuranceCase)
    (order : list Id) : bool :=
  forallb (fun l =>
    match l.(link_kind) with
    | SupportedBy =>
      match index_of l.(link_from) order,
            index_of l.(link_to)   order with
      | Some i, Some j => Nat.ltb i j
      | _, _ => false
      end
    | _ => true
    end) ac.(ac_links) &&
  forallb (fun n => mem_string n.(node_id) order)
          ac.(ac_nodes) &&
  nodupb order.

(* Combined structural checks with proved soundness (see Reflect.v:
   build_well_formed).  Uses verify_topo_order for acyclicity
   (soundness proved via verify_topo_order_acyclic) and
   check_all_discharged for evidence coverage (stronger than the
   reachable-only check, easier to reflect).
   For concrete assurance cases, structural_checks and
   check_wf_extended agree — see Example.v for computational proofs.   *)
Definition structural_checks (ac : AssuranceCase) : bool :=
  check_top_is_goal ac &&
  check_unique_ids ac &&
  check_no_dangling ac &&
  verify_topo_order ac (topo_sort ac) &&
  check_all_discharged ac &&
  check_context_links ac.

(* ------------------------------------------------------------------ *)
(* topo_sort completeness                                              *)
(* ------------------------------------------------------------------ *)

(* --- Predecessor extraction from positive in-degree --- *)

Definition extract_predecessor (ac : AssuranceCase)
    (remaining : list Id) (id : Id) : Id :=
  match filter (fun l =>
    match l.(link_kind) with
    | SupportedBy =>
      String.eqb l.(link_to) id && mem_string l.(link_from) remaining
    | _ => false
    end) ac.(ac_links) with
  | l :: _ => l.(link_from)
  | [] => id
  end.

Lemma filter_nonempty_of_length_pos : forall {A} (f : A -> bool) l,
    length (filter f l) > 0 -> exists x, In x l /\ f x = true.
Proof.
  intros A f l H.
  destruct (filter f l) as [|a rest] eqn:Ef.
  - simpl in H. inversion H.
  - assert (Ha : In a (filter f l)) by (rewrite Ef; left; reflexivity).
    apply filter_In in Ha. exists a. exact Ha.
Qed.

Lemma extract_predecessor_valid : forall ac remaining id,
    sb_in_degree ac remaining id > 0 ->
    In (extract_predecessor ac remaining id) remaining /\
    In id (supportedby_children ac (extract_predecessor ac remaining id)).
Proof.
  intros ac remaining id Hpos.
  unfold sb_in_degree in Hpos.
  unfold extract_predecessor.
  remember (filter _ ac.(ac_links)) as flinks eqn:Ef.
  destruct flinks as [|l rest].
  - simpl in Hpos. inversion Hpos.
  - assert (Hl : In l (l :: rest)) by (left; reflexivity).
    rewrite Ef in Hl. apply filter_In in Hl.
    destruct Hl as [Hlin Hcond].
    destruct l.(link_kind) eqn:Hk; try discriminate.
    apply Bool.andb_true_iff in Hcond.
    destruct Hcond as [Hto Hfrom].
    apply String.eqb_eq in Hto.
    apply existsb_In in Hfrom.
    split; [exact Hfrom |].
    unfold supportedby_children.
    apply in_map_iff. exists l. split; [exact Hto |].
    apply filter_In. split; [exact Hlin |].
    apply Bool.andb_true_iff. split.
    + apply String.eqb_refl.
    + rewrite Hk. reflexivity.
Qed.

(* --- Predecessor chain --- *)

Fixpoint pred_chain (ac : AssuranceCase) (remaining : list Id)
    (fuel : nat) (start : Id) : list Id :=
  start :: match fuel with
  | 0 => []
  | S f => pred_chain ac remaining f
             (extract_predecessor ac remaining start)
  end.

Lemma pred_chain_length : forall ac remaining fuel start,
    length (pred_chain ac remaining fuel start) = S fuel.
Proof.
  intros ac remaining fuel. induction fuel as [|f IH]; intro start; simpl.
  - reflexivity.
  - f_equal. exact (IH _).
Qed.

Lemma pred_chain_in_remaining : forall ac remaining fuel start,
    (forall id, In id remaining ->
      sb_in_degree ac remaining id > 0) ->
    In start remaining ->
    forall x, In x (pred_chain ac remaining fuel start) ->
    In x remaining.
Proof.
  intros ac remaining fuel. induction fuel as [|f IH];
    intros start Hindeg Hstart x Hin; simpl in Hin.
  - destruct Hin as [<- | []]. exact Hstart.
  - destruct Hin as [<- | Hin].
    + exact Hstart.
    + apply IH with (extract_predecessor ac remaining start);
        [exact Hindeg | | exact Hin].
      exact (proj1 (extract_predecessor_valid ac remaining start
                      (Hindeg start Hstart))).
Qed.

(* Every element after the head is reachable from the head *)
Lemma pred_chain_reaches : forall fuel ac remaining start x,
    (forall id, In id remaining ->
      sb_in_degree ac remaining id > 0) ->
    In start remaining ->
    In x (tl (pred_chain ac remaining fuel start)) ->
    Reaches ac x start.
Proof.
  induction fuel as [|f IH]; intros ac remaining start x Hindeg Hstart Hin.
  - simpl in Hin. destruct Hin.
  - simpl in Hin.
    set (next := extract_predecessor ac remaining start) in *.
    assert (Hnext_in : In next remaining).
    { exact (proj1 (extract_predecessor_valid ac remaining start
                      (Hindeg start Hstart))). }
    assert (Hedge : In start (supportedby_children ac next)).
    { exact (proj2 (extract_predecessor_valid ac remaining start
                      (Hindeg start Hstart))). }
    destruct (pred_chain ac remaining f next) as [|y rest] eqn:Hchain.
    + destruct Hin.
    + assert (Hy : y = next).
      { assert (H : hd_error (pred_chain ac remaining f next) = Some next)
          by (destruct f; reflexivity).
        rewrite Hchain in H. simpl in H. injection H. auto. }
      subst y.
      destruct Hin as [<- | Hin'].
      * exact (R_Step ac next start Hedge).
      * assert (Hin_tl : In x (tl (pred_chain ac remaining f next))).
        { rewrite Hchain. exact Hin'. }
        exact (R_Trans ac x next start
                 (IH ac remaining next x Hindeg Hnext_in Hin_tl)
                 (R_Step ac next start Hedge)).
Qed.

(* The chain is NoDup when the graph is acyclic *)
Lemma pred_chain_nodup : forall fuel ac remaining start,
    Acyclic ac ->
    (forall id, In id remaining ->
      sb_in_degree ac remaining id > 0) ->
    In start remaining ->
    NoDup (pred_chain ac remaining fuel start).
Proof.
  induction fuel as [|f IH]; intros ac remaining start Hacyc Hindeg Hstart.
  - simpl. constructor; [exact (fun H => H) | constructor].
  - remember (extract_predecessor ac remaining start) as next eqn:Enext.
    assert (Hnext_in : In next remaining).
    { subst next. exact (proj1 (extract_predecessor_valid ac remaining start
                      (Hindeg start Hstart))). }
    assert (Hedge : In start (supportedby_children ac next)).
    { subst next. exact (proj2 (extract_predecessor_valid ac remaining start
                      (Hindeg start Hstart))). }
    simpl. rewrite <- Enext. constructor.
    + intro Hin.
      destruct (pred_chain ac remaining f next) as [|y rest] eqn:Hchain.
      * destruct Hin.
      * assert (Hy : y = next) by (destruct f; simpl in Hchain; injection Hchain; auto).
        subst y. destruct Hin as [Heq | Hin'].
        -- subst start. exact (Hacyc next (R_Step ac next next Hedge)).
        -- assert (Hin_tl : In start (tl (pred_chain ac remaining f next))).
           { rewrite Hchain. exact Hin'. }
           exact (Hacyc start
                    (R_Trans ac start next start
                       (pred_chain_reaches f ac remaining next start
                          Hindeg Hnext_in Hin_tl)
                       (R_Step ac next start Hedge))).
    + apply IH; [exact Hacyc | exact Hindeg | exact Hnext_in].
Qed.

(* Pigeonhole helper *)
Lemma nodup_incl_length : forall (l1 l2 : list string),
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
    + destruct Hr as [Heqa | Hr]; [subst x; exfalso; exact (Hna Hx) | right; exact Hr].
Qed.

(* In an acyclic graph, some node has in-degree 0. *)
Lemma acyclic_has_zero_indeg : forall ac remaining,
    remaining <> [] ->
    (forall id, In id remaining ->
      In id (map node_id ac.(ac_nodes))) ->
    Acyclic ac ->
    exists id, In id remaining /\
      sb_in_degree ac remaining id = 0.
Proof.
  intros ac remaining Hne Hin Hacyc.
  destruct (existsb (fun id => Nat.eqb (sb_in_degree ac remaining id) 0)
              remaining) eqn:Hex.
  - apply existsb_exists in Hex. destruct Hex as [id [Hid Heq]].
    apply Nat.eqb_eq in Heq. exists id. exact (conj Hid Heq).
  - exfalso.
    assert (Hindeg : forall id, In id remaining ->
              sb_in_degree ac remaining id > 0).
    { intros id Hid.
      assert (Hnz : Nat.eqb (sb_in_degree ac remaining id) 0 = false).
      { destruct (existsb_exists
          (fun id0 => Nat.eqb (sb_in_degree ac remaining id0) 0)
          remaining) as [_ Hrev].
        destruct (Nat.eqb (sb_in_degree ac remaining id) 0) eqn:E;
          [| reflexivity].
        exfalso. rewrite Hex in Hrev.
        assert (Hex' : existsb
          (fun id0 => Nat.eqb (sb_in_degree ac remaining id0) 0)
          remaining = true).
        { apply existsb_exists. exists id. exact (conj Hid E). }
        rewrite Hex' in Hex. discriminate. }
      apply Nat.eqb_neq in Hnz.
      destruct (sb_in_degree ac remaining id) as [|k].
      + exfalso. exact (Hnz eq_refl).
      + apply Nat.lt_0_succ. }
    destruct remaining as [|r0 rs]; [exact (Hne eq_refl) |].
    pose proof (pred_chain_nodup
                  (length (r0 :: rs))
                  ac (r0 :: rs) r0 Hacyc Hindeg
                  (or_introl eq_refl)) as Hnd.
    pose proof (pred_chain_length ac (r0 :: rs) (length (r0 :: rs)) r0) as Hlen.
    pose proof (pred_chain_in_remaining ac (r0 :: rs) (length (r0 :: rs)) r0
                  Hindeg (or_introl eq_refl)) as Hincl.
    assert (Habs : S (length (r0 :: rs)) <= length (r0 :: rs)).
    { rewrite <- Hlen.
      exact (nodup_incl_length _ _ Hnd Hincl). }
    exact (Nat.nle_succ_diag_l _ Habs).
Qed.

(* ------------------------------------------------------------------ *)
(* topo_sort_go helpers                                                *)
(* ------------------------------------------------------------------ *)

Lemma existsb_find : forall {A : Type} (f : A -> bool) (l : list A),
    existsb f l = true -> exists x, find f l = Some x /\ f x = true.
Proof.
  induction l as [|a l' IH]; simpl; intro H.
  - discriminate.
  - apply Bool.orb_true_iff in H. destruct H as [H | H].
    + exists a. rewrite H. auto.
    + destruct (f a) eqn:E.
      * exists a. auto.
      * destruct (IH H) as [x [Hf Hx]]. exists x. auto.
Qed.

Lemma find_zero_indeg : forall ac remaining,
    remaining <> [] ->
    (forall id, In id remaining ->
      In id (map node_id ac.(ac_nodes))) ->
    Acyclic ac ->
    exists id,
      find (fun id0 => Nat.eqb (sb_in_degree ac remaining id0) 0)
           remaining = Some id.
Proof.
  intros ac remaining Hne Hin Hacyc.
  destruct (acyclic_has_zero_indeg ac remaining Hne Hin Hacyc)
    as [id [Hid Hdeg]].
  assert (Hex : existsb (fun id0 => Nat.eqb (sb_in_degree ac remaining id0) 0)
                  remaining = true).
  { apply existsb_exists. exists id. split; [exact Hid |].
    apply Nat.eqb_eq. exact Hdeg. }
  destruct (existsb_find _ _ Hex) as [x [Hfind _]].
  exists x. exact Hfind.
Qed.

Lemma filter_remove_In : forall id remaining x,
    In x (filter (fun x0 => negb (String.eqb x0 id)) remaining) ->
    In x remaining /\ x <> id.
Proof.
  intros id remaining x H.
  apply filter_In in H. destruct H as [Hin Hneq].
  split; [exact Hin |].
  intro Heq. subst. rewrite String.eqb_refl in Hneq. discriminate.
Qed.

Lemma filter_remove_length : forall id remaining,
    In id remaining -> NoDup remaining ->
    length (filter (fun x => negb (String.eqb x id)) remaining) < length remaining.
Proof.
  induction remaining as [|a rest IH]; intros Hin Hnd.
  - destruct Hin.
  - inversion Hnd as [| ? ? Hna Hnd']; subst.
    simpl. destruct (String.eqb a id) eqn:E.
    + simpl. apply Nat.lt_succ_r.
      apply filter_length_le.
    + simpl. apply -> Nat.succ_lt_mono.
      apply IH; [| exact Hnd'].
      destruct Hin as [<- | Hin].
      * rewrite String.eqb_refl in E. discriminate.
      * exact Hin.
Qed.

Lemma find_In : forall {A : Type} (f : A -> bool) (l : list A) x,
    find f l = Some x -> In x l.
Proof.
  induction l as [|a l' IH]; simpl; intros x H.
  - discriminate.
  - destruct (f a) eqn:E.
    + injection H as <-. left. reflexivity.
    + right. exact (IH x H).
Qed.

Lemma In_filter_remove : forall id remaining x,
    In x remaining -> x <> id ->
    In x (filter (fun x0 => negb (String.eqb x0 id)) remaining).
Proof.
  intros id remaining x Hin Hneq.
  apply filter_In. split; [exact Hin |].
  destruct (String.eqb x id) eqn:E; [| reflexivity].
  apply String.eqb_eq in E. exfalso. exact (Hneq E).
Qed.

Lemma NoDup_filter : forall {A : Type} (f : A -> bool) (l : list A),
    NoDup l -> NoDup (filter f l).
Proof.
  induction l as [|a l' IH]; intro Hnd; simpl.
  - constructor.
  - inversion Hnd as [| ? ? Hna Hnd']; subst.
    destruct (f a) eqn:E.
    + constructor; [| exact (IH Hnd')].
      intro H. apply filter_In in H.
      exact (Hna (proj1 H)).
    + exact (IH Hnd').
Qed.

(* ------------------------------------------------------------------ *)
(* topo_sort_complete                                                  *)
(* ------------------------------------------------------------------ *)

(* Coverage: topo_sort_go returns acc ++ elements from remaining *)
Lemma topo_sort_go_acc_prefix : forall ac fuel remaining acc x,
    In x acc -> In x (topo_sort_go ac fuel remaining acc).
Proof.
  intros ac fuel. induction fuel as [|f IH]; intros remaining acc x Hin; simpl.
  - exact Hin.
  - destruct (find _ remaining) as [id|].
    + apply IH. apply in_or_app. left. exact Hin.
    + exact Hin.
Qed.

Lemma topo_sort_go_remaining : forall ac fuel remaining acc x,
    Acyclic ac ->
    (forall id, In id remaining ->
      In id (map node_id ac.(ac_nodes))) ->
    NoDup remaining ->
    fuel >= length remaining ->
    In x remaining ->
    In x (topo_sort_go ac fuel remaining acc).
Proof.
  intros ac fuel. induction fuel as [|f IH];
    intros remaining acc x Hacyc Hin_nodes Hnd Hfuel Hx.
  - destruct remaining; [destruct Hx | simpl in Hfuel; inversion Hfuel].
  - simpl.
    destruct remaining as [|r0 rest] eqn:Hrem.
    + destruct Hx.
    + destruct (find (fun id => Nat.eqb (sb_in_degree ac (r0 :: rest) id) 0)
                  (r0 :: rest)) as [id|] eqn:Hfind.
      * assert (Hid_in : In id (r0 :: rest)) by exact (find_In _ _ _ Hfind).
        destruct (String.eqb x id) eqn:Exid.
        -- apply String.eqb_eq in Exid. subst.
           apply topo_sort_go_acc_prefix. apply in_or_app. right. left. reflexivity.
        -- apply IH.
           ++ exact Hacyc.
           ++ intros id' Hid'. apply filter_remove_In in Hid'.
              exact (Hin_nodes _ (proj1 Hid')).
           ++ exact (NoDup_filter _ _ Hnd).
           ++ assert (Hlt : length (filter (fun x0 => negb (String.eqb x0 id))
                              (r0 :: rest)) < length (r0 :: rest)).
              { exact (filter_remove_length id (r0 :: rest) Hid_in Hnd). }
              apply Nat.lt_succ_r.
              apply Nat.lt_le_trans with (length (r0 :: rest)); [exact Hlt |].
              exact Hfuel.
           ++ apply In_filter_remove; [exact Hx |].
              intro Heq. subst.
              rewrite String.eqb_refl in Exid. discriminate.
      * (* find = None: contradicts acyclic_has_zero_indeg *)
        exfalso.
        destruct (find_zero_indeg ac (r0 :: rest) ltac:(discriminate) Hin_nodes Hacyc)
          as [id' Hfind'].
        rewrite Hfind in Hfind'. discriminate.
Qed.

Lemma topo_sort_go_nodup : forall ac fuel remaining acc,
    Acyclic ac ->
    (forall id, In id remaining ->
      In id (map node_id ac.(ac_nodes))) ->
    NoDup remaining ->
    NoDup acc ->
    (forall x, In x acc -> ~ In x remaining) ->
    fuel >= length remaining ->
    NoDup (topo_sort_go ac fuel remaining acc).
Proof.
  intros ac fuel. induction fuel as [|f IH];
    intros remaining acc Hacyc Hin_nodes Hnd_rem Hnd_acc Hdisj Hfuel.
  - destruct remaining; [exact Hnd_acc | simpl in Hfuel; inversion Hfuel].
  - simpl.
    destruct remaining as [|r0 rest] eqn:Hrem.
    + exact Hnd_acc.
    + destruct (find (fun id => Nat.eqb (sb_in_degree ac (r0 :: rest) id) 0)
                  (r0 :: rest)) as [id|] eqn:Hfind.
      * assert (Hid_in : In id (r0 :: rest)) by exact (find_In _ _ _ Hfind).
        apply IH.
        -- exact Hacyc.
        -- intros id' Hid'. apply filter_remove_In in Hid'.
           exact (Hin_nodes _ (proj1 Hid')).
        -- exact (NoDup_filter _ _ Hnd_rem).
        -- apply NoDup_app; [exact Hnd_acc | |].
           ++ constructor; [| constructor].
              intro H. destruct H.
           ++ intros x Hacc [Heq | []]. subst x.
              exact (Hdisj id Hacc Hid_in).
        -- intros x Hx Hf.
           apply in_app_or in Hx. apply filter_remove_In in Hf.
           destruct Hx as [Hx | [Heq | []]].
           ++ exact (Hdisj x Hx (proj1 Hf)).
           ++ subst x. exact (proj2 Hf eq_refl).
        -- assert (Hlt : length (filter (fun x0 => negb (String.eqb x0 id))
                            (r0 :: rest)) < length (r0 :: rest)).
           { exact (filter_remove_length id (r0 :: rest) Hid_in Hnd_rem). }
           apply Nat.lt_succ_r.
           apply Nat.lt_le_trans with (length (r0 :: rest)); [exact Hlt | exact Hfuel].
      * exact Hnd_acc.
Qed.

Theorem topo_sort_complete : forall ac,
    Acyclic ac ->
    NoDup (map node_id ac.(ac_nodes)) ->
    forall x, In x (map node_id ac.(ac_nodes)) ->
    In x (topo_sort ac).
Proof.
  intros ac Hacyc Hnd x Hx.
  unfold topo_sort.
  apply topo_sort_go_remaining;
    [exact Hacyc | exact (fun id H => H) | exact Hnd
    | rewrite length_map; apply Nat.le_refl | exact Hx].
Qed.

Theorem topo_sort_nodup : forall ac,
    Acyclic ac ->
    NoDup (map node_id ac.(ac_nodes)) ->
    NoDup (topo_sort ac).
Proof.
  intros ac Hacyc Hnd. unfold topo_sort.
  apply topo_sort_go_nodup;
    [exact Hacyc | exact (fun id H => H) | exact Hnd
    | exact (NoDup_nil Id) | intros x Hx; destruct Hx
    | rewrite length_map; apply Nat.le_refl].
Qed.

Lemma topo_sort_go_subset : forall ac fuel remaining acc x,
    In x (topo_sort_go ac fuel remaining acc) ->
    In x acc \/ In x remaining.
Proof.
  intros ac fuel. induction fuel as [|f IH];
    intros remaining acc x Hx; simpl in Hx.
  - left. exact Hx.
  - destruct (find _ remaining) as [id|] eqn:Hfind.
    + apply IH in Hx. destruct Hx as [Hx | Hx].
      * apply in_app_or in Hx. destruct Hx as [Hx | [<- | []]].
        -- left. exact Hx.
        -- right. exact (find_In _ _ _ Hfind).
      * right. apply filter_remove_In in Hx. exact (proj1 Hx).
    + left. exact Hx.
Qed.

Lemma topo_sort_subset : forall ac x,
    In x (topo_sort ac) ->
    In x (map node_id ac.(ac_nodes)).
Proof.
  intros ac x Hx. unfold topo_sort in Hx.
  apply topo_sort_go_subset in Hx. destruct Hx as [Hx | Hx].
  - destruct Hx.
  - exact Hx.
Qed.

Theorem topo_sort_length : forall ac,
    Acyclic ac ->
    NoDup (map node_id ac.(ac_nodes)) ->
    length (topo_sort ac) = length (map node_id ac.(ac_nodes)).
Proof.
  intros ac Hacyc Hnd.
  apply Nat.le_antisymm.
  - exact (nodup_incl_length (topo_sort ac) (map node_id ac.(ac_nodes))
             (topo_sort_nodup ac Hacyc Hnd)
             (topo_sort_subset ac)).
  - exact (nodup_incl_length (map node_id ac.(ac_nodes)) (topo_sort ac)
             Hnd (topo_sort_complete ac Hacyc Hnd)).
Qed.

(* ================================================================== *)
(* topo_sort_valid: Kahn's produces a valid topological order          *)
(* ================================================================== *)

Lemma sb_indeg_zero_no_parent : forall ac remaining id l,
    sb_in_degree ac remaining id = 0 ->
    In l ac.(ac_links) ->
    l.(link_kind) = SupportedBy ->
    l.(link_to) = id ->
    mem_string l.(link_from) remaining = false.
Proof.
  intros ac remaining id l Hdeg Hlin Hkind Hto.
  destruct (mem_string l.(link_from) remaining) eqn:E; [| reflexivity].
  exfalso. unfold sb_in_degree in Hdeg.
  assert (Hin : In l (filter (fun l0 =>
    match l0.(link_kind) with
    | SupportedBy =>
      String.eqb l0.(link_to) id && mem_string l0.(link_from) remaining
    | _ => false end) ac.(ac_links))).
  { apply filter_In. split; [exact Hlin |].
    rewrite Hkind, Hto, String.eqb_refl, E. reflexivity. }
  destruct (filter _ _) as [|x xs] eqn:Ef.
  - destruct Hin.
  - simpl in Hdeg. discriminate.
Qed.

Lemma index_of_app_left : forall s l1 l2 i,
    index_of s l1 = Some i ->
    index_of s (l1 ++ l2) = Some i.
Proof.
  intros s l1. induction l1 as [|a l1' IH]; intros l2 i H; simpl in *.
  - discriminate.
  - destruct (String.eqb s a) eqn:E.
    + exact H.
    + destruct (index_of s l1') eqn:Ei; [| discriminate].
      injection H as <-. rewrite (IH l2 n eq_refl). reflexivity.
Qed.

Lemma index_of_app_right : forall s l1 l2 i,
    (forall j, index_of s l1 = Some j -> False) ->
    index_of s l2 = Some i ->
    index_of s (l1 ++ l2) = Some (length l1 + i).
Proof.
  intros s l1. induction l1 as [|a l1' IH]; intros l2 i Hnone H; simpl in *.
  - exact H.
  - destruct (String.eqb s a) eqn:E.
    + exfalso. exact (Hnone 0 eq_refl).
    + assert (Hnone' : forall j, index_of s l1' = Some j -> False).
      { intros j Hj. exact (Hnone (S j) ltac:(rewrite Hj; reflexivity)). }
      rewrite (IH l2 i Hnone' H). reflexivity.
Qed.

Lemma index_of_Some_In : forall s l i,
    index_of s l = Some i -> In s l.
Proof.
  intros s l. induction l as [|x xs IH]; intros i H; simpl in H.
  - discriminate.
  - destruct (String.eqb s x) eqn:Heq.
    + left. apply String.eqb_eq in Heq. exact (eq_sym Heq).
    + destruct (index_of s xs) eqn:Hrest; [| discriminate].
      right. exact (IH n eq_refl).
Qed.

Lemma index_of_None_not_In : forall s l,
    (forall i, index_of s l = Some i -> False) -> ~ In s l.
Proof.
  intros s l H Hin.
  induction l as [|a l' IH].
  - destruct Hin.
  - simpl in H. destruct Hin as [<- | Hin'].
    + rewrite String.eqb_refl in H. exact (H 0 eq_refl).
    + apply IH; [| exact Hin'].
      intros i Hi. destruct (String.eqb s a) eqn:E.
      * exact (H 0 eq_refl).
      * exact (H (S i) ltac:(rewrite Hi; reflexivity)).
Qed.

Lemma not_In_index_of_None : forall s l,
    ~ In s l -> forall i, index_of s l = Some i -> False.
Proof.
  intros s l Hni i Hi.
  exact (Hni (index_of_Some_In s l i Hi)).
Qed.

Lemma index_of_In : forall s l,
    In s l -> NoDup l -> exists i, index_of s l = Some i.
Proof.
  intros s l Hin Hnd. induction l as [|x xs IH].
  - destruct Hin.
  - inversion Hnd as [| ? ? Hna Hnd']; subst.
    simpl. destruct (String.eqb s x) eqn:Heq.
    + exists 0. reflexivity.
    + destruct Hin as [<- | Hin].
      * rewrite String.eqb_refl in Heq. discriminate.
      * destruct (IH Hin Hnd') as [i Hi].
        rewrite Hi. exists (S i). reflexivity.
Qed.

Lemma index_of_lt : forall s l i,
    index_of s l = Some i -> i < length l.
Proof.
  intros s l. induction l as [|x xs IH]; intros i H; simpl in *.
  - discriminate.
  - destruct (String.eqb s x) eqn:Heq.
    + injection H as <-. apply Nat.lt_0_succ.
    + destruct (index_of s xs) eqn:Hrest; [| discriminate].
      injection H as <-. apply -> Nat.succ_lt_mono.
      exact (IH n eq_refl).
Qed.

Lemma topo_sort_go_ordered :
  forall ac fuel remaining acc,
    Acyclic ac ->
    NoDup remaining -> NoDup acc ->
    (forall x, In x acc -> ~ In x remaining) ->
    (forall x, In x (map node_id ac.(ac_nodes)) ->
      In x acc \/ In x remaining) ->
    fuel >= length remaining ->
    (forall x, In x remaining ->
      In x (map node_id ac.(ac_nodes))) ->
    (forall l, In l ac.(ac_links) ->
      l.(link_kind) = SupportedBy ->
      In l.(link_to) acc ->
      ~ In l.(link_from) remaining) ->
    (forall l, In l ac.(ac_links) ->
      l.(link_kind) = SupportedBy ->
      In l.(link_from) acc -> In l.(link_to) acc ->
      exists i j, index_of l.(link_from) acc = Some i /\
                   index_of l.(link_to) acc = Some j /\ i < j) ->
    forall l, In l ac.(ac_links) ->
      l.(link_kind) = SupportedBy ->
      In l.(link_from) (map node_id ac.(ac_nodes)) ->
      In l.(link_to) (map node_id ac.(ac_nodes)) ->
      exists i j,
        index_of l.(link_from) (topo_sort_go ac fuel remaining acc) = Some i /\
        index_of l.(link_to) (topo_sort_go ac fuel remaining acc) = Some j /\
        i < j.
Proof.
  intros ac fuel. induction fuel as [|f IH];
    intros remaining acc Hacyc Hnd_rem Hnd_acc Hdisj Hpart Hfuel
           Hnodes Hup Hord l Hlin Hkind Hfrom_n Hto_n.
  - destruct remaining; [| simpl in Hfuel; inversion Hfuel].
    simpl. apply Hord; [exact Hlin | exact Hkind | |].
    + destruct (Hpart _ Hfrom_n) as [H|H]; [exact H | destruct H].
    + destruct (Hpart _ Hto_n) as [H|H]; [exact H | destruct H].
  - simpl.
    destruct remaining as [|r0 rest] eqn:Hrem.
    + apply Hord; [exact Hlin | exact Hkind | |].
      * destruct (Hpart _ Hfrom_n) as [H|H]; [exact H | destruct H].
      * destruct (Hpart _ Hto_n) as [H|H]; [exact H | destruct H].
    + destruct (find (fun id0 => Nat.eqb (sb_in_degree ac (r0 :: rest) id0) 0)
                  (r0 :: rest)) as [peeled|] eqn:Hfind.
      * assert (Hpeel_in : In peeled (r0 :: rest))
          by exact (find_In _ _ _ Hfind).
        assert (Hpeel_deg : sb_in_degree ac (r0 :: rest) peeled = 0).
        { apply find_some in Hfind. apply Nat.eqb_eq. exact (proj2 Hfind). }
        apply IH; clear IH.
        -- exact Hacyc.
        -- exact (NoDup_filter _ _ Hnd_rem).
        -- apply NoDup_app; [exact Hnd_acc | |].
           ++ constructor; [exact (fun H => H) | constructor].
           ++ intros x Hx [Heq_px | []].
              rewrite Heq_px in Hpeel_in.
              exact (Hdisj x Hx Hpeel_in).
        -- intros x Hx Hx'.
           apply in_app_or in Hx. apply filter_remove_In in Hx'.
           destruct Hx as [Hxa | [Heq_px | []]].
           ++ exact (Hdisj x Hxa (proj1 Hx')).
           ++ exact (proj2 Hx' (eq_sym Heq_px)).
        -- intros x Hxn. destruct (Hpart x Hxn) as [Hxa | Hxr].
           ++ left. apply in_or_app. left. exact Hxa.
           ++ destruct (String.eqb x peeled) eqn:Exid.
              ** left. apply in_or_app. right.
                 apply String.eqb_eq in Exid. rewrite Exid. left. reflexivity.
              ** right. apply In_filter_remove; [exact Hxr |].
                 intro Heq. rewrite Heq in Exid.
                 rewrite String.eqb_refl in Exid. discriminate.
        -- assert (Hlt : length (filter (fun x => negb (String.eqb x peeled))
                            (r0 :: rest)) < length (r0 :: rest))
             by exact (filter_remove_length peeled (r0 :: rest) Hpeel_in Hnd_rem).
           apply Nat.lt_succ_r.
           exact (Nat.lt_le_trans _ _ _ Hlt Hfuel).
        -- intros x Hx. apply filter_remove_In in Hx.
           exact (Hnodes x (proj1 Hx)).
        -- intros l0 Hl0 Hk0 Hto0 Hfr0.
           apply in_app_or in Hto0.
           destruct Hto0 as [Hto_acc | [Hto_eq | []]].
           ++ apply filter_remove_In in Hfr0.
              exact (Hup l0 Hl0 Hk0 Hto_acc (proj1 Hfr0)).
           ++ apply filter_remove_In in Hfr0.
              destruct Hfr0 as [Hfr_rem _].
              assert (Hmem : mem_string l0.(link_from) (r0 :: rest) = false)
                by exact (sb_indeg_zero_no_parent ac (r0 :: rest) peeled l0
                           Hpeel_deg Hl0 Hk0 (eq_sym Hto_eq)).
              assert (Hin : In l0.(link_from) (r0 :: rest) -> False).
              { intro Hin. apply In_existsb in Hin.
                unfold mem_string in Hmem. rewrite Hin in Hmem. discriminate. }
              exact (Hin Hfr_rem).
        -- intros l0 Hl0 Hk0 Hfr0 Hto0.
           apply in_app_or in Hfr0. apply in_app_or in Hto0.
           destruct Hfr0 as [Hfr_a | [Hfr_eq | []]];
           destruct Hto0 as [Hto_a | [Hto_eq | []]].
           ++ destruct (Hord l0 Hl0 Hk0 Hfr_a Hto_a) as [i [j [Hi [Hj Hlt]]]].
              exists i, j. repeat split.
              ** exact (index_of_app_left _ _ [peeled] _ Hi).
              ** exact (index_of_app_left _ _ [peeled] _ Hj).
              ** exact Hlt.
           ++ destruct (index_of_In l0.(link_from) acc Hfr_a Hnd_acc) as [i Hi].
              assert (Hpeel_not_acc : ~ In peeled acc)
                by exact (fun H => Hdisj peeled H Hpeel_in).
              exists i, (length acc). repeat split.
              ** exact (index_of_app_left _ _ [peeled] _ Hi).
              ** replace (link_to l0) with peeled by exact Hto_eq.
                 assert (Hidx : index_of peeled [peeled] = Some 0)
                   by (simpl; rewrite String.eqb_refl; reflexivity).
                 pose proof (index_of_app_right peeled acc [peeled] 0
                   (not_In_index_of_None _ _ Hpeel_not_acc) Hidx) as Hres.
                 rewrite Nat.add_0_r in Hres. exact Hres.
              ** exact (Nat.lt_le_trans _ _ _ (index_of_lt _ _ _ Hi) (Nat.le_refl _)).
           ++ exfalso.
              rewrite Hfr_eq in Hpeel_in.
              exact (Hup l0 Hl0 Hk0 Hto_a Hpeel_in).
           ++ exfalso.
              apply (Hacyc peeled). apply R_Step.
              unfold supportedby_children. apply in_map_iff.
              exists l0. split; [exact (eq_sym Hto_eq) |].
              apply filter_In. split; [exact Hl0 |].
              rewrite (eq_sym Hfr_eq).
              simpl. rewrite Hk0. rewrite String.eqb_refl. reflexivity.
        -- exact Hlin.
        -- exact Hkind.
        -- exact Hfrom_n.
        -- exact Hto_n.
      * exfalso.
        destruct (find_zero_indeg ac (r0 :: rest) ltac:(discriminate)
                    Hnodes Hacyc) as [id' Hfind'].
        rewrite Hfind in Hfind'. discriminate.
Qed.

Theorem topo_sort_valid : forall ac,
    Acyclic ac ->
    NoDup (map node_id ac.(ac_nodes)) ->
    no_dangling_links ac ->
    verify_topo_order ac (topo_sort ac) = true.
Proof.
  intros ac Hacyc Hnd Hndl.
  unfold verify_topo_order.
  apply Bool.andb_true_iff. split.
  apply Bool.andb_true_iff. split.
  - apply forallb_forall. intros l Hlin.
    destruct l.(link_kind) eqn:Hk; [| reflexivity | reflexivity].
    assert (Hfrom : In l.(link_from) (map node_id ac.(ac_nodes))).
    { destruct (Hndl l Hlin) as [[nf Hf] _].
      apply in_map_iff. exists nf. split.
      - unfold find_node in Hf. apply find_some in Hf.
        apply String.eqb_eq. exact (proj2 Hf).
      - unfold find_node in Hf. apply find_some in Hf. exact (proj1 Hf). }
    assert (Hto : In l.(link_to) (map node_id ac.(ac_nodes))).
    { destruct (Hndl l Hlin) as [_ [nt Ht]].
      apply in_map_iff. exists nt. split.
      - unfold find_node in Ht. apply find_some in Ht.
        apply String.eqb_eq. exact (proj2 Ht).
      - unfold find_node in Ht. apply find_some in Ht. exact (proj1 Ht). }
    assert (Hfuel : length ac.(ac_nodes) >= length (map node_id ac.(ac_nodes)))
      by (rewrite length_map; apply Nat.le_refl).
    destruct (topo_sort_go_ordered ac (length ac.(ac_nodes))
                (map node_id ac.(ac_nodes)) []
                Hacyc Hnd (NoDup_nil _)
                (fun x Hx => match Hx with end)
                (fun x Hx => or_intror Hx)
                Hfuel
                (fun x Hx => Hx)
                (fun _ _ _ Hto0 => match Hto0 with end)
                (fun _ _ _ Hfr0 _ => match Hfr0 with end)
                l Hlin Hk Hfrom Hto)
      as [i [j [Hi [Hj Hlt]]]].
    unfold topo_sort. rewrite Hi, Hj. apply Nat.ltb_lt. exact Hlt.
  - apply forallb_forall. intros n Hn.
    apply In_existsb.
    exact (topo_sort_complete ac Hacyc Hnd n.(node_id)
             (in_map node_id _ n Hn)).
  - assert (Htsnd := topo_sort_nodup ac Hacyc Hnd).
    induction (topo_sort ac) as [|a ts IH].
    + reflexivity.
    + inversion Htsnd as [| ? ? Hna Hnd']; subst.
      simpl. apply Bool.andb_true_iff. split.
      * apply Bool.negb_true_iff.
        destruct (mem_string a ts) eqn:E; [| reflexivity].
        exfalso. exact (Hna (existsb_In a ts E)).
      * exact (IH Hnd').
Qed.
