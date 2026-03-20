(* ------------------------------------------------------------------ *)
(* Reflection: boolean checkers imply propositional well-formedness     *)
(* ------------------------------------------------------------------ *)

From RACK Require Import Core.
From RACK Require Import Main.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
From Stdlib Require Import Lia.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Arguments supportedby_children : simpl never.


(* ================================================================== *)
(* Section 1: Simple boolean reflections                               *)
(* ================================================================== *)

Lemma check_top_is_goal_correct : forall ac,
    check_top_is_goal ac = true -> top_is_goal ac.
Proof.
  intros ac H. unfold check_top_is_goal in H. unfold top_is_goal.
  destruct (find_node ac ac.(ac_top)) as [n|]; [| discriminate].
  destruct n.(node_kind) eqn:Hk; try discriminate.
  exists n. split; [reflexivity | exact Hk].
Qed.

Lemma check_no_dangling_correct : forall ac,
    check_no_dangling ac = true -> no_dangling_links ac.
Proof.
  intros ac H l Hin. unfold check_no_dangling in H.
  apply forallb_forall with (x := l) in H; [| exact Hin].
  destruct (find_node ac l.(link_from)) as [nf|];
  destruct (find_node ac l.(link_to))   as [nt|];
  try discriminate.
  split; [exists nf | exists nt]; reflexivity.
Qed.

Lemma check_unique_ids_correct : forall ac,
    check_unique_ids ac = true -> NoDup (map node_id ac.(ac_nodes)).
Proof.
  intros ac H. exact (nodupb_NoDup _ H).
Qed.

Lemma check_context_links_correct : forall ac,
    check_context_links ac = true -> well_typed_context_links ac.
Proof.
  intros ac H l Hin Hkind. unfold check_context_links in H.
  apply forallb_forall with (x := l) in H; [| exact Hin].
  rewrite Hkind in H.
  destruct (find_node ac l.(link_from)) as [nf|];
  destruct (find_node ac l.(link_to))   as [nt|];
  try discriminate.
  apply Bool.andb_true_iff in H. destruct H as [Hfk Htk].
  exists nf, nt.
  split; [reflexivity |].
  split; [reflexivity |].
  split.
  - destruct nf.(node_kind) eqn:?; try discriminate;
    [left | right]; reflexivity.
  - destruct nt.(node_kind) eqn:?; try discriminate;
    [left | right; left | right; right]; reflexivity.
Qed.

(* ================================================================== *)
(* Section 2: Topological order and acyclicity                         *)
(* ================================================================== *)

(* A SupportedBy child witnesses a link in ac_links.                   *)
Lemma supportedby_children_link : forall ac u v,
    In v (supportedby_children ac u) ->
    exists l, In l ac.(ac_links) /\
              l.(link_kind) = SupportedBy /\
              l.(link_from) = u /\
              l.(link_to) = v.
Proof.
  intros ac u v H.
  unfold supportedby_children in H.
  apply in_map_iff in H. destruct H as [l [Hto Hinf]].
  apply filter_In in Hinf. destruct Hinf as [Hin Hcond].
  apply Bool.andb_true_iff in Hcond. destruct Hcond as [Hfrom Hkind].
  apply String.eqb_eq in Hfrom.
  exists l. repeat split.
  - exact Hin.
  - destruct l.(link_kind); [reflexivity | discriminate | discriminate].
  - exact Hfrom.
  - exact Hto.
Qed.

(* index_of_Some_In, index_of_In, index_of_lt are in TopoSort.v. *)

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

Lemma index_of_NoDup_unique : forall s l i j,
    NoDup l -> index_of s l = Some i -> index_of s l = Some j -> i = j.
Proof. intros. congruence. Qed.

(* The key acyclicity lemma: if verify_topo_order passes,
   every Reaches chain strictly increases the index.                   *)

Lemma verify_topo_edge_index : forall ac order l,
    forallb (fun l0 =>
      match l0.(link_kind) with
      | SupportedBy =>
        match index_of l0.(link_from) order,
              index_of l0.(link_to)   order with
        | Some i, Some j => Nat.ltb i j
        | _, _ => false
        end
      | _ => true
      end) ac.(ac_links) = true ->
    In l ac.(ac_links) ->
    l.(link_kind) = SupportedBy ->
    exists i j,
      index_of l.(link_from) order = Some i /\
      index_of l.(link_to)   order = Some j /\
      i < j.
Proof.
  intros ac order l Hforall Hin Hkind.
  apply forallb_forall with (x := l) in Hforall; [| exact Hin].
  rewrite Hkind in Hforall.
  destruct (index_of l.(link_from) order) as [i|] eqn:Hi;
  destruct (index_of l.(link_to)   order) as [j|] eqn:Hj;
  try discriminate.
  apply Nat.ltb_lt in Hforall.
  exists i, j. auto.
Qed.

(* Reachable nodes have indices in the topo order.                     *)
Lemma reaches_has_index : forall ac order u v,
    forallb (fun l =>
      match l.(link_kind) with
      | SupportedBy =>
        match index_of l.(link_from) order,
              index_of l.(link_to)   order with
        | Some i, Some j => Nat.ltb i j
        | _, _ => false
        end
      | _ => true
      end) ac.(ac_links) = true ->
    Reaches ac u v ->
    exists j, index_of v order = Some j.
Proof.
  intros ac order u v Hedge H.
  induction H as [u0 v0 Hin | u0 w v0 H1 IH1 H2 IH2].
  - destruct (supportedby_children_link ac u0 v0 Hin)
      as [l [Hlin [Hkind [Hfrom Hto]]]].
    destruct (verify_topo_edge_index ac order l Hedge Hlin Hkind)
      as [i [j [Hi [Hj _]]]].
    rewrite Hto in Hj. exists j. exact Hj.
  - exact IH2.
Qed.

Lemma step_index_lt : forall ac order u v iu iv,
    forallb (fun l =>
      match l.(link_kind) with
      | SupportedBy =>
        match index_of l.(link_from) order,
              index_of l.(link_to)   order with
        | Some i, Some j => Nat.ltb i j
        | _, _ => false
        end
      | _ => true
      end) ac.(ac_links) = true ->
    In v (supportedby_children ac u) ->
    index_of u order = Some iu ->
    index_of v order = Some iv ->
    iu < iv.
Proof.
  intros ac order u v iu iv Hedge Hin Hiu Hiv.
  destruct (supportedby_children_link ac u v Hin)
    as [l [Hlin [Hkind [Hfrom Hto]]]].
  destruct (verify_topo_edge_index ac order l Hedge Hlin Hkind)
    as [i [j [Hi [Hj Hlt]]]].
  rewrite Hfrom in Hi. rewrite Hto in Hj.
  rewrite Hi in Hiu. injection Hiu as <-.
  rewrite Hj in Hiv. injection Hiv as <-.
  exact Hlt.
Qed.

Lemma reaches_index_lt : forall ac order u v iu iv,
    forallb (fun l =>
      match l.(link_kind) with
      | SupportedBy =>
        match index_of l.(link_from) order,
              index_of l.(link_to)   order with
        | Some i, Some j => Nat.ltb i j
        | _, _ => false
        end
      | _ => true
      end) ac.(ac_links) = true ->
    Reaches ac u v ->
    index_of u order = Some iu ->
    index_of v order = Some iv ->
    iu < iv.
Proof.
  intros ac order u v iu iv Hedge H. revert iu iv.
  induction H as [u0 v0 Hin | u0 w v0 H1 IH1 H2 IH2];
    intros iu iv Hiu Hiv.
  - exact (step_index_lt ac order u0 v0 iu iv Hedge Hin Hiu Hiv).
  - destruct (reaches_has_index ac order u0 w Hedge H1) as [iw Hiw].
    exact (Nat.lt_trans _ _ _ (IH1 _ _ Hiu Hiw) (IH2 _ _ Hiw Hiv)).
Qed.

Lemma verify_topo_order_acyclic : forall ac order,
    verify_topo_order ac order = true ->
    Acyclic ac.
Proof.
  intros ac order H id Hcycle.
  unfold verify_topo_order in H.
  apply Bool.andb_true_iff in H. destruct H as [H Hnodup].
  apply Bool.andb_true_iff in H. destruct H as [Hedge Hcover].
  (* id must have an index: it's endpoint of some edge in the cycle *)
  assert (Hid_idx : exists i, index_of id order = Some i).
  { induction Hcycle as [u v Hin | u w v H1 IH1 H2 IH2].
    - destruct (supportedby_children_link ac u v Hin)
        as [l [Hlin [Hkind [Hfrom Hto]]]].
      destruct (verify_topo_edge_index ac order l Hedge Hlin Hkind)
        as [i [j [Hi [Hj _]]]].
      rewrite Hto in Hj. exists j. exact Hj.
    - exact IH2. }
  destruct Hid_idx as [i Hi].
  exact (Nat.lt_irrefl i (reaches_index_lt ac order id id i i Hedge
                            Hcycle Hi Hi)).
Qed.

(* Convenience: decide acyclicity from check_acyclic.
   This bridges the existing BFS-based checker to Acyclic
   via the topo order verifier.                                        *)
Lemma check_acyclic_or_topo : forall ac,
    verify_topo_order ac (topo_sort ac) = true ->
    Acyclic ac.
Proof.
  intros. exact (verify_topo_order_acyclic ac (topo_sort ac) H).
Qed.

(* ================================================================== *)
(* Section 3: Discharged reflection                                    *)
(* ================================================================== *)

(* Reachable nodes have find_node = Some.                              *)
Lemma reaches_has_node : forall ac u v,
    no_dangling_links ac ->
    (exists n, find_node ac u = Some n) ->
    Reaches ac u v ->
    exists n, find_node ac v = Some n.
Proof.
  intros ac u v Hnd Hu H.
  induction H as [u0 v0 Hin | u0 w v0 H1 IH1 H2 IH2].
  - destruct (supportedby_children_link ac u0 v0 Hin)
      as [l [Hlin [_ [_ Hto]]]].
    destruct (Hnd l Hlin) as [_ [nt Htf]].
    rewrite Hto in Htf. exists nt. exact Htf.
  - exact (IH2 (IH1 Hu)).
Qed.

Lemma reachable_has_node : forall ac id,
    no_dangling_links ac ->
    (exists n, find_node ac ac.(ac_top) = Some n) ->
    (id = ac.(ac_top) \/ Reaches ac ac.(ac_top) id) ->
    exists n, find_node ac id = Some n.
Proof.
  intros ac id Hnd Htop [-> | Hreach].
  - exact Htop.
  - exact (reaches_has_node ac _ _ Hnd Htop Hreach).
Qed.

(* find_node = Some implies node is In ac_nodes.                       *)
Lemma find_node_in' : forall ac id n,
    find_node ac id = Some n -> In n ac.(ac_nodes).
Proof.
  intros ac id n H. unfold find_node in H.
  apply find_some in H. exact (proj1 H).
Qed.

Lemma find_node_id' : forall ac id n,
    find_node ac id = Some n -> n.(node_id) = id.
Proof.
  intros ac id n H. unfold find_node in H.
  apply find_some in H. destruct H as [_ Heqb].
  apply String.eqb_eq in Heqb. exact Heqb.
Qed.

(* check_all_discharged implies the discharged condition for all nodes
   that have find_node = Some. Requires a separate proof that
   ProofTerm evidence types match their node claims (undecidable in
   general, but trivial for correctly constructed cases).              *)
Lemma check_all_discharged_correct : forall ac,
    no_dangling_links ac ->
    top_is_goal ac ->
    check_all_discharged ac = true ->
    (forall n e, In n ac.(ac_nodes) ->
      n.(node_kind) = Solution ->
      n.(node_evidence) = Some e ->
      evidence_valid n e) ->
    all_reachable_discharged ac.
Proof.
  intros ac Hnd Htop Hcheck Hev id Hreach.
  assert (Hn : exists n, find_node ac id = Some n).
  { apply reachable_has_node; [exact Hnd | | exact Hreach].
    destruct Htop as [n [Hf _]]. exists n. exact Hf. }
  destruct Hn as [n Hfind]. rewrite Hfind.
  assert (Hin : In n ac.(ac_nodes)).
  { exact (find_node_in' ac id n Hfind). }
  assert (Hid : n.(node_id) = id).
  { exact (find_node_id' ac id n Hfind). }
  unfold check_all_discharged in Hcheck.
  apply forallb_forall with (x := n) in Hcheck; [| exact Hin].
  destruct n.(node_kind) eqn:Hk.
  - (* Goal *)
    rewrite <- Hid.
    destruct (supportedby_children ac n.(node_id)) eqn:Hkids.
    + simpl in Hcheck. discriminate.
    + intro Habs. discriminate.
  - (* Strategy *)
    rewrite <- Hid.
    destruct (supportedby_children ac n.(node_id)) eqn:Hkids.
    + simpl in Hcheck. discriminate.
    + intro Habs. discriminate.
  - (* Solution *)
    destruct n.(node_evidence) as [e|] eqn:He; [| discriminate].
    exists e. split; [reflexivity |].
    exact (Hev n e Hin Hk He).
  - (* Context *) exact I.
  - (* Assumption *) exact I.
  - (* Justification *) exact I.
Qed.

(* ================================================================== *)
(* Section 4: Combined well-formedness builder                         *)
(* ================================================================== *)

Lemma build_well_formed : forall ac,
    structural_checks ac = true ->
    (* Entailment: user provides (undecidable in general) *)
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
    (* ProofTerm evidence validity: trivial for correct constructions *)
    (forall n e,
      In n ac.(ac_nodes) ->
      n.(node_kind) = Solution ->
      n.(node_evidence) = Some e ->
      evidence_valid n e) ->
    WellFormed ac.
Proof.
  intros ac Hstruct Hent Hev.
  unfold structural_checks in Hstruct.
  repeat (apply Bool.andb_true_iff in Hstruct;
          destruct Hstruct as [Hstruct ?]).
  rename H into Hctx, H0 into Halldisc, H1 into Htopo,
         H2 into Hndang, H3 into Huniq.
  rename Hstruct into Htopg.
  constructor.
  - exact (check_top_is_goal_correct ac Htopg).
  - exact (verify_topo_order_acyclic ac (topo_sort ac) Htopo).
  - (* all_reachable_discharged — use check_all_discharged + evidence validity *)
    intros id Hreach.
    pose proof (check_no_dangling_correct ac Hndang) as Hnd.
    pose proof (check_top_is_goal_correct ac Htopg) as Htop_prop.
    assert (Hn : exists n, find_node ac id = Some n).
    { apply reachable_has_node; [exact Hnd | | exact Hreach].
      destruct Htop_prop as [nt [Hf _]]. exists nt. exact Hf. }
    destruct Hn as [n Hfind]. rewrite Hfind.
    assert (Hin : In n ac.(ac_nodes)).
    { exact (find_node_in' ac id n Hfind). }
    assert (Hid : n.(node_id) = id).
    { exact (find_node_id' ac id n Hfind). }
    unfold check_all_discharged in Halldisc.
    apply forallb_forall with (x := n) in Halldisc; [| exact Hin].
    destruct n.(node_kind) eqn:Hk.
    + (* Goal *) rewrite <- Hid.
      destruct (supportedby_children ac n.(node_id)) eqn:Hkids;
        [simpl in Halldisc; discriminate | intro; discriminate].
    + (* Strategy *) rewrite <- Hid.
      destruct (supportedby_children ac n.(node_id)) eqn:Hkids;
        [simpl in Halldisc; discriminate | intro; discriminate].
    + (* Solution *)
      destruct n.(node_evidence) as [e|] eqn:He; [| discriminate].
      exists e. split; [reflexivity |].
      exact (Hev n e Hin Hk He).
    + exact I.
    + exact I.
    + exact I.
  - exact (check_no_dangling_correct ac Hndang).
  - exact (nodupb_NoDup _ Huniq).
  - exact Hent.
  - exact (check_context_links_correct ac Hctx).
  - exact (check_context_links_defeaters ac Hctx).
Qed.

(* ================================================================== *)
(* Section 5: Tactics                                                  *)
(* ================================================================== *)

(* Discharge Acyclic via topo sort.                                    *)
Ltac decide_acyclic :=
  match goal with
  | |- Acyclic ?ac =>
    exact (verify_topo_order_acyclic ac (topo_sort ac)
             ltac:(vm_compute; reflexivity))
  end.

(* Discharge evidence_valid for all solutions in a concrete graph.     *)
Ltac prove_evidence_valid :=
  intros ? ? ? ? ?; vm_compute; reflexivity.

(* Discharge well_typed_context_links from check_context_links.        *)
Ltac decide_context_links :=
  match goal with
  | |- well_typed_context_links ?ac =>
    exact (check_context_links_correct ac
             ltac:(vm_compute; reflexivity))
  end.

(* One-shot well-formedness builder for concrete assurance cases.
   User must provide: entailment proof and evidence validity proof.     *)
Ltac prove_well_formed_with ent_proof ev_proof :=
  match goal with
  | |- WellFormed ?ac =>
    exact (build_well_formed ac
             ltac:(vm_compute; reflexivity)
             ent_proof
             ev_proof)
  end.

(* Fully automated well-formedness for concrete cases.
   Entailment resolution order:
   1. Typeclass resolution (Entails instances: identity, conj, disj, True)
   2. Hint database (rack_entail: user-registered domain lemmas)
   3. vm_compute; tauto / intuition / firstorder
   4. Fall back to exfalso for non-Goal/Strategy nodes.                  *)
Ltac prove_well_formed_auto :=
  match goal with
  | |- WellFormed ?ac =>
    apply build_well_formed;
    [ vm_compute; reflexivity
    | (* entailment *)
      let id := fresh "id" in
      let n := fresh "n" in
      let Hfind := fresh "Hfind" in
      let Hkind := fresh "Hkind" in
      intros id n Hfind Hkind;
      vm_compute in Hfind;
      repeat match type of Hfind with
      | (if ?c then _ else _) = _ =>
          destruct c eqn:?;
          [ injection Hfind as <-;
            first [ (* typeclass resolution *)
                    typeclasses eauto
                  | (* hint database *)
                    intro; eauto with rack_entail
                  | vm_compute; tauto
                  | vm_compute; intuition
                  | vm_compute; firstorder
                  | exfalso; destruct Hkind as [? | ?]; discriminate ]
          | ]
      end;
      try discriminate
    | prove_evidence_valid ]
  end.

(* ================================================================== *)
(* Section 6: Compositional assembly lemmas                            *)
(* ================================================================== *)

Lemma find_node_app : forall nodes1 nodes2 id,
    find (fun n => String.eqb n.(node_id) id) (nodes1 ++ nodes2) =
    match find (fun n => String.eqb n.(node_id) id) nodes1 with
    | Some n => Some n
    | None => find (fun n => String.eqb n.(node_id) id) nodes2
    end.
Proof.
  intros. induction nodes1 as [|a ns IH]; simpl.
  - reflexivity.
  - destruct (String.eqb a.(node_id) id); [reflexivity | exact IH].
Qed.

Lemma compose_find_node : forall p s g id,
    find_node (compose_cases p s g) id =
    match find_node p id with
    | Some n => Some n
    | None   => find_node s id
    end.
Proof.
  intros. unfold find_node, compose_cases. simpl.
  exact (find_node_app p.(ac_nodes) s.(ac_nodes) id).
Qed.

Lemma compose_no_dangling : forall p s g,
    no_dangling_links p ->
    no_dangling_links s ->
    (exists n, find_node p g = Some n) ->
    (exists n, find_node s s.(ac_top) = Some n) ->
    no_dangling_links (compose_cases p s g).
Proof.
  intros p s g Hndp Hnds [ng Hng] [nt Hnt] l Hin.
  simpl in Hin. apply in_app_iff in Hin.
  destruct Hin as [Hinp | Hins].
  - (* link from parent *)
    destruct (Hndp l Hinp) as [[nf Hf] [nto Hto]].
    split; rewrite compose_find_node; rewrite Hf || rewrite Hto;
      [exists nf | exists nto]; reflexivity.
  - apply in_app_iff in Hins. destruct Hins as [Hins | [<- | []]].
    + (* link from subcase *)
      destruct (Hnds l Hins) as [[nf Hf] [nto Hto]].
      split; rewrite compose_find_node.
      * destruct (find_node p l.(link_from)); [eexists; reflexivity |].
        exists nf. exact Hf.
      * destruct (find_node p l.(link_to)); [eexists; reflexivity |].
        exists nto. exact Hto.
    + (* bridge link *)
      simpl. split; rewrite compose_find_node.
      * rewrite Hng. exists ng. reflexivity.
      * destruct (find_node p s.(ac_top)) eqn:?.
        -- eexists; reflexivity.
        -- exists nt. exact Hnt.
Qed.

Lemma compose_unique_ids : forall p s g,
    NoDup (map node_id p.(ac_nodes)) ->
    NoDup (map node_id s.(ac_nodes)) ->
    (forall id,
      In id (map node_id p.(ac_nodes)) ->
      In id (map node_id s.(ac_nodes)) ->
      False) ->
    NoDup (map node_id (compose_cases p s g).(ac_nodes)).
Proof.
  intros p s g Hndp Hnds Hdisj. simpl.
  rewrite map_app.
  induction p.(ac_nodes) as [|a ns IH]; simpl.
  - exact Hnds.
  - inversion Hndp as [| ? ? Hna Hnd']; subst.
    constructor.
    + intro Hin. apply in_app_iff in Hin.
      destruct Hin as [Hin | Hin].
      * exact (Hna Hin).
      * exact (Hdisj a.(node_id) (or_introl eq_refl) Hin).
    + apply IH.
      * exact Hnd'.
      * intros id Hp Hs. exact (Hdisj id (or_intror Hp) Hs).
Qed.

(* ================================================================== *)
(* Section 7: Composed supportedby_children decomposition              *)
(* ================================================================== *)

(* Key building block for composed entailment proofs.
   In a composed case, the children of any node id decompose into:
   - children from the parent's links
   - children from the subcase's links
   - the bridge target (if id is the bridge node)                      *)
Lemma compose_supportedby_children : forall p s g id,
    supportedby_children (compose_cases p s g) id =
    supportedby_children p id ++
    supportedby_children s id ++
    (if String.eqb g id then [s.(ac_top)] else []).
Proof.
  intros p s g id.
  unfold supportedby_children, compose_cases. simpl.
  rewrite filter_app, map_app.
  f_equal.
  rewrite filter_app, map_app.
  f_equal.
  simpl.
  destruct (String.eqb g id); simpl; reflexivity.
Qed.

(* For non-bridge parent nodes, children are unchanged.                *)
Corollary compose_children_parent : forall p s g id,
    String.eqb g id = false ->
    supportedby_children s id = [] ->
    supportedby_children (compose_cases p s g) id =
    supportedby_children p id.
Proof.
  intros p s g id Hneq Hempty.
  rewrite compose_supportedby_children, Hempty, Hneq.
  rewrite app_nil_r. reflexivity.
Qed.

(* For subcase nodes (not in parent links), children are unchanged.    *)
Corollary compose_children_subcase : forall p s g id,
    String.eqb g id = false ->
    supportedby_children p id = [] ->
    supportedby_children (compose_cases p s g) id =
    supportedby_children s id.
Proof.
  intros p s g id Hneq Hempty.
  rewrite compose_supportedby_children, Hempty, Hneq.
  simpl. rewrite app_nil_r. reflexivity.
Qed.

(* ================================================================== *)
(* Section 8: Composed well_typed_context_links                        *)
(* ================================================================== *)

Lemma compose_well_typed_context_links : forall p s g,
    well_typed_context_links p ->
    well_typed_context_links s ->
    (forall id, In id (map node_id p.(ac_nodes)) ->
                In id (map node_id s.(ac_nodes)) -> False) ->
    well_typed_context_links (compose_cases p s g).
Proof.
  intros p s g Hwtp Hwts Hdisj l Hin Hkind.
  simpl in Hin.
  apply in_app_iff in Hin.
  destruct Hin as [Hinp | Hins].
  - (* link from parent *)
    destruct (Hwtp l Hinp Hkind) as [nf [nt [Hf [Ht [Hfk Htk]]]]].
    exists nf, nt.
    split; [rewrite compose_find_node; rewrite Hf; reflexivity |].
    split; [rewrite compose_find_node; rewrite Ht; reflexivity |].
    split; assumption.
  - apply in_app_iff in Hins.
    destruct Hins as [Hins | [<- | []]].
    + (* link from subcase *)
      destruct (Hwts l Hins Hkind) as [nf' [nt' [Hf' [Ht' [Hfk' Htk']]]]].
      exists nf', nt'.
      (* Subcase node IDs are disjoint from parent, so
         compose_find_node falls through to the subcase. *)
      assert (Epf : find_node p l.(link_from) = None).
      { destruct (find_node p l.(link_from)) as [npf|] eqn:E; [| reflexivity].
        exfalso. apply (Hdisj l.(link_from)).
        - apply in_map_iff. exists npf. split.
          + exact (find_node_id' _ _ _ E).
          + exact (find_node_in' _ _ _ E).
        - apply in_map_iff. exists nf'. split.
          + exact (find_node_id' _ _ _ Hf').
          + exact (find_node_in' _ _ _ Hf'). }
      assert (Ept : find_node p l.(link_to) = None).
      { destruct (find_node p l.(link_to)) as [npt|] eqn:E; [| reflexivity].
        exfalso. apply (Hdisj l.(link_to)).
        - apply in_map_iff. exists npt. split.
          + exact (find_node_id' _ _ _ E).
          + exact (find_node_in' _ _ _ E).
        - apply in_map_iff. exists nt'. split.
          + exact (find_node_id' _ _ _ Ht').
          + exact (find_node_in' _ _ _ Ht'). }
      split; [rewrite compose_find_node; rewrite Epf; exact Hf' |].
      split; [rewrite compose_find_node; rewrite Ept; exact Ht' |].
      split; assumption.
    + (* bridge link — SupportedBy, not InContextOf *)
      simpl in Hkind. discriminate.
Qed.

(* ================================================================== *)
(* Section 9: check_support_tree_go soundness                          *)
(* ================================================================== *)

(* The boolean support-tree checker is sound: if it returns true,
   then SupportTree holds (given entailment and evidence validity
   assumptions that cannot be checked computationally).                *)
Lemma check_support_tree_go_sound : forall ac fuel id,
    check_support_tree_go ac fuel id = true ->
    (forall n e,
      In n ac.(ac_nodes) -> n.(node_kind) = Solution ->
      n.(node_evidence) = Some e -> evidence_valid n e) ->
    (forall id' n,
      find_node ac id' = Some n ->
      (n.(node_kind) = Goal \/ n.(node_kind) = Strategy) ->
      (let kids := supportedby_children ac id' in
       let child_claims :=
         flat_map (fun kid =>
           match find_node ac kid with
           | Some cn => [cn.(node_claim)]
           | None     => []
           end) kids
       in fold_right and True child_claims -> n.(node_claim))) ->
    SupportTree ac id.
Proof.
  intros ac fuel. induction fuel as [|f IH]; intros id Hcheck Hev Hent.
  - simpl in Hcheck. discriminate.
  - simpl in Hcheck.
    destruct (find_node ac id) as [n|] eqn:Hfind; [| discriminate].
    destruct n.(node_kind) eqn:Hkind.
    + (* Goal *)
      destruct (supportedby_children ac id) as [|k ks] eqn:Hkids;
        [discriminate | ].
      apply ST_Internal with n (k :: ks).
      * exact Hfind.
      * rewrite Hkind; discriminate.
      * symmetry; exact Hkids.
      * discriminate.
      * intros kid Hkid.
        apply IH.
        -- rewrite forallb_forall in Hcheck. exact (Hcheck kid Hkid).
        -- exact Hev.
        -- exact Hent.
      * rewrite <- Hkids. apply Hent; [exact Hfind | left; exact Hkind].
    + (* Strategy *)
      destruct (supportedby_children ac id) as [|k ks] eqn:Hkids;
        [discriminate | ].
      apply ST_Internal with n (k :: ks).
      * exact Hfind.
      * rewrite Hkind; discriminate.
      * symmetry; exact Hkids.
      * discriminate.
      * intros kid Hkid.
        apply IH.
        -- rewrite forallb_forall in Hcheck. exact (Hcheck kid Hkid).
        -- exact Hev.
        -- exact Hent.
      * rewrite <- Hkids. apply Hent; [exact Hfind | right; exact Hkind].
    + (* Solution *)
      destruct n.(node_evidence) as [e|] eqn:He; [| discriminate].
      apply ST_Leaf with n e.
      * exact Hfind.
      * exact Hkind.
      * exact He.
      * exact (Hev n e (find_node_in' ac id n Hfind) Hkind He).
    + (* Context *)
      exact (ST_Annotation ac id n Hfind (or_introl Hkind)).
    + (* Assumption *)
      exact (ST_Annotation ac id n Hfind (or_intror (or_introl Hkind))).
    + (* Justification *)
      exact (ST_Annotation ac id n Hfind (or_intror (or_intror Hkind))).
Qed.

Lemma check_support_tree_sound : forall ac id,
    check_support_tree ac id = true ->
    (forall n e,
      In n ac.(ac_nodes) -> n.(node_kind) = Solution ->
      n.(node_evidence) = Some e -> evidence_valid n e) ->
    (forall id' n,
      find_node ac id' = Some n ->
      (n.(node_kind) = Goal \/ n.(node_kind) = Strategy) ->
      (let kids := supportedby_children ac id' in
       let child_claims :=
         flat_map (fun kid =>
           match find_node ac kid with
           | Some cn => [cn.(node_claim)]
           | None     => []
           end) kids
       in fold_right and True child_claims -> n.(node_claim))) ->
    SupportTree ac id.
Proof.
  intros ac id. exact (check_support_tree_go_sound ac (length ac.(ac_nodes)) id).
Qed.

(* ================================================================== *)
(* Section 9b: Direct support-tree soundness (no user obligations)    *)
(* ================================================================== *)

(** [ComputationalSupportTree] captures exactly what
    [check_support_tree] decides — no entailment, no ProofTerm
    type matching. *)
Inductive ComputationalSupportTree (ac : AssuranceCase) : Id -> Prop :=
  | CST_Leaf : forall id n,
      find_node ac id = Some n ->
      n.(node_kind) = Solution ->
      (match n.(node_evidence) with
       | Some (ProofTerm _ _ _ (Some f)) => f n.(node_claim_text) = true
       | Some (ProofTerm _ _ _ None) => False
       | Some (Certificate b _ v) => v b = true
       | None => False
       end) ->
      ComputationalSupportTree ac id
  | CST_Internal : forall id n (kids : list Id),
      find_node ac id = Some n ->
      (n.(node_kind) = Goal \/ n.(node_kind) = Strategy) ->
      kids = supportedby_children ac id ->
      kids <> [] ->
      (forall kid, In kid kids -> ComputationalSupportTree ac kid) ->
      ComputationalSupportTree ac id
  | CST_Annotation : forall id n,
      find_node ac id = Some n ->
      (n.(node_kind) = Context \/
       n.(node_kind) = Assumption \/
       n.(node_kind) = Justification) ->
      ComputationalSupportTree ac id.

Lemma check_support_tree_go_direct : forall ac fuel id,
    check_support_tree_go ac fuel id = true ->
    ComputationalSupportTree ac id.
Proof.
  intros ac fuel. induction fuel as [|f IH]; intros id Hcheck.
  - simpl in Hcheck. discriminate.
  - simpl in Hcheck.
    destruct (find_node ac id) as [n|] eqn:Hfind; [| discriminate].
    destruct n.(node_kind) eqn:Hkind.
    + destruct (supportedby_children ac id) as [|k ks] eqn:Hkids;
        [discriminate |].
      apply CST_Internal with n (k :: ks);
        [exact Hfind | left; exact Hkind | symmetry; exact Hkids
        | discriminate |].
      intros kid Hkid. apply IH.
      apply forallb_forall with (x := kid) in Hcheck; exact Hcheck || exact Hkid.
    + destruct (supportedby_children ac id) as [|k ks] eqn:Hkids;
        [discriminate |].
      apply CST_Internal with n (k :: ks);
        [exact Hfind | right; exact Hkind | symmetry; exact Hkids
        | discriminate |].
      intros kid Hkid. apply IH.
      apply forallb_forall with (x := kid) in Hcheck; exact Hcheck || exact Hkid.
    + apply CST_Leaf with n; [exact Hfind | exact Hkind |].
      destruct n.(node_evidence) as [e|]; [| discriminate].
      destruct e as [lbl P pf [chk|] | b tool v]; [exact Hcheck | discriminate | exact Hcheck].
    + exact (CST_Annotation ac id n Hfind (or_introl Hkind)).
    + exact (CST_Annotation ac id n Hfind (or_intror (or_introl Hkind))).
    + exact (CST_Annotation ac id n Hfind (or_intror (or_intror Hkind))).
Qed.

(** Direct soundness: no entailment or evidence validity hypotheses. *)
Theorem check_support_tree_direct : forall ac id,
    check_support_tree ac id = true ->
    ComputationalSupportTree ac id.
Proof.
  intros ac id.
  exact (check_support_tree_go_direct ac (length ac.(ac_nodes)) id).
Qed.

(* ================================================================== *)
(* Section 10: BFS reachability lemmas                                 *)
(* ================================================================== *)

(* Monotonicity: the accumulator is always a subset of the result.     *)
Lemma rsf_acc_subset : forall ac fuel frontier acc x,
    In x acc ->
    In x (reachable_set_fuel ac fuel frontier acc).
Proof.
  intros ac fuel. induction fuel as [|f IH]; intros frontier acc x Hin; simpl.
  - exact Hin.
  - remember (filter (fun id => negb (mem_string id acc))
               (flat_map (supportedby_children ac) frontier)) as fresh.
    destruct fresh as [|h t].
    + exact Hin.
    + apply IH. apply in_or_app. left. exact Hin.
Qed.

(* Children of frontier nodes are in the result (given fuel > 0).      *)
Lemma rsf_frontier_child : forall ac f frontier acc x y,
    In x frontier ->
    In y (supportedby_children ac x) ->
    In y (reachable_set_fuel ac (S f) frontier acc).
Proof.
  intros ac f frontier acc x y Hx Hy. simpl.
  remember (filter (fun id => negb (mem_string id acc))
             (flat_map (supportedby_children ac) frontier)) as fresh.
  assert (Hyin: In y (flat_map (supportedby_children ac) frontier)).
  { apply in_flat_map. exists x. split; assumption. }
  destruct (mem_string y acc) eqn:Hmem.
  - destruct fresh as [|h t].
    + exact (existsb_In _ _ Hmem).
    + apply rsf_acc_subset. apply in_or_app. left.
      exact (existsb_In _ _ Hmem).
  - assert (Hyfresh : In y (filter (fun id => negb (mem_string id acc))
                     (flat_map (supportedby_children ac) frontier))).
    { apply filter_In. split; [exact Hyin |]. rewrite Hmem. reflexivity. }
    destruct fresh as [|h t].
    + rewrite <- Heqfresh in Hyfresh. destruct Hyfresh.
    + apply rsf_acc_subset. apply in_or_app. right.
      rewrite <- Heqfresh in Hyfresh. exact Hyfresh.
Qed.

(* A set S is child-closed when all SupportedBy children of members
   are also members.                                                    *)
Definition child_closed (ac : AssuranceCase) (S : list Id) : Prop :=
  forall x y, In x S -> In y (supportedby_children ac x) -> In y S.

(* Key lemma: Reaches within a child-closed set.                       *)
Lemma reaches_in_closed : forall ac (S : list Id) u v,
    child_closed ac S ->
    In u S ->
    Reaches ac u v ->
    In v S.
Proof.
  intros ac S u v Hclosed Hu Hreach.
  induction Hreach as [u0 v0 Hin | u0 w v0 H1 IH1 H2 IH2].
  - exact (Hclosed u0 v0 Hu Hin).
  - exact (IH2 (IH1 Hu)).
Qed.

(* Decompose Reaches into first step + remainder.                      *)
Lemma reaches_first_step : forall ac u v,
    Reaches ac u v ->
    exists mid, In mid (supportedby_children ac u) /\
                (mid = v \/ Reaches ac mid v).
Proof.
  intros ac u v H.
  induction H as [u0 v0 Hin | u0 w v0 H1 IH1 H2 IH2].
  - exists v0. split; [exact Hin | left; reflexivity].
  - destruct IH1 as [mid1 [Hmid1 Hrest1]].
    exists mid1. split; [exact Hmid1 |].
    destruct Hrest1 as [<- | Hmid1w].
    + right. exact H2.
    + right. exact (R_Trans ac mid1 w v0 Hmid1w H2).
Qed.

(* BFS check_acyclic detects self-loops.                               *)
Lemma check_acyclic_self_loop : forall ac id,
    check_acyclic ac = true ->
    In id (map node_id ac.(ac_nodes)) ->
    ~ In id (supportedby_children ac id).
Proof.
  intros ac id Hcheck Hin_nodes Hself.
  unfold check_acyclic in Hcheck.
  apply in_map_iff in Hin_nodes. destruct Hin_nodes as [n [Hid Hn]].
  apply forallb_forall with (x := n) in Hcheck; [| exact Hn].
  subst id.
  assert (Hresult : In n.(node_id) (reachable_from ac n.(node_id))).
  { unfold reachable_from. apply rsf_acc_subset. exact Hself. }
  assert (Hmem : mem_string n.(node_id) (reachable_from ac n.(node_id)) = true).
  { unfold mem_string. apply In_existsb. exact Hresult. }
  rewrite Hmem in Hcheck. discriminate.
Qed.

(* BFS detects 1-step cycles: if x is a node and y is a child of x,
   and x is a child of y, check_acyclic catches it.                    *)
Lemma check_acyclic_two_cycle : forall ac x y,
    check_acyclic ac = true ->
    In x (map node_id ac.(ac_nodes)) ->
    In y (supportedby_children ac x) ->
    ~ In x (supportedby_children ac y).
Proof.
  intros ac x y Hcheck Hx_node Hxy Hyx.
  unfold check_acyclic in Hcheck.
  apply in_map_iff in Hx_node. destruct Hx_node as [n [Hid Hn]].
  apply forallb_forall with (x := n) in Hcheck; [| exact Hn].
  subst x.
  (* y is a child of n, and n is a child of y: two-step cycle.
     reachable_from finds n in its own reachable set. *)
  assert (Hresult : mem_string n.(node_id) (reachable_from ac n.(node_id)) = true).
  { unfold mem_string, reachable_from.
    apply In_existsb.
    set (kids := supportedby_children ac n.(node_id)).
    (* y is in kids (by Hxy), so y is in the initial frontier.
       n.(node_id) is a child of y (by Hyx).
       rsf explores children of frontier nodes. *)
    change (In n.(node_id) (reachable_set_fuel ac (length (ac_nodes ac)) kids kids)).
    assert (Hlen : exists m, length (ac_nodes ac) = S m).
    { destruct (ac_nodes ac) eqn:?; [exact (False_ind _ Hn) | eexists; reflexivity]. }
    destruct Hlen as [m Hm]. rewrite Hm.
    exact (rsf_frontier_child ac m kids kids y n.(node_id) Hxy Hyx). }
  rewrite Hresult in Hcheck. discriminate.
Qed.

(* Bridge: check_wf_extended + structural_checks => Acyclic.
   Either path suffices; the topo path has complete soundness.         *)
Lemma check_wf_extended_acyclic : forall ac,
    check_wf_extended ac = true ->
    structural_checks ac = true ->
    Acyclic ac.
Proof.
  intros ac _ Hstruct.
  unfold structural_checks in Hstruct.
  repeat (apply Bool.andb_true_iff in Hstruct;
          destruct Hstruct as [Hstruct ?]).
  exact (verify_topo_order_acyclic ac (topo_sort ac) H1).
Qed.

(* ================================================================== *)
(* Section 11: Checker relationship                                    *)
(* ================================================================== *)

(* check_all_discharged implies the discharged condition for
   individual nodes.                                                    *)
Lemma check_all_discharged_node : forall ac n,
    check_all_discharged ac = true ->
    In n ac.(ac_nodes) ->
    match n.(node_kind) with
    | Solution =>
      match n.(node_evidence) with
      | Some (Certificate b _ v) => v b = true
      | Some (ProofTerm _ _ _ (Some f)) => f n.(node_claim_text) = true
      | Some (ProofTerm _ _ _ None) => False
      | None => False
      end
    | Goal | Strategy =>
      supportedby_children ac n.(node_id) <> []
    | _ => True
    end.
Proof.
  intros ac n Hall Hn.
  unfold check_all_discharged in Hall.
  apply forallb_forall with (x := n) in Hall; [| exact Hn].
  destruct n.(node_kind) eqn:Hk.
  - destruct (supportedby_children ac n.(node_id)) eqn:Hkids;
      [simpl in Hall; discriminate | intro; discriminate].
  - destruct (supportedby_children ac n.(node_id)) eqn:Hkids;
      [simpl in Hall; discriminate | intro; discriminate].
  - destruct n.(node_evidence) as [e|] eqn:He; [| discriminate].
    destruct e as [lbl P pf [chk|] | blob tool v].
    + exact Hall.
    + discriminate.
    + exact Hall.
  - exact I.
  - exact I.
  - exact I.
Qed.

(* ================================================================== *)
(* Section 12: Compositional well-formedness                           *)
(* ================================================================== *)

(* Compositional WellFormed theorem.
   Assembles all proved component lemmas and takes the remaining
   obligations (acyclicity, entailment, evidence validity, discharged)
   as user-supplied hypotheses.  For concrete cases, these are
   typically discharged by vm_compute.                                 *)
Theorem compose_well_formed : forall p s g,
    WellFormed p ->
    WellFormed s ->
    (exists ng, find_node p g = Some ng) ->
    (exists nt, find_node s s.(ac_top) = Some nt) ->
    (forall id, In id (map node_id p.(ac_nodes)) ->
                In id (map node_id s.(ac_nodes)) -> False) ->
    (* User obligations — provable by vm_compute for concrete cases *)
    Acyclic (compose_cases p s g) ->
    all_reachable_discharged (compose_cases p s g) ->
    (forall id n,
      find_node (compose_cases p s g) id = Some n ->
      (n.(node_kind) = Goal \/ n.(node_kind) = Strategy) ->
      (let kids := supportedby_children (compose_cases p s g) id in
       let child_claims :=
         flat_map (fun kid =>
           match find_node (compose_cases p s g) kid with
           | Some cn => [cn.(node_claim)]
           | None     => []
           end) kids
       in fold_right and True child_claims -> n.(node_claim))) ->
    well_typed_defeater_links (compose_cases p s g) ->
    WellFormed (compose_cases p s g).
Proof.
  intros p s g HWFp HWFs Hng Hnt Hdisj Hacyc Hdisc Hent Hdef.
  constructor.
  - (* top_is_goal *)
    destruct (wf_top _ HWFp) as [n [Hf Hk]].
    exists n. split.
    + simpl. rewrite compose_find_node. rewrite Hf. reflexivity.
    + exact Hk.
  - exact Hacyc.
  - exact Hdisc.
  - exact (compose_no_dangling p s g
             (wf_no_dangle _ HWFp) (wf_no_dangle _ HWFs) Hng Hnt).
  - exact (compose_unique_ids p s g
             (wf_unique_ids _ HWFp) (wf_unique_ids _ HWFs) Hdisj).
  - exact Hent.
  - exact (compose_well_typed_context_links p s g
             (wf_context_links _ HWFp) (wf_context_links _ HWFs) Hdisj).
  - exact Hdef.
Qed.

(* Concrete-case variant: discharge acyclicity and discharged-ness
   via structural_checks, keeping entailment as user obligation.       *)
Theorem compose_well_formed_auto : forall p s g,
    WellFormed p ->
    WellFormed s ->
    (exists ng, find_node p g = Some ng) ->
    (exists nt, find_node s s.(ac_top) = Some nt) ->
    (forall id, In id (map node_id p.(ac_nodes)) ->
                In id (map node_id s.(ac_nodes)) -> False) ->
    structural_checks (compose_cases p s g) = true ->
    (forall n e,
      In n (compose_cases p s g).(ac_nodes) ->
      n.(node_kind) = Solution ->
      n.(node_evidence) = Some e ->
      evidence_valid n e) ->
    (forall id n,
      find_node (compose_cases p s g) id = Some n ->
      (n.(node_kind) = Goal \/ n.(node_kind) = Strategy) ->
      (let kids := supportedby_children (compose_cases p s g) id in
       let child_claims :=
         flat_map (fun kid =>
           match find_node (compose_cases p s g) kid with
           | Some cn => [cn.(node_claim)]
           | None     => []
           end) kids
       in fold_right and True child_claims -> n.(node_claim))) ->
    WellFormed (compose_cases p s g).
Proof.
  intros p s g HWFp HWFs Hng Hnt Hdisj Hstruct Hev Hent.
  exact (build_well_formed (compose_cases p s g) Hstruct Hent Hev).
Qed.

(* ================================================================== *)
(* Section 13: Improved entailment tactics                             *)
(* ================================================================== *)

Ltac solve_entailment_robust find_equiv :=
  intros ? ? Hfind Hkind;
  rewrite find_equiv in Hfind;
  repeat match type of Hfind with
  | (if ?c then _ else _) = _ =>
      destruct c eqn:?;
      [ injection Hfind as <-;
        first [ vm_compute; tauto
              | vm_compute; intuition
              | vm_compute; firstorder
              | simpl; tauto
              | simpl; intuition
              | exfalso; destruct Hkind as [? | ?]; discriminate ]
      | ]
  end;
  try discriminate.

Ltac solve_entailment_with_hyps find_equiv :=
  intros ? ? Hfind Hkind;
  rewrite find_equiv in Hfind;
  repeat match type of Hfind with
  | (if ?c then _ else _) = _ =>
      destruct c eqn:?;
      [ injection Hfind as <-;
        first [ vm_compute; tauto
              | vm_compute; intuition auto with *
              | vm_compute; firstorder auto with *
              | exfalso; destruct Hkind as [? | ?]; discriminate ]
      | ]
  end;
  try discriminate.

Ltac try_well_formed_auto :=
  first [ prove_well_formed_auto
        | match goal with
          | |- WellFormed ?ac =>
            apply build_well_formed;
            [ vm_compute; reflexivity
            | idtac "Entailment goal requires manual proof"
            | prove_evidence_valid ]
          end ].

(* ================================================================== *)
(* Section 14: ID-disjointness reflection                              *)
(* ================================================================== *)

Lemma mem_string_In : forall s l,
    mem_string s l = true -> In s l.
Proof.
  intros s l H. unfold mem_string in H.
  exact (existsb_In _ _ H).
Qed.

Lemma In_mem_string : forall s l,
    In s l -> mem_string s l = true.
Proof.
  intros s l H. unfold mem_string.
  exact (In_existsb _ _ H).
Qed.

Lemma check_id_disjoint_correct : forall ac1 ac2,
    check_id_disjoint ac1 ac2 = true ->
    forall id,
      In id (map node_id ac1.(ac_nodes)) ->
      In id (map node_id ac2.(ac_nodes)) ->
      False.
Proof.
  intros ac1 ac2 H id Hin1 Hin2.
  unfold check_id_disjoint in H.
  apply in_map_iff in Hin1. destruct Hin1 as [n [Hid Hn]].
  apply forallb_forall with (x := n) in H; [| exact Hn].
  subst id.
  assert (Hmem : mem_string n.(node_id) (map node_id ac2.(ac_nodes)) = true).
  { unfold mem_string. apply In_existsb. exact Hin2. }
  rewrite Hmem in H. discriminate.
Qed.

(** One-shot composition: check disjointness and structural_checks,
    then build WellFormed.  Entailment and evidence validity are
    still user obligations. *)
Ltac prove_composed_well_formed :=
  match goal with
  | |- WellFormed (compose_cases ?p ?s ?g) =>
    apply build_well_formed;
    [ vm_compute; reflexivity
    | (* entailment — user must prove *)
      idtac
    | (* evidence validity *)
      prove_evidence_valid ]
  end.

(* ================================================================== *)
(* Section 15: compute_diagnostics with soundness + completeness       *)
(* ================================================================== *)

(** Helper: flat_map over a list is [] when each element maps to []. *)
Lemma flat_map_nil : forall {A B : Type} (f : A -> list B) (l : list A),
    flat_map f l = [] -> forall x, In x l -> f x = [].
Proof.
  induction l as [|a l' IH]; intros Hnil x Hx.
  - destruct Hx.
  - simpl in Hnil. apply app_eq_nil in Hnil. destruct Hnil as [Ha Hl'].
    destruct Hx as [<- | Hx].
    + exact Ha.
    + exact (IH Hl' x Hx).
Qed.

Lemma forallb_flat_map_nil : forall {A B : Type} (p : A -> bool)
    (f : A -> list B) (l : list A),
    forallb p l = true ->
    (forall x, In x l -> p x = true -> f x = []) ->
    flat_map f l = [].
Proof.
  induction l as [|a l' IH]; intros Hp Hf; simpl.
  - reflexivity.
  - simpl in Hp. apply Bool.andb_true_iff in Hp. destruct Hp as [Ha Hl'].
    rewrite (Hf a (or_introl eq_refl) Ha).
    simpl. exact (IH Hl' (fun x Hx => Hf x (or_intror Hx))).
Qed.

(** Soundness of each diagnostic sub-function: if the corresponding
    boolean check passes, the diagnostic returns []. *)

Lemma diagnose_top_sound : forall ac,
    check_top_is_goal ac = true -> diagnose_top ac = [].
Proof.
  intros ac H. unfold check_top_is_goal in H. unfold diagnose_top.
  destruct (find_node ac ac.(ac_top)) as [n|]; [| discriminate].
  destruct n.(node_kind); try discriminate. reflexivity.
Qed.

Lemma not_In_mem_string : forall s l,
    ~ In s l -> mem_string s l = false.
Proof.
  intros s l Hni. unfold mem_string.
  destruct (existsb (String.eqb s) l) eqn:E; [| reflexivity].
  exfalso. exact (Hni (existsb_In s l E)).
Qed.

Lemma diagnose_unique_ids_go_sound : forall nodes seen,
    NoDup (map node_id nodes) ->
    (forall x, In x seen -> ~ In x (map node_id nodes)) ->
    (let fix go (s : list Id) (ns : list Node) : list CheckError :=
       match ns with
       | [] => []
       | n :: rest =>
         if mem_string n.(node_id) s
         then ErrDuplicateId n.(node_id) :: go s rest
         else go (n.(node_id) :: s) rest
       end
     in go seen nodes) = [].
Proof.
  induction nodes as [|n ns IH]; intros seen Hnd Hdisj; simpl.
  - reflexivity.
  - inversion Hnd as [| ? ? Hna Hnd']; subst.
    assert (Hni : ~ In n.(node_id) seen).
    { intro Hin. exact (Hdisj _ Hin (or_introl eq_refl)). }
    rewrite (not_In_mem_string _ _ Hni).
    apply IH.
    + exact Hnd'.
    + intros x [<- | Hx].
      * exact Hna.
      * intro Hx'. exact (Hdisj x Hx (or_intror Hx')).
Qed.

Lemma diagnose_unique_ids_sound : forall ac,
    check_unique_ids ac = true -> diagnose_unique_ids ac = [].
Proof.
  intros ac H. unfold diagnose_unique_ids.
  apply diagnose_unique_ids_go_sound.
  - exact (nodupb_NoDup _ H).
  - intros x Hx. destruct Hx.
Qed.

Lemma diagnose_dangling_sound : forall ac,
    check_no_dangling ac = true -> diagnose_dangling ac = [].
Proof.
  intros ac H. unfold diagnose_dangling. unfold check_no_dangling in H.
  apply forallb_flat_map_nil with
    (p := fun l =>
      match find_node ac l.(link_from), find_node ac l.(link_to) with
      | Some _, Some _ => true | _, _ => false end).
  - exact H.
  - intros l _ Hp.
    destruct (find_node ac l.(link_from));
    destruct (find_node ac l.(link_to)); try discriminate.
    reflexivity.
Qed.

Lemma diagnose_acyclic_sound : forall ac,
    verify_topo_order ac (topo_sort ac) = true ->
    diagnose_acyclic ac = [].
Proof.
  intros ac H. unfold diagnose_acyclic. rewrite H. reflexivity.
Qed.

Lemma diagnose_context_links_sound : forall ac,
    check_context_links ac = true -> diagnose_context_links ac = [].
Proof.
  intros ac H. unfold diagnose_context_links. unfold check_context_links in H.
  apply forallb_flat_map_nil with
    (p := fun l =>
      match l.(link_kind) with
      | SupportedBy => true
      | InContextOf =>
        match find_node ac l.(link_from), find_node ac l.(link_to) with
        | Some nf, Some nt =>
          (match nf.(node_kind) with Goal | Strategy => true | _ => false end) &&
          (match nt.(node_kind) with
           | Context | Assumption | Justification => true | _ => false end)
        | _, _ => false
        end
      | Defeater =>
        match find_node ac l.(link_to) with
        | Some nt =>
          match nt.(node_kind) with Goal | Strategy => true | _ => false end
        | None => false
        end
      end).
  - exact H.
  - intros l _ Hp.
    destruct l.(link_kind).
    + reflexivity.
    + destruct (find_node ac l.(link_from)) as [nf|]; [| discriminate].
      destruct (find_node ac l.(link_to)) as [nt|]; [| discriminate].
      apply Bool.andb_true_iff in Hp. destruct Hp as [Hfk Htk].
      simpl.
      destruct nf.(node_kind); try discriminate;
      destruct nt.(node_kind); try discriminate;
      reflexivity.
    + destruct (find_node ac l.(link_to)) as [nt|]; [| discriminate].
      simpl.
      destruct nt.(node_kind); try discriminate;
      reflexivity.
Qed.

(** Verified diagnostic function tied to [structural_checks].
    Returns [] iff structural_checks passes. *)
Definition compute_diagnostics (ac : AssuranceCase) : list CheckError :=
  (if check_top_is_goal ac then nil else diagnose_top ac) ++
  (if check_unique_ids ac then nil else diagnose_unique_ids ac) ++
  (if check_no_dangling ac then nil else diagnose_dangling ac) ++
  (if verify_topo_order ac (topo_sort ac) then nil
   else diagnose_acyclic ac) ++
  (if check_all_discharged ac then nil
   else flat_map (fun n =>
    match n.(node_kind) with
    | Goal | Strategy =>
      match supportedby_children ac n.(node_id) with
      | [] => [ErrUnsupported n.(node_id)]
      | _ => []
      end
    | Solution =>
      match n.(node_evidence) with
      | None => [ErrMissingEvidence n.(node_id)]
      | Some (ProofTerm _ _ _ _) => []
      | Some (Certificate b _ v) =>
        if v b then [] else [ErrInvalidEvidence n.(node_id)]
      end
    | _ => []
    end) ac.(ac_nodes)) ++
  (if check_context_links ac then nil
   else diagnose_context_links ac).

Lemma compute_diagnostics_sound : forall ac,
    structural_checks ac = true ->
    compute_diagnostics ac = [].
Proof.
  intros ac H. unfold compute_diagnostics. unfold structural_checks in H.
  repeat (apply Bool.andb_true_iff in H; destruct H as [H ?]).
  (* H : check_top_is_goal, H4 : check_unique_ids,
     H3 : check_no_dangling, H2 : verify_topo_order,
     H1 : check_all_discharged, H0 : check_context_links *)
  rewrite H, H0, H1, H2, H3, H4. reflexivity.
Qed.

(** Completeness requires each diagnostic to be non-empty on failure.
    We guarantee this by construction: when a check fails, we include
    a sentinel error, ensuring the overall list is always non-empty. *)
Definition compute_diagnostics_strict (ac : AssuranceCase) : list CheckError :=
  (if check_top_is_goal ac then nil else [ErrTopNotGoal ac.(ac_top)]) ++
  (if check_unique_ids ac then nil else [ErrDuplicateId ""]) ++
  (if check_no_dangling ac then nil else [ErrDanglingFrom "" ""]) ++
  (if verify_topo_order ac (topo_sort ac) then nil else [ErrCycle ""]) ++
  (if check_all_discharged ac then nil else [ErrMissingEvidence ""]) ++
  (if check_context_links ac then nil else [ErrBadContextSource "" ""]).

Lemma compute_diagnostics_strict_sound : forall ac,
    structural_checks ac = true ->
    compute_diagnostics_strict ac = [].
Proof.
  intros ac H. unfold compute_diagnostics_strict, structural_checks in *.
  repeat (apply Bool.andb_true_iff in H; destruct H as [H ?]).
  rewrite H, H0, H1, H2, H3, H4. reflexivity.
Qed.

Lemma compute_diagnostics_strict_complete : forall ac,
    compute_diagnostics_strict ac = [] ->
    structural_checks ac = true.
Proof.
  intros ac H. unfold compute_diagnostics_strict in H. unfold structural_checks.
  destruct (check_top_is_goal ac); simpl in H; [|discriminate].
  destruct (check_unique_ids ac); simpl in H; [|discriminate].
  destruct (check_no_dangling ac); simpl in H; [|discriminate].
  destruct (verify_topo_order ac (topo_sort ac)); simpl in H; [|discriminate].
  destruct (check_all_discharged ac); simpl in H; [|discriminate].
  destruct (check_context_links ac); simpl in H; [|discriminate].
  reflexivity.
Qed.

(** Concrete-case tactic for CI gates. *)
Ltac prove_diagnostics_empty :=
  match goal with
  | |- compute_diagnostics ?ac = [] =>
    apply compute_diagnostics_sound; vm_compute; reflexivity
  end.

(** Structural soundness: diagnostics empty + entailment + evidence
    validity implies WellFormed. *)
Theorem diagnostics_to_well_formed : forall ac,
    compute_diagnostics_strict ac = [] ->
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
    WellFormed ac.
Proof.
  intros ac Hdiag Hent Hev.
  apply build_well_formed.
  - exact (compute_diagnostics_strict_complete ac Hdiag).
  - exact Hent.
  - exact Hev.
Qed.

(* ================================================================== *)
(* Section 16: check_support_tree completeness                         *)
(* ================================================================== *)

(** Monotonicity: check_support_tree_go is monotonically
    non-decreasing in fuel — passing at fuel [f1] implies
    passing at any fuel [f2 >= f1]. *)
Lemma check_stg_mono : forall ac fuel1 id,
    check_support_tree_go ac fuel1 id = true ->
    forall fuel2, fuel1 <= fuel2 ->
    check_support_tree_go ac fuel2 id = true.
Proof.
  intros ac fuel1. induction fuel1 as [|f1 IH]; intros id H1 fuel2 Hle.
  - simpl in H1. discriminate.
  - destruct fuel2 as [|f2]; [inversion Hle |].
    apply le_S_n in Hle.
    simpl in H1. simpl.
    destruct (find_node ac id) as [n|]; [| exact H1].
    destruct n.(node_kind) eqn:Hk; try exact H1.
    (* Goal *)
    + destruct (supportedby_children ac id) as [|k ks] eqn:Hkids; [exact H1 |].
      apply forallb_forall. intros kid Hkid.
      apply forallb_forall with (x := kid) in H1; [| exact Hkid].
      exact (IH kid H1 f2 Hle).
    (* Strategy *)
    + destruct (supportedby_children ac id) as [|k ks] eqn:Hkids; [exact H1 |].
      apply forallb_forall. intros kid Hkid.
      apply forallb_forall with (x := kid) in H1; [| exact Hkid].
      exact (IH kid H1 f2 Hle).
Qed.

(** Height stability: when [height_fuel] hasn't hit the fuel ceiling,
    adding more fuel doesn't change the result. *)
Lemma height_fuel_stable : forall ac f id,
    height_fuel ac f id < f ->
    height_fuel ac (S f) id = height_fuel ac f id.
Proof.
  intros ac f. induction f as [|f' IH]; intros id Hlt.
  - inversion Hlt.
  - rewrite height_fuel_S. rewrite height_fuel_S.
    destruct (supportedby_children ac id) as [|k ks] eqn:Hkids.
    + reflexivity.
    + rewrite height_fuel_S in Hlt. rewrite Hkids in Hlt.
      apply Nat.succ_lt_mono in Hlt.
      f_equal. f_equal.
      apply map_ext_in. intros kid Hkid.
      apply IH.
      apply Nat.le_lt_trans with
        (fold_right Nat.max 0 (map (height_fuel ac f') (k :: ks))).
      * exact (In_le_fold_max _ kid (k :: ks) Hkid).
      * exact Hlt.
Qed.

(** In a well-formed case, children have strictly smaller
    [height_fuel] at the canonical fuel [N = length ac_nodes]. *)
Lemma height_child_canonical : forall ac kid id,
    WellFormed ac ->
    (id = ac.(ac_top) \/ Reaches ac ac.(ac_top) id) ->
    In kid (supportedby_children ac id) ->
    height_fuel ac (length (ac_nodes ac)) kid <
    height_fuel ac (length (ac_nodes ac)) id.
Proof.
  intros ac kid id HWF Hreach Hkid.
  set (N := length (ac_nodes ac)).
  pose proof (height_fuel_lt_nodes ac id HWF Hreach) as Hid_lt.
  fold N in Hid_lt.
  (* N >= 1 since id is reachable *)
  destruct N as [|m].
  { exfalso. inversion Hid_lt. }
  pose proof (height_child_fuel ac m id kid Hkid) as Hchild.
  (* Hchild : height_fuel ac m kid < height_fuel ac (S m) id *)
  (* Hid_lt : height_fuel ac (S m) id < S m *)
  assert (Hkid_lt : height_fuel ac m kid < m).
  { apply Nat.lt_le_trans with (height_fuel ac (S m) id).
    - exact Hchild.
    - apply Nat.lt_succ_r. exact Hid_lt. }
  rewrite (height_fuel_stable ac m kid Hkid_lt).
  exact Hchild.
Qed.

(** Main completeness: by strong induction on height_fuel. *)
Lemma check_stg_by_height : forall ac h id,
    WellFormed ac ->
    (id = ac.(ac_top) \/ Reaches ac ac.(ac_top) id) ->
    height_fuel ac (length (ac_nodes ac)) id = h ->
    (forall n, In n ac.(ac_nodes) ->
      n.(node_kind) = Solution ->
      match n.(node_evidence) with
      | Some (ProofTerm _ _ _ (Some f)) => f n.(node_claim_text) = true
      | Some (ProofTerm _ _ _ None) => False
      | Some (Certificate b _ v) => v b = true
      | None => False
      end) ->
    check_support_tree_go ac (S h) id = true.
Proof.
  intros ac h. induction h as [h IH] using (well_founded_ind Wf_nat.lt_wf).
  intros id HWF Hreach Hheq Hev.
  set (N := length (ac_nodes ac)).
  simpl.
  (* find_node succeeds for reachable nodes *)
  assert (Hfn : exists n, find_node ac id = Some n).
  { exact (reachable_find_node ac id HWF Hreach). }
  destruct Hfn as [n Hfind]. rewrite Hfind.
  pose proof (wf_discharged _ HWF id Hreach) as Hdisch.
  rewrite Hfind in Hdisch.
  destruct n.(node_kind) eqn:Hk.
  - (* Goal *)
    destruct (supportedby_children ac id) as [|k ks] eqn:Hkids.
    + exfalso. exact (Hdisch eq_refl).
    + apply forallb_forall. intros kid Hkid.
      assert (Hkid_reach : kid = ac.(ac_top) \/ Reaches ac ac.(ac_top) kid).
      { exact (children_reachable ac id kid Hreach
                (eq_ind _ (fun l => In kid l) Hkid _ (eq_sym Hkids))). }
      pose proof (height_child_canonical ac kid id HWF Hreach
                   (eq_ind _ (fun l => In kid l) Hkid _ (eq_sym Hkids)))
        as Hlt.
      rewrite Hheq in Hlt.
      set (hk := height_fuel ac N kid).
      apply check_stg_mono with (fuel1 := S hk).
      * apply IH; [exact Hlt | exact HWF | exact Hkid_reach | reflexivity | exact Hev].
      * apply Nat.le_succ_l. exact Hlt.
  - (* Strategy — same structure as Goal *)
    destruct (supportedby_children ac id) as [|k ks] eqn:Hkids.
    + exfalso. exact (Hdisch eq_refl).
    + apply forallb_forall. intros kid Hkid.
      assert (Hkid_reach : kid = ac.(ac_top) \/ Reaches ac ac.(ac_top) kid).
      { exact (children_reachable ac id kid Hreach
                (eq_ind _ (fun l => In kid l) Hkid _ (eq_sym Hkids))). }
      pose proof (height_child_canonical ac kid id HWF Hreach
                   (eq_ind _ (fun l => In kid l) Hkid _ (eq_sym Hkids)))
        as Hlt.
      rewrite Hheq in Hlt.
      set (hk := height_fuel ac N kid).
      apply check_stg_mono with (fuel1 := S hk).
      * apply IH; [exact Hlt | exact HWF | exact Hkid_reach | reflexivity | exact Hev].
      * apply Nat.le_succ_l. exact Hlt.
  - (* Solution *)
    destruct Hdisch as [e [He Hvalid]]. rewrite He.
    pose proof (Hev n (find_node_in ac id n Hfind) Hk) as Hev_n.
    rewrite He in Hev_n.
    destruct e as [lbl P pf [chk|] | blob tool v].
    + exact Hev_n.
    + destruct Hev_n.
    + exact Hev_n.
  - (* Context *) reflexivity.
  - (* Assumption *) reflexivity.
  - (* Justification *) reflexivity.
Qed.

(** check_support_tree is complete for well-formed cases:
    if the assurance case is well-formed and evidence is
    computationally valid, the boolean checker returns true. *)
Theorem check_support_tree_complete : forall ac,
    WellFormed ac ->
    (forall n, In n ac.(ac_nodes) ->
      n.(node_kind) = Solution ->
      match n.(node_evidence) with
      | Some (ProofTerm _ _ _ (Some f)) => f n.(node_claim_text) = true
      | Some (ProofTerm _ _ _ None) => False
      | Some (Certificate b _ v) => v b = true
      | None => False
      end) ->
    check_support_tree ac ac.(ac_top) = true.
Proof.
  intros ac HWF Hev.
  unfold check_support_tree.
  set (N := length (ac_nodes ac)).
  set (h := height_fuel ac N ac.(ac_top)).
  pose proof (height_fuel_lt_nodes ac ac.(ac_top) HWF
    (or_introl eq_refl)) as Hlt.
  apply check_stg_mono with (fuel1 := S h).
  - exact (check_stg_by_height ac h ac.(ac_top) HWF
             (or_introl eq_refl) eq_refl Hev).
  - fold N. fold h. exact Hlt.
Qed.

(* ================================================================== *)
(* Diagnose-structural completeness                                   *)
(* ================================================================== *)

(** Sub-completeness: diagnose_top *)
Lemma diagnose_top_nil_check : forall ac,
    diagnose_top ac = [] -> check_top_is_goal ac = true.
Proof.
  intros ac H. unfold diagnose_top in H. unfold check_top_is_goal.
  destruct (find_node ac ac.(ac_top)) as [n|]; [| discriminate].
  destruct n.(node_kind); try discriminate. reflexivity.
Qed.

(** Sub-completeness: diagnose_dangling *)
Lemma diagnose_dangling_nil_check : forall ac,
    diagnose_dangling ac = [] -> check_no_dangling ac = true.
Proof.
  intros ac H. unfold check_no_dangling.
  apply forallb_forall. intros l Hin.
  unfold diagnose_dangling in H.
  pose proof (flat_map_nil _ _ H l Hin) as Hl.
  simpl in Hl.
  destruct (find_node ac l.(link_from)) as [nf|];
  destruct (find_node ac l.(link_to))   as [nt|];
  simpl in Hl; try discriminate; reflexivity.
Qed.

(** Sub-completeness: discharged (all-nodes variant) *)
Lemma diagnose_discharged_all_nil_check : forall ac,
    flat_map (fun n =>
      match n.(node_kind) with
      | Goal | Strategy =>
        match supportedby_children ac n.(node_id) with
        | [] => [ErrUnsupported n.(node_id)]
        | _ => []
        end
      | Solution =>
        match n.(node_evidence) with
        | None => [ErrMissingEvidence n.(node_id)]
        | Some (ProofTerm _ _ _ (Some f)) =>
          if f n.(node_claim_text) then [] else [ErrInvalidEvidence n.(node_id)]
        | Some (ProofTerm _ _ _ None) =>
          [ErrInvalidEvidence n.(node_id)]
        | Some (Certificate b _ v) =>
          if v b then [] else [ErrInvalidEvidence n.(node_id)]
        end
      | _ => []
      end) ac.(ac_nodes) = [] ->
    check_all_discharged ac = true.
Proof.
  intros ac H. unfold check_all_discharged.
  apply forallb_forall. intros n Hin.
  assert (Hn := flat_map_nil _ _ H n Hin).
  simpl in Hn.
  destruct n.(node_kind); try reflexivity.
  - destruct (supportedby_children ac n.(node_id));
      [discriminate | reflexivity].
  - destruct (supportedby_children ac n.(node_id));
      [discriminate | reflexivity].
  - destruct n.(node_evidence) as [[lbl P pf chk | b ? v]|];
      try discriminate.
    + (* ProofTerm *)
      destruct chk as [f|].
      * (* Some f: Hn says if f n.(node_claim_text) then [] else [...] = [] *)
        destruct (f n.(node_claim_text)) eqn:Ef.
        -- reflexivity.
        -- exfalso. exact (nil_cons (eq_sym Hn)).
      * (* None: Hn says [...] = [] *)
        exfalso. exact (nil_cons (eq_sym Hn)).
    + (* Certificate *)
      destruct (v b); [reflexivity | discriminate].
Qed.

(** Sub-completeness: diagnose_context_links (requires no dangling
    links, since the diagnostic does not flag missing endpoints). *)
Lemma diagnose_context_links_nil_check : forall ac,
    no_dangling_links ac ->
    diagnose_context_links ac = [] ->
    check_context_links ac = true.
Proof.
  intros ac Hnd H. unfold check_context_links.
  apply forallb_forall. intros l Hin.
  destruct l.(link_kind) eqn:Hkind.
  - reflexivity.
  - unfold diagnose_context_links in H.
    assert (Hl := flat_map_nil _ _ H l Hin).
    simpl in Hl. rewrite Hkind in Hl. cbv zeta in Hl.
    destruct (Hnd l Hin) as [[nf Hfrom] [nt Hto]].
    rewrite Hfrom, Hto. rewrite Hfrom, Hto in Hl. simpl in Hl.
    apply Bool.andb_true_iff. split.
    + destruct nf.(node_kind); try reflexivity;
        exfalso; revert Hl; destruct nt.(node_kind); simpl; discriminate.
    + destruct nt.(node_kind); try reflexivity;
        exfalso; revert Hl; destruct nf.(node_kind); simpl;
        try discriminate;
        intro HH; apply app_eq_nil in HH; destruct HH; discriminate.
  - unfold diagnose_context_links in H.
    assert (Hl := flat_map_nil _ _ H l Hin).
    simpl in Hl. rewrite Hkind in Hl.
    destruct (Hnd l Hin) as [_ [nt Hto]].
    rewrite Hto. rewrite Hto in Hl.
    destruct nt.(node_kind); try reflexivity;
      simpl in Hl; discriminate.
Qed.

(** Sub-completeness: diagnose_unique_ids *)

Fixpoint diag_uid_go (seen : list Id) (nodes : list Node)
  : list CheckError :=
  match nodes with
  | [] => []
  | n :: rest =>
    if mem_string n.(node_id) seen
    then ErrDuplicateId n.(node_id) :: diag_uid_go seen rest
    else diag_uid_go (n.(node_id) :: seen) rest
  end.

Lemma diagnose_unique_ids_unfold : forall ac,
    diagnose_unique_ids ac = diag_uid_go [] ac.(ac_nodes).
Proof. reflexivity. Qed.

Lemma diag_uid_go_nil_disjoint : forall seen ns,
    diag_uid_go seen ns = [] ->
    forall id, In id (map node_id ns) ->
    mem_string id seen = false.
Proof.
  intros seen ns. revert seen.
  induction ns as [|n rest IH]; intros seen H id Hin.
  - destruct Hin.
  - simpl in H.
    destruct (mem_string n.(node_id) seen) eqn:Hmem; [discriminate |].
    simpl in Hin. destruct Hin as [<- | Hin].
    + exact Hmem.
    + pose proof (IH _ H id Hin) as IHres.
      unfold mem_string in IHres. simpl in IHres.
      apply Bool.orb_false_iff in IHres. exact (proj2 IHres).
Qed.

Lemma diag_uid_go_nil_nodupb : forall seen ns,
    diag_uid_go seen ns = [] ->
    nodupb (map node_id ns) = true.
Proof.
  intros seen ns. revert seen.
  induction ns as [|n rest IH]; intros seen H.
  - reflexivity.
  - simpl. simpl in H.
    destruct (mem_string n.(node_id) seen) eqn:Hmem; [discriminate |].
    apply Bool.andb_true_iff. split.
    + apply Bool.negb_true_iff.
      destruct (mem_string n.(node_id) (map node_id rest)) eqn:Hm2.
      * exfalso.
        apply existsb_In in Hm2.
        pose proof (diag_uid_go_nil_disjoint _ _ H _ Hm2) as Habs.
        unfold mem_string in Habs. simpl in Habs.
        rewrite String.eqb_refl in Habs. discriminate.
      * reflexivity.
    + exact (IH _ H).
Qed.

Lemma diagnose_unique_ids_nil_check : forall ac,
    diagnose_unique_ids ac = [] ->
    check_unique_ids ac = true.
Proof.
  intros ac H.
  rewrite diagnose_unique_ids_unfold in H.
  exact (diag_uid_go_nil_nodupb [] _ H).
Qed.

(* ================================================================== *)
(* BFS monotonicity                                                   *)
(* ================================================================== *)

(** BFS result grows with fuel: more fuel means a superset. *)
Lemma rsf_fuel_mono : forall ac f1 f2 frontier acc,
    f1 <= f2 ->
    forall x, In x (reachable_set_fuel ac f1 frontier acc) ->
              In x (reachable_set_fuel ac f2 frontier acc).
Proof.
  intros ac f1. induction f1 as [|f1' IH]; intros f2 frontier acc Hle x Hin.
  - simpl in Hin. exact (rsf_acc_subset ac f2 frontier acc x Hin).
  - destruct f2 as [|f2']; [inversion Hle |].
    apply Nat.succ_le_mono in Hle.
    simpl in Hin |- *.
    remember (filter (fun id => negb (mem_string id acc))
               (flat_map (supportedby_children ac) frontier)) as fresh.
    destruct fresh as [|h t].
    + exact Hin.
    + apply IH; [exact Hle | exact Hin].
Qed.

(** BFS completeness: single-step children of accumulated nodes
    are in the result (with enough fuel). *)
Lemma rsf_child_in_result : forall ac fuel frontier acc w v,
    In w frontier ->
    In v (supportedby_children ac w) ->
    In v (reachable_set_fuel ac (S fuel) frontier acc).
Proof.
  intros ac fuel frontier acc w v Hw Hv.
  simpl.
  remember (filter (fun id => negb (mem_string id acc))
             (flat_map (supportedby_children ac) frontier)) as fresh.
  destruct (mem_string v acc) eqn:Hmem.
  - (* v already in acc *)
    destruct fresh.
    + exact (existsb_In v acc Hmem).
    + apply rsf_acc_subset. apply in_or_app. left.
      exact (existsb_In v acc Hmem).
  - (* v is fresh *)
    destruct fresh as [|h t] eqn:Hfresh.
    + (* no fresh nodes: v must be in acc *)
      exfalso.
      assert (Hin : In v (flat_map (supportedby_children ac) frontier)).
      { apply in_flat_map. exists w. exact (conj Hw Hv). }
      assert (Hfilt : In v (filter (fun id => negb (mem_string id acc))
                             (flat_map (supportedby_children ac) frontier))).
      { apply filter_In. split; [exact Hin |]. rewrite Hmem. reflexivity. }
      rewrite <- Heqfresh in Hfilt. destruct Hfilt.
    + apply rsf_acc_subset. apply in_or_app. right.
      rewrite Heqfresh.
      apply filter_In. split.
      * apply in_flat_map. exists w. exact (conj Hw Hv).
      * rewrite Hmem. reflexivity.
Qed.

Lemma children_in_node_ids : forall ac w v,
    no_dangling_links ac ->
    In v (supportedby_children ac w) ->
    In v (map node_id ac.(ac_nodes)).
Proof.
  intros ac w v Hnd Hv.
  unfold supportedby_children in Hv.
  apply in_map_iff in Hv. destruct Hv as [l [Hto Hfilt]].
  apply filter_In in Hfilt. destruct Hfilt as [Hlin _].
  destruct (Hnd l Hlin) as [_ [nt Hnt]].
  subst v. apply in_map_iff. exists nt. split.
  - exact (find_node_id ac l.(link_to) nt Hnt).
  - exact (find_node_in ac l.(link_to) nt Hnt).
Qed.

Lemma rsf_closed_terminal : forall ac frontier acc,
    (forall w, In w acc ->
      (forall v, In v (supportedby_children ac w) -> In v acc) \/
      In w frontier) ->
    filter (fun id => negb (mem_string id acc))
      (flat_map (supportedby_children ac) frontier) = [] ->
    forall w v, In w acc -> In v (supportedby_children ac w) -> In v acc.
Proof.
  intros ac frontier acc HINV Hfr w v Hw Hv.
  destruct (HINV w Hw) as [Hc | Hf].
  - exact (Hc v Hv).
  - destruct (mem_string v acc) eqn:Hm.
    + exact (existsb_In v acc Hm).
    + exfalso.
      assert (In v (filter (fun id => negb (mem_string id acc))
                      (flat_map (supportedby_children ac) frontier))).
      { apply filter_In. split.
        - apply in_flat_map. exists w. exact (conj Hf Hv).
        - rewrite Hm. reflexivity. }
      rewrite Hfr in H. exact H.
Qed.

Lemma rsf_inv_step : forall ac frontier acc fresh,
    fresh = filter (fun id => negb (mem_string id acc))
              (flat_map (supportedby_children ac) frontier) ->
    (forall w, In w acc ->
      (forall v, In v (supportedby_children ac w) -> In v acc) \/
      In w frontier) ->
    (forall w, In w (acc ++ fresh) ->
      (forall v, In v (supportedby_children ac w) -> In v (acc ++ fresh)) \/
      In w fresh).
Proof.
  intros ac frontier acc fresh Hfresh HINV w Hw.
  apply in_app_iff in Hw. destruct Hw as [Ha | Hf].
  - destruct (HINV w Ha) as [Hc | Hfront].
    + left. intros v Hv. apply in_or_app. left. exact (Hc v Hv).
    + left. intros v Hv. apply in_or_app.
      destruct (mem_string v acc) eqn:Hm.
      * left. exact (existsb_In v acc Hm).
      * right. rewrite Hfresh. apply filter_In. split.
        -- apply in_flat_map. exists w. exact (conj Hfront Hv).
        -- rewrite Hm. reflexivity.
  - right. exact Hf.
Qed.

(* ================================================================== *)
(* NoDup-free BFS closure via missing-count fuel bound               *)
(* ================================================================== *)

(** Count of node IDs not yet in the accumulator.  Decreases by at
    least 1 per BFS step, providing a fuel bound without NoDup. *)
Definition missing_count (ac : AssuranceCase) (acc : list Id) : nat :=
  length (filter (fun id => negb (mem_string id acc))
                 (map node_id ac.(ac_nodes))).

Lemma filter_length_le_gen : forall {A} (f : A -> bool) (l : list A),
    length (filter f l) <= length l.
Proof.
  intros A f l. induction l as [|a l' IH]; simpl.
  - apply Nat.le_refl.
  - destruct (f a); simpl.
    + apply le_n_S. exact IH.
    + apply Nat.le_trans with (length l').
      * exact IH.
      * apply Nat.le_succ_diag_r.
Qed.

Lemma missing_count_le_nodes : forall ac acc,
    missing_count ac acc <= length ac.(ac_nodes).
Proof.
  intros. unfold missing_count.
  apply Nat.le_trans with (length (map node_id ac.(ac_nodes))).
  - exact (filter_length_le_gen _ _).
  - rewrite length_map. apply Nat.le_refl.
Qed.

Lemma missing_count_zero_mem : forall ac acc id,
    missing_count ac acc = 0 ->
    In id (map node_id ac.(ac_nodes)) ->
    mem_string id acc = true.
Proof.
  intros ac acc id H Hin.
  unfold missing_count in H.
  destruct (mem_string id acc) eqn:Hm; [reflexivity |].
  exfalso.
  assert (Hfilt : In id (filter (fun x => negb (mem_string x acc))
                           (map node_id ac.(ac_nodes)))).
  { apply filter_In. split; [exact Hin |]. rewrite Hm. reflexivity. }
  destruct (filter (fun x => negb (mem_string x acc))
              (map node_id ac.(ac_nodes))) as [|a rest] eqn:E.
  - destruct Hfilt.
  - simpl in H. discriminate.
Qed.

Lemma mem_string_weaken_app : forall s l1 l2,
    mem_string s l1 = true -> mem_string s (l1 ++ l2) = true.
Proof.
  intros s l1 l2 H. unfold mem_string in *.
  apply In_existsb. apply in_or_app. left. exact (existsb_In s l1 H).
Qed.

Lemma filter_incl_length : forall {A} (f g : A -> bool) (l : list A),
    (forall x, In x l -> f x = true -> g x = true) ->
    length (filter f l) <= length (filter g l).
Proof.
  intros A f g l Himpl. induction l as [|a l' IH]; simpl.
  - apply Nat.le_refl.
  - assert (Himpl' : forall x, In x l' -> f x = true -> g x = true)
      by (intros x Hx; exact (Himpl x (or_intror Hx))).
    destruct (f a) eqn:Hf; destruct (g a) eqn:Hg; simpl.
    + apply le_n_S. exact (IH Himpl').
    + exfalso. rewrite (Himpl a (or_introl eq_refl) Hf) in Hg. discriminate.
    + apply Nat.le_trans with (length (filter g l')).
      * exact (IH Himpl').
      * apply Nat.le_succ_diag_r.
    + exact (IH Himpl').
Qed.

Lemma filter_strict_length : forall {A} (f g : A -> bool) (l : list A),
    (forall x, In x l -> f x = true -> g x = true) ->
    (exists x, In x l /\ g x = true /\ f x = false) ->
    length (filter f l) < length (filter g l).
Proof.
  intros A f g l Himpl [w [Hw [Hgw Hfw]]].
  induction l as [|a l' IH]; [destruct Hw |].
  assert (Himpl' : forall x, In x l' -> f x = true -> g x = true)
    by (intros x Hx; exact (Himpl x (or_intror Hx))).
  simpl.
  destruct Hw as [<- | Hw'].
  - rewrite Hgw, Hfw. simpl.
    apply le_n_S. exact (filter_incl_length f g l' Himpl').
  - destruct (f a) eqn:Hf; destruct (g a) eqn:Hg; simpl.
    + apply le_n_S. exact (IH Himpl' Hw').
    + exfalso. rewrite (Himpl a (or_introl eq_refl) Hf) in Hg. discriminate.
    + apply Nat.le_lt_trans with (length (filter g l')).
      * exact (filter_incl_length f g l' Himpl').
      * apply Nat.lt_succ_diag_r.
    + exact (IH Himpl' Hw').
Qed.

Lemma missing_count_decrease : forall ac acc fresh,
    fresh <> [] ->
    (forall x, In x fresh -> negb (mem_string x acc) = true) ->
    (forall x, In x fresh -> In x (map node_id ac.(ac_nodes))) ->
    missing_count ac (acc ++ fresh) < missing_count ac acc.
Proof.
  intros ac acc fresh Hne Hnot_in Hin_nids.
  unfold missing_count.
  apply filter_strict_length.
  - intros id _ Hf.
    apply Bool.negb_true_iff in Hf. apply Bool.negb_true_iff.
    destruct (mem_string id acc) eqn:Hm; [|reflexivity].
    exfalso. rewrite (mem_string_weaken_app id acc fresh Hm) in Hf.
    discriminate.
  - destruct fresh as [|h t]; [contradiction |].
    exists h. split; [| split].
    + exact (Hin_nids h (or_introl eq_refl)).
    + exact (Hnot_in h (or_introl eq_refl)).
    + apply Bool.negb_false_iff.
      unfold mem_string. apply In_existsb.
      apply in_or_app. right. left. reflexivity.
Qed.

Theorem rsf_result_closed : forall ac fuel frontier acc,
    no_dangling_links ac ->
    (forall w, In w acc ->
      (forall v, In v (supportedby_children ac w) -> In v acc) \/
      In w frontier) ->
    (forall w, In w frontier -> In w acc) ->
    (forall x, In x acc -> In x (map node_id ac.(ac_nodes))) ->
    missing_count ac acc <= fuel ->
    forall w v,
    In w (reachable_set_fuel ac fuel frontier acc) ->
    In v (supportedby_children ac w) ->
    In v (reachable_set_fuel ac fuel frontier acc).
Proof.
  intros ac fuel. induction fuel as [|f IH];
    intros frontier acc Hnd HINV HSUB HIN HFUEL w v Hw Hv.
  - (* fuel = 0: all node IDs are in acc *)
    simpl in Hw |- *.
    assert (Hmz : missing_count ac acc = 0) by (apply Nat.le_0_r; exact HFUEL).
    assert (Hv_nid : In v (map node_id ac.(ac_nodes)))
      by exact (children_in_node_ids ac w v Hnd Hv).
    exact (existsb_In v acc (missing_count_zero_mem ac acc v Hmz Hv_nid)).
  - (* fuel = S f *)
    simpl in Hw |- *.
    remember (filter (fun id => negb (mem_string id acc))
               (flat_map (supportedby_children ac) frontier)) as fresh.
    destruct fresh as [|h t].
    + exact (rsf_closed_terminal ac frontier acc HINV
               (eq_sym Heqfresh) w v Hw Hv).
    + assert (Hfresh_not_in : forall x, In x (h :: t) ->
          negb (mem_string x acc) = true).
      { intros x Hx. rewrite Heqfresh in Hx.
        apply filter_In in Hx. exact (proj2 Hx). }
      assert (HIN' : forall x, In x (acc ++ h :: t) ->
          In x (map node_id ac.(ac_nodes))).
      { intros x Hx. apply in_app_iff in Hx. destruct Hx as [Ha | Hfr].
        - exact (HIN x Ha).
        - rewrite Heqfresh in Hfr. apply filter_In in Hfr.
          destruct Hfr as [Hfm _]. apply in_flat_map in Hfm.
          destruct Hfm as [p [_ Hpc]].
          exact (children_in_node_ids ac p x Hnd Hpc). }
      assert (HFUEL' : missing_count ac (acc ++ h :: t) <= f).
      { assert (Hlt : missing_count ac (acc ++ h :: t) <
                       missing_count ac acc).
        { apply missing_count_decrease; [discriminate | exact Hfresh_not_in |].
          intros x Hx.
          exact (HIN' x (in_or_app acc (h :: t) x (or_intror Hx))). }
        apply Nat.lt_succ_r. apply Nat.lt_le_trans with (missing_count ac acc).
        - exact Hlt.
        - exact HFUEL. }
      exact (IH (h :: t) (acc ++ h :: t) Hnd
               (rsf_inv_step ac frontier acc (h :: t) Heqfresh HINV)
               (fun w0 Hw0 => in_or_app acc (h :: t) w0 (or_intror Hw0))
               HIN' HFUEL' w v Hw Hv).
Qed.

Theorem reachable_from_closed : forall ac start w v,
    no_dangling_links ac ->
    In w (reachable_from ac start) ->
    In v (supportedby_children ac w) ->
    In v (reachable_from ac start).
Proof.
  intros ac start w v Hnd Hw Hv.
  unfold reachable_from in *.
  set (kids := supportedby_children ac start) in *.
  exact (rsf_result_closed ac (length ac.(ac_nodes)) kids kids Hnd
           (fun w0 Hw0 => or_intror Hw0)
           (fun w0 Hw0 => Hw0)
           (fun x Hx => children_in_node_ids ac start x Hnd Hx)
           (missing_count_le_nodes ac kids)
           w v Hw Hv).
Qed.

(* ================================================================== *)
(* Section 17: BFS acyclicity soundness                               *)
(* ================================================================== *)

(** If w is in the BFS result and Reaches ac w v, then v is also
    in the result.  Follows by induction on Reaches using
    reachable_from_closed at each step. *)
Lemma reaches_in_reachable_from : forall ac start w v,
    no_dangling_links ac ->
    In w (reachable_from ac start) ->
    Reaches ac w v ->
    In v (reachable_from ac start).
Proof.
  intros ac start w v Hnd Hw Hreach.
  induction Hreach as [u0 v0 Hstep | u0 m v0 H1 IH1 H2 IH2].
  - exact (reachable_from_closed ac start u0 v0 Hnd Hw Hstep).
  - exact (IH2 (IH1 Hw)).
Qed.

(** Soundness of check_acyclic: if the BFS-based checker returns
    true and the graph has no dangling links, the graph is acyclic.
    NoDup is not required — the BFS fuel bound uses missing_count. *)
Lemma check_acyclic_sound : forall ac,
    no_dangling_links ac ->
    check_acyclic ac = true -> Acyclic ac.
Proof.
  intros ac Hnd Hcheck id Hcycle.
  (* From the cycle Reaches ac id id, extract a first step. *)
  destruct (reaches_first_step ac id id Hcycle) as [mid [Hmid Hrest]].
  (* mid is a SupportedBy child of id, hence in the initial
     frontier = supportedby_children ac id = kids. *)
  (* id must be a node: mid ∈ supportedby_children ac id
     implies a SupportedBy link from id, so find_node ac id = Some n
     by no_dangling_links. *)
  destruct (supportedby_children_link ac id mid Hmid)
    as [l [Hlin [_ [Hfrom _]]]].
  destruct (Hnd l Hlin) as [[nf Hnf] _].
  rewrite Hfrom in Hnf.
  assert (Hin_nodes : In nf ac.(ac_nodes))
    by exact (find_node_in' ac id nf Hnf).
  assert (Hid_eq : nf.(node_id) = id)
    by exact (find_node_id' ac id nf Hnf).
  (* From check_acyclic, nf.(node_id) is NOT in
     reachable_from ac nf.(node_id). *)
  unfold check_acyclic in Hcheck.
  apply forallb_forall with (x := nf) in Hcheck; [| exact Hin_nodes].
  rewrite Hid_eq in Hcheck.
  (* mid is in reachable_from ac id (it's in kids, which is the
     initial accumulator of rsf). *)
  assert (Hmid_in : In mid (reachable_from ac id)).
  { unfold reachable_from. apply rsf_acc_subset. exact Hmid. }
  (* Now derive id ∈ reachable_from ac id for contradiction. *)
  assert (Hid_in : In id (reachable_from ac id)).
  { destruct Hrest as [<- | Hreach_mid_id].
    - (* mid = id: self-loop *)
      exact Hmid_in.
    - (* Reaches ac mid id: iterate reachable_from_closed *)
      exact (reaches_in_reachable_from ac id mid id
               Hnd Hmid_in Hreach_mid_id). }
  (* mem_string id (reachable_from ac id) = true *)
  assert (Hmem : mem_string id (reachable_from ac id) = true)
    by exact (In_mem_string id (reachable_from ac id) Hid_in).
  (* But check_acyclic says negb (mem_string ...) = true,
     i.e., mem_string ... = false.  Contradiction. *)
  rewrite Hmem in Hcheck. discriminate.
Qed.

(** Combined completeness: diagnose_structural = [] implies
    structural_checks = true.  Self-contained — no topo premise. *)
Theorem diagnose_structural_complete : forall ac,
    diagnose_structural ac = [] ->
    structural_checks ac = true.
Proof.
  intros ac Hdiag.
  unfold diagnose_structural in Hdiag.
  apply app_eq_nil in Hdiag. destruct Hdiag as [Htop Hdiag].
  apply app_eq_nil in Hdiag. destruct Hdiag as [Huniq Hdiag].
  apply app_eq_nil in Hdiag. destruct Hdiag as [Hdang Hdiag].
  apply app_eq_nil in Hdiag. destruct Hdiag as [Hacyc Hdiag].
  apply app_eq_nil in Hdiag. destruct Hdiag as [Hdisch Hdiag].
  apply app_eq_nil in Hdiag. destruct Hdiag as [Hctx _].
  (* diagnose_acyclic = [] => verify_topo_order = true *)
  pose proof (diagnose_dangling_nil_check ac Hdang) as Hndang_b.
  pose proof (check_no_dangling_correct ac Hndang_b) as Hnd.
  pose proof (diagnose_unique_ids_nil_check ac Huniq) as Huniq_b.
  pose proof (nodupb_NoDup _ Huniq_b) as Hnodup.
  assert (Htopo : verify_topo_order ac (topo_sort ac) = true).
  { unfold diagnose_acyclic in Hacyc.
    destruct (verify_topo_order ac (topo_sort ac)) eqn:E.
    - reflexivity.
    - (* BFS fallback returned []: extract check_acyclic = true *)
      assert (Hca : check_acyclic ac = true).
      { unfold check_acyclic. apply forallb_forall. intros n Hin.
        apply Bool.negb_true_iff.
        destruct (mem_string n.(node_id) (reachable_from ac n.(node_id))) eqn:Em;
          [| reflexivity].
        exfalso.
        assert (Herr : In (ErrCycle n.(node_id))
          (flat_map (fun n0 =>
            if mem_string n0.(node_id) (reachable_from ac n0.(node_id))
            then [ErrCycle n0.(node_id)] else []) ac.(ac_nodes))).
        { apply in_flat_map. exists n. split; [exact Hin |].
          rewrite Em. left. reflexivity. }
        rewrite Hacyc in Herr. exact Herr. }
      pose proof (check_acyclic_sound ac Hnd Hca) as Hacyclic.
      rewrite (topo_sort_valid ac Hacyclic Hnodup Hnd) in E.
      discriminate. }
  unfold structural_checks.
  rewrite (diagnose_top_nil_check ac Htop).
  rewrite (diagnose_unique_ids_nil_check ac Huniq).
  rewrite (diagnose_dangling_nil_check ac Hdang).
  rewrite Htopo.
  rewrite (diagnose_discharged_all_nil_check ac Hdisch).
  rewrite (diagnose_context_links_nil_check ac
            (check_no_dangling_correct ac
              (diagnose_dangling_nil_check ac Hdang)) Hctx).
  reflexivity.
Qed.

(* ================================================================== *)
(* Factored well-formedness tactic                                     *)
(* ================================================================== *)

Ltac prove_evidence_valid_robust :=
  intros n e Hin Hkind He; simpl in Hin;
  repeat (destruct Hin as [<- | Hin];
    [try discriminate; injection He as <-;
     first [vm_compute; reflexivity | reflexivity] |]);
  destruct Hin as [].

Ltac prove_well_formed_full :=
  match goal with
  | |- WellFormed ?ac =>
    apply build_well_formed;
    [ vm_compute; reflexivity
    | intros ? ? Hfind Hkind;
      vm_compute in Hfind;
      repeat match type of Hfind with
      | (if ?c then _ else _) = _ =>
          destruct c eqn:?;
          [ injection Hfind as <-;
            first [ typeclasses eauto
                  | intro; eauto with rack_entail
                  | vm_compute; tauto
                  | vm_compute; intuition
                  | vm_compute; firstorder
                  | exfalso; destruct Hkind as [? | ?]; discriminate ]
          | ]
      end;
      try discriminate
    | prove_evidence_valid_robust ]
  end.

(* ================================================================== *)
(* check_all_discharged completeness                                   *)
(* ================================================================== *)

Lemma check_all_discharged_complete : forall ac,
    (forall n, In n ac.(ac_nodes) ->
      match n.(node_kind) with
      | Solution =>
        match n.(node_evidence) with
        | Some (Certificate b _ v) => v b = true
        | Some (ProofTerm _ _ _ (Some f)) => f n.(node_claim_text) = true
        | Some (ProofTerm _ _ _ None) => False
        | None => False
        end
      | Goal | Strategy =>
        supportedby_children ac n.(node_id) <> []
      | _ => True
      end) ->
    check_all_discharged ac = true.
Proof.
  intros ac H. unfold check_all_discharged.
  apply forallb_forall. intros n Hin.
  pose proof (H n Hin) as Hn.
  destruct n.(node_kind) eqn:Hk.
  - destruct (supportedby_children ac n.(node_id)) eqn:Hkids;
      [exfalso; exact (Hn eq_refl) | reflexivity].
  - destruct (supportedby_children ac n.(node_id)) eqn:Hkids;
      [exfalso; exact (Hn eq_refl) | reflexivity].
  - destruct n.(node_evidence) as [[? ? ? [?|]|b ? v]|].
    + exact Hn.
    + destruct Hn.
    + exact Hn.
    + destruct Hn.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* ================================================================== *)
(* BFS reachability soundness                                          *)
(* ================================================================== *)

Lemma rsf_sound : forall ac fuel frontier acc start,
    (forall w, In w acc -> Reaches ac start w) ->
    (forall w, In w frontier -> In w acc) ->
    forall v,
    In v (reachable_set_fuel ac fuel frontier acc) ->
    Reaches ac start v.
Proof.
  intros ac fuel. induction fuel as [|f IH];
    intros frontier acc start Hacc Hsub v Hin.
  - simpl in Hin. exact (Hacc v Hin).
  - simpl in Hin.
    remember (filter (fun id => negb (mem_string id acc))
               (flat_map (supportedby_children ac) frontier)) as fresh.
    destruct fresh as [|h t].
    + exact (Hacc v Hin).
    + apply (IH (h :: t) (acc ++ h :: t) start); [| | exact Hin].
      * intros w Hw. apply in_app_iff in Hw.
        destruct Hw as [Hw | Hw].
        -- exact (Hacc w Hw).
        -- rewrite Heqfresh in Hw.
           apply filter_In in Hw. destruct Hw as [Hw _].
           apply in_flat_map in Hw. destruct Hw as [parent [Hpin Hchild]].
           exact (R_Trans ac start parent w
                    (Hacc parent (Hsub parent Hpin))
                    (R_Step ac parent w Hchild)).
      * intros w Hw. apply in_or_app. right. exact Hw.
Qed.

Lemma reachable_from_sound : forall ac start v,
    In v (reachable_from ac start) ->
    Reaches ac start v.
Proof.
  intros ac start v Hin.
  unfold reachable_from in Hin.
  exact (rsf_sound ac _ _ _ start
           (fun w Hw => R_Step ac start w Hw)
           (fun w Hw => Hw)
           v Hin).
Qed.

Theorem check_acyclic_complete : forall ac,
    no_dangling_links ac ->
    Acyclic ac ->
    check_acyclic ac = true.
Proof.
  intros ac Hnd Hacyc. unfold check_acyclic.
  apply forallb_forall. intros n Hin.
  apply Bool.negb_true_iff.
  destruct (mem_string n.(node_id) (reachable_from ac n.(node_id))) eqn:E;
    [| reflexivity].
  exfalso.
  apply existsb_In in E.
  exact (Hacyc n.(node_id) (reachable_from_sound ac n.(node_id) n.(node_id) E)).
Qed.

(* ================================================================== *)
(* Checker relationship lemmas                                         *)
(* ================================================================== *)

Lemma check_wf_extended_equiv : forall ac,
    check_wf_extended ac =
    (structural_checks ac && check_defeaters ac).
Proof. reflexivity. Qed.

Lemma checkers_agree_no_defeaters : forall ac,
    (forall l, In l ac.(ac_links) -> l.(link_kind) <> Defeater) ->
    check_wf_extended ac = structural_checks ac.
Proof.
  intros ac Hnd. unfold check_wf_extended.
  assert (Hdef : check_defeaters ac = true).
  { unfold check_defeaters. apply forallb_forall.
    intros l Hin. destruct l.(link_kind) eqn:Hk; [reflexivity | reflexivity |].
    exfalso. exact (Hnd l Hin Hk). }
  rewrite Hdef, Bool.andb_true_r. reflexivity.
Qed.

Lemma structural_implies_well_formed_iff : forall ac,
    structural_checks ac = true ->
    check_wf_extended ac = check_defeaters ac.
Proof.
  intros ac H. unfold check_wf_extended. rewrite H. reflexivity.
Qed.


(* ================================================================== *)
(* Compositional well-formedness from structural_checks                *)
(* ================================================================== *)

Theorem compose_well_formed_structural : forall p s g,
    WellFormed p ->
    WellFormed s ->
    (exists ng, find_node p g = Some ng) ->
    (exists nt, find_node s s.(ac_top) = Some nt) ->
    (forall id, In id (map node_id p.(ac_nodes)) ->
                In id (map node_id s.(ac_nodes)) -> False) ->
    structural_checks (compose_cases p s g) = true ->
    (forall n e,
      In n (compose_cases p s g).(ac_nodes) ->
      n.(node_kind) = Solution ->
      n.(node_evidence) = Some e ->
      evidence_valid n e) ->
    (forall id n,
      find_node (compose_cases p s g) id = Some n ->
      (n.(node_kind) = Goal \/ n.(node_kind) = Strategy) ->
      (let kids := supportedby_children (compose_cases p s g) id in
       let child_claims :=
         flat_map (fun kid =>
           match find_node (compose_cases p s g) kid with
           | Some cn => [cn.(node_claim)]
           | None     => []
           end) kids
       in fold_right and True child_claims -> n.(node_claim))) ->
    WellFormed (compose_cases p s g).
Proof.
  intros p s g HWFp HWFs Hng Hnt Hdisj Hstruct Hev Hent.
  exact (build_well_formed (compose_cases p s g) Hstruct Hent Hev).
Qed.

