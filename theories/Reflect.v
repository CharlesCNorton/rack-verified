(* ------------------------------------------------------------------ *)
(* Reflection: boolean checkers imply propositional well-formedness     *)
(* ------------------------------------------------------------------ *)

From RACK Require Import Core.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

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
  - destruct l.(link_kind); [reflexivity | discriminate].
  - exact Hfrom.
  - exact Hto.
Qed.

(* index_of properties.                                                *)

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
      | InContextOf => true
      | SupportedBy =>
        match index_of l0.(link_from) order,
              index_of l0.(link_to)   order with
        | Some i, Some j => Nat.ltb i j
        | _, _ => false
        end
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
      | InContextOf => true
      | SupportedBy =>
        match index_of l.(link_from) order,
              index_of l.(link_to)   order with
        | Some i, Some j => Nat.ltb i j
        | _, _ => false
        end
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
      | InContextOf => true
      | SupportedBy =>
        match index_of l.(link_from) order,
              index_of l.(link_to)   order with
        | Some i, Some j => Nat.ltb i j
        | _, _ => false
        end
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
      | InContextOf => true
      | SupportedBy =>
        match index_of l.(link_from) order,
              index_of l.(link_to)   order with
        | Some i, Some j => Nat.ltb i j
        | _, _ => false
        end
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

(* Fully automated well-formedness for concrete cases where
   vm_compute can solve entailment and evidence validity.              *)
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
            first [ vm_compute; tauto
                  | vm_compute; intuition
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
    well_typed_context_links (compose_cases p s g).
Proof.
  intros p s g Hwtp Hwts l Hin Hkind.
  simpl in Hin.
  apply in_app_iff in Hin.
  destruct Hin as [Hinp | Hins].
  - (* link from parent *)
    destruct (Hwtp l Hinp Hkind) as [nf [nt [Hf [Ht [Hfk Htk]]]]].
    exists nf, nt.
    rewrite compose_find_node, Hf.
    split; [reflexivity |].
    rewrite compose_find_node.
    destruct (find_node p nt.(node_id)) eqn:?.
    + split; [reflexivity | split; assumption].
    + rewrite (find_node_id' _ _ _ Ht).
      rewrite Ht.
      split; [reflexivity | split; assumption].
  - apply in_app_iff in Hins.
    destruct Hins as [Hins | [<- | []]].
    + (* link from subcase *)
      destruct (Hwts l Hins Hkind) as [nf [nt [Hf [Ht [Hfk Htk]]]]].
      exists nf, nt.
      split.
      * rewrite compose_find_node.
        destruct (find_node p l.(link_from)); [reflexivity |].
        exact Hf.
      * split.
        -- rewrite compose_find_node.
           destruct (find_node p l.(link_to)); [reflexivity |].
           exact Ht.
        -- split; assumption.
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
        rewrite Hkids in Hcheck.
        apply IH.
        -- rewrite forallb_forall in Hcheck. exact (Hcheck kid Hkid).
        -- exact Hev.
        -- exact Hent.
      * apply Hent; [exact Hfind | left; exact Hkind].
    + (* Strategy *)
      destruct (supportedby_children ac id) as [|k ks] eqn:Hkids;
        [discriminate | ].
      apply ST_Internal with n (k :: ks).
      * exact Hfind.
      * rewrite Hkind; discriminate.
      * symmetry; exact Hkids.
      * discriminate.
      * intros kid Hkid.
        rewrite Hkids in Hcheck.
        apply IH.
        -- rewrite forallb_forall in Hcheck. exact (Hcheck kid Hkid).
        -- exact Hev.
        -- exact Hent.
      * apply Hent; [exact Hfind | right; exact Hkind].
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
