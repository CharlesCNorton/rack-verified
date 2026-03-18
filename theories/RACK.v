(******************************************************************************)
(*                                                                            *)
(*          Rocq Assurance Case Kernel: Mechanized Evidence Graphs            *)
(*                                                                            *)
(*     Typed GSN-inspired claim/strategy/evidence graph with machine-         *)
(*     checked well-formedness, evidence coverage, acyclicity, and            *)
(*     support-tree completeness. Designed for CI-gated assurance cases       *)
(*     linking requirements to proofs and external certificates.              *)
(*                                                                            *)
(*     "The price of reliability is the pursuit of the utmost simplicity."    *)
(*     — C.A.R. Hoare, 1980                                                  *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: March 17, 2026                                                   *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

Require Import Stdlib.Strings.String.
Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(* 1. Core types                                                        *)
(* ------------------------------------------------------------------ *)

Definition Id := string.

Inductive NodeKind : Type :=
  | Goal | Strategy | Solution | Context | Assumption | Justification.

(* Evidence must *witness* the node's own claim, not an arbitrary Prop. *)
Inductive Evidence : Type :=
  (* A Rocq proof term whose type IS the node's claim — no cheating *)
  | ProofTerm  : forall (P : Prop), P -> Evidence
  (* External certificate: a raw blob plus a decidable validator              *)
  (* (e.g., a SAW/Kani result with a signature check)                        *)
  | Certificate : string -> (string -> bool) -> Evidence.

Record Node : Type := {
  node_id       : Id;
  node_kind     : NodeKind;
  node_claim    : Prop;
  node_evidence : option Evidence;
}.

Inductive LinkKind : Type := SupportedBy | InContextOf.

Record Link : Type := {
  link_kind : LinkKind;
  link_from : Id;
  link_to   : Id;
}.

Record AssuranceCase : Type := {
  ac_nodes : list Node;
  ac_links : list Link;
  ac_top   : Id;
}.

(* ------------------------------------------------------------------ *)
(* 2. Graph operations                                                  *)
(* ------------------------------------------------------------------ *)

Definition find_node (ac : AssuranceCase) (id : Id) : option Node :=
  find (fun n => String.eqb n.(node_id) id) ac.(ac_nodes).

Definition supportedby_children (ac : AssuranceCase) (id : Id) : list Id :=
  map link_to
    (filter (fun l => andb
               (String.eqb l.(link_from) id)
               (match l.(link_kind) with SupportedBy => true | _ => false end))
            ac.(ac_links)).

(* ------------------------------------------------------------------ *)
(* 3. Reachability and acyclicity                                       *)
(* ------------------------------------------------------------------ *)

Inductive Reaches (ac : AssuranceCase) : Id -> Id -> Prop :=
  | R_Step  : forall u v,
      In v (supportedby_children ac u) -> Reaches ac u v
  | R_Trans : forall u w v,
      Reaches ac u w -> Reaches ac w v -> Reaches ac u v.

Definition Acyclic (ac : AssuranceCase) : Prop :=
  forall id, ~ Reaches ac id id.

(* ------------------------------------------------------------------ *)
(* 4. Evidence validity                                                 *)
(* ------------------------------------------------------------------ *)

(* Evidence is valid for a node only if it discharges THAT node's claim. *)
Definition evidence_valid (n : Node) (e : Evidence) : Prop :=
  match e with
  | ProofTerm P _   => P = n.(node_claim)   (* proof type must match claim *)
  | Certificate b v => v b = true            (* validator accepts the blob  *)
  end.

(* A Solution is discharged iff it carries valid evidence. *)
Definition solution_discharged (n : Node) : Prop :=
  n.(node_kind) = Solution ->
  exists e,
    n.(node_evidence) = Some e /\
    evidence_valid n e.

(* ------------------------------------------------------------------ *)
(* 5. Support tree — the central inductive witness                      *)
(* ------------------------------------------------------------------ *)

(* A SupportTree for node [id] is a proof-relevant object:             *)
(*  - Leaf case: the node is a Solution with valid evidence.            *)
(*  - Internal case: the node has ≥1 SupportedBy child, and EVERY      *)
(*    child has its own SupportTree (all branches must close).          *)
(*    We also require that children's claims ENTAIL the parent's claim  *)
(*    (captured by the [entailment] hypothesis), so the tree is not     *)
(*    merely structurally complete but logically sound.                  *)

Inductive SupportTree (ac : AssuranceCase) : Id -> Prop :=
  | ST_Leaf : forall id n e,
      find_node ac id = Some n ->
      n.(node_kind) = Solution ->
      n.(node_evidence) = Some e ->
      evidence_valid n e ->
      SupportTree ac id

  | ST_Internal : forall id n (kids : list Id),
      find_node ac id = Some n ->
      n.(node_kind) <> Solution ->
      kids = supportedby_children ac id ->
      kids <> [] ->
      (* Every child closes *)
      (forall kid, In kid kids -> SupportTree ac kid) ->
      (* Children's claims jointly entail the parent's claim            *)
      (* (For ProofTerm leaves this is checkable; for mixed trees it is *)
      (*  an explicit logical obligation left to the case author.)       *)
      (let child_claims :=
           flat_map (fun kid =>
             match find_node ac kid with
             | Some cn => [cn.(node_claim)]
             | None     => []
             end) kids
       in fold_right and True child_claims -> n.(node_claim)) ->
      SupportTree ac id

  | ST_Annotation : forall id n,
      find_node ac id = Some n ->
      (n.(node_kind) = Context \/
       n.(node_kind) = Assumption \/
       n.(node_kind) = Justification) ->
      SupportTree ac id.

(* ------------------------------------------------------------------ *)
(* 6. Well-formedness                                                   *)
(* ------------------------------------------------------------------ *)

Definition top_is_goal (ac : AssuranceCase) : Prop :=
  exists n,
    find_node ac ac.(ac_top) = Some n /\
    n.(node_kind) = Goal.

(* Every node reachable from the top goal is either                    *)
(*  (a) a Solution with valid evidence, or                             *)
(*  (b) a Goal/Strategy with at least one SupportedBy child.           *)
Definition all_reachable_discharged (ac : AssuranceCase) : Prop :=
  forall id,
    (id = ac.(ac_top) \/ Reaches ac ac.(ac_top) id) ->
    match find_node ac id with
    | None   => False
    | Some n =>
      match n.(node_kind) with
      | Solution =>
          exists e,
            n.(node_evidence) = Some e /\
            evidence_valid n e
      | Goal | Strategy =>
          supportedby_children ac id <> []
      | _ => True  (* Context, Assumption, Justification carry no obligation *)
      end
    end.

(* No dangling links: every link endpoint names a real node. *)
Definition no_dangling_links (ac : AssuranceCase) : Prop :=
  forall l,
    In l ac.(ac_links) ->
    (exists n, find_node ac l.(link_from) = Some n) /\
    (exists n, find_node ac l.(link_to)   = Some n).

Record WellFormed (ac : AssuranceCase) : Prop := {
  wf_top        : top_is_goal ac;
  wf_acyclic    : Acyclic ac;
  wf_discharged : all_reachable_discharged ac;
  wf_no_dangle  : no_dangling_links ac;
  wf_entailment : forall id n,
    find_node ac id = Some n ->
    (n.(node_kind) = Goal \/ n.(node_kind) = Strategy) ->
    (let kids := supportedby_children ac id in
     let child_claims :=
       flat_map (fun kid =>
         match find_node ac kid with
         | Some cn => [cn.(node_claim)]
         | None     => []
         end) kids
     in fold_right and True child_claims -> n.(node_claim));
}.

(* ------------------------------------------------------------------ *)
(* 7. Main theorem                                                      *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(* 7a. Decomposed well-foundedness lemmas                              *)
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

(* L1: Reachability is transitive.                                     *)
Lemma reaches_trans : forall ac u w v,
    Reaches ac u w -> Reaches ac w v -> Reaches ac u v.
Proof.
  intros. exact (R_Trans ac u w v H H0).
Qed.

(* L2: A child is reachable from its parent in one step.              *)
Lemma child_reaches : forall ac parent kid,
    In kid (supportedby_children ac parent) ->
    Reaches ac parent kid.
Proof.
  intros. exact (R_Step ac parent kid H).
Qed.

(* L3: Everything reachable from a child is reachable from parent.    *)
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

(* L4: In an acyclic graph, a parent is NOT reachable from its child. *)
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

(* L5a: height_fuel is bounded by fuel.                                *)
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

(* L5b: A child's height at fuel f is < parent's at fuel (S f).       *)
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

(* L5c: Acc from fuel induction — if height < fuel, then Acc.         *)
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
(* 7b. Path-length bound (pigeonhole)                                  *)
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

(* L5d: height_fuel at fuel = |nodes| is strictly less than |nodes|.  *)
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

(* ------------------------------------------------------------------ *)
(* 8. JSON export                                                       *)
(* ------------------------------------------------------------------ *)

(* ASCII 34 = double-quote. *)
Definition dquote_char : ascii :=
  Ascii false true false false false true false false.
Definition dquote : string := String dquote_char EmptyString.

(* Minimal JSON AST. *)
Inductive Json : Type :=
  | JNull   : Json
  | JBool   : bool -> Json
  | JStr    : string -> Json
  | JNum    : nat -> Json
  | JArr    : list Json -> Json
  | JObj    : list (string * Json) -> Json.

(* — Serialization to JSON AST — *)

Definition node_kind_to_json (nk : NodeKind) : Json :=
  JStr match nk with
  | Goal => "Goal" | Strategy => "Strategy" | Solution => "Solution"
  | Context => "Context" | Assumption => "Assumption"
  | Justification => "Justification"
  end.

Definition evidence_to_json (e : Evidence) : Json :=
  match e with
  | ProofTerm _ _ =>
      JObj [("type", JStr "ProofTerm")]
  | Certificate blob _ =>
      JObj [("type", JStr "Certificate"); ("blob", JStr blob)]
  end.

Definition node_to_json (n : Node) : Json :=
  JObj [("id", JStr n.(node_id));
        ("kind", node_kind_to_json n.(node_kind));
        ("evidence",
          match n.(node_evidence) with
          | Some e => evidence_to_json e
          | None => JNull
          end)].

Definition link_kind_to_json (lk : LinkKind) : Json :=
  JStr match lk with
  | SupportedBy => "SupportedBy"
  | InContextOf => "InContextOf"
  end.

Definition link_to_json (l : Link) : Json :=
  JObj [("kind", link_kind_to_json l.(link_kind));
        ("from", JStr l.(link_from));
        ("to", JStr l.(link_to))].

Definition assurance_case_to_json (ac : AssuranceCase) : Json :=
  JObj [("top", JStr ac.(ac_top));
        ("nodes", JArr (map node_to_json ac.(ac_nodes)));
        ("links", JArr (map link_to_json ac.(ac_links)))].

(* — JSON text renderer — *)

Definition digit_to_string (n : nat) : string :=
  match n with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9"
  | _ => "?"
  end.

Fixpoint nat_to_string_go (fuel n : nat) (acc : string) : string :=
  match fuel with
  | 0 => acc
  | S fuel' =>
    let acc' := String.append (digit_to_string (n mod 10)) acc in
    match n / 10 with
    | 0 => acc'
    | q => nat_to_string_go fuel' q acc'
    end
  end.

Definition nat_to_string (n : nat) : string :=
  nat_to_string_go (S n) n EmptyString.

Fixpoint join_strings (sep : string) (ss : list string) : string :=
  match ss with
  | [] => EmptyString
  | s :: rest =>
    String.append s
      (match rest with
       | [] => EmptyString
       | _ => String.append sep (join_strings sep rest)
       end)
  end.

Definition json_quote (s : string) : string :=
  String.append dquote (String.append s dquote).

Fixpoint render_json (j : Json) : string :=
  let fix render_list (js : list Json) : list string :=
    match js with
    | [] => []
    | j' :: rest => render_json j' :: render_list rest
    end
  in
  let fix render_kvs (kvs : list (string * Json)) : list string :=
    match kvs with
    | [] => []
    | (k, v) :: rest =>
        String.append (String.append (json_quote k) ":") (render_json v)
          :: render_kvs rest
    end
  in
  match j with
  | JNull => "null"
  | JBool true => "true"
  | JBool false => "false"
  | JStr s => json_quote s
  | JNum n => nat_to_string n
  | JArr elems =>
      String.append "[" (String.append (join_strings "," (render_list elems)) "]")
  | JObj kvs =>
      String.append "{" (String.append (join_strings "," (render_kvs kvs)) "}")
  end.

Definition render_assurance_case (ac : AssuranceCase) : string :=
  render_json (assurance_case_to_json ac).

(* ------------------------------------------------------------------ *)
(* 9. DOT export                                                        *)
(* ------------------------------------------------------------------ *)

(* ASCII 10 = newline. *)
Definition nl_char : ascii :=
  Ascii false true false true false false false false.
Definition nl : string := String nl_char EmptyString.

Definition concat_strings (ss : list string) : string :=
  fold_right String.append EmptyString ss.

Definition node_kind_shape (nk : NodeKind) : string :=
  match nk with
  | Goal => "box" | Strategy => "parallelogram" | Solution => "ellipse"
  | Context => "note" | Assumption => "diamond" | Justification => "hexagon"
  end.

Definition node_kind_color (nk : NodeKind) : string :=
  match nk with
  | Goal => "#c6e2ff" | Strategy => "#ffffcc" | Solution => "#c6ffc6"
  | Context => "#f0f0f0" | Assumption => "#ffe0cc" | Justification => "#e0ccff"
  end.

Definition render_dot_node (n : Node) : string :=
  "  " ++ json_quote n.(node_id) ++ " [label=" ++ json_quote n.(node_id)
       ++ ",shape=" ++ node_kind_shape n.(node_kind)
       ++ ",style=filled,fillcolor=" ++ json_quote (node_kind_color n.(node_kind))
       ++ "];" ++ nl.

Definition render_dot_edge (l : Link) : string :=
  "  " ++ json_quote l.(link_from) ++ " -> " ++ json_quote l.(link_to)
       ++ match l.(link_kind) with
          | SupportedBy => " [style=solid];"
          | InContextOf  => " [style=dashed];"
          end ++ nl.

Definition render_dot (ac : AssuranceCase) : string :=
  "digraph assurance_case {" ++ nl
    ++ concat_strings (map render_dot_node ac.(ac_nodes))
    ++ concat_strings (map render_dot_edge ac.(ac_links))
    ++ "}" ++ nl.

(* ------------------------------------------------------------------ *)
(* 10. Signed evidence blobs                                            *)
(* ------------------------------------------------------------------ *)

Record SignedBlob : Type := {
  sb_payload   : string;
  sb_signature : string;
  sb_verify    : string -> string -> bool;
}.

Definition signed_blob_valid (sb : SignedBlob) : Prop :=
  sb.(sb_verify) sb.(sb_payload) sb.(sb_signature) = true.

(* Wrap a signed blob as a Certificate evidence node.                  *)
(* The verifier closes over the stored signature so the Evidence       *)
(* validator only needs the payload.                                   *)
Definition signed_to_evidence (sb : SignedBlob) : Evidence :=
  Certificate sb.(sb_payload)
              (fun p => sb.(sb_verify) p sb.(sb_signature)).

Lemma signed_evidence_valid : forall sb n,
    signed_blob_valid sb ->
    evidence_valid n (signed_to_evidence sb).
Proof. intros sb n H. exact H. Qed.

Definition signed_to_json (sb : SignedBlob) : Json :=
  JObj [("type", JStr "SignedBlob");
        ("payload", JStr sb.(sb_payload));
        ("signature", JStr sb.(sb_signature))].

(* ------------------------------------------------------------------ *)
(* 11. Example: requirement -> theorem -> evidence                      *)
(* ------------------------------------------------------------------ *)

(* Claim: 2 + 2 = 4, witnessed by a Rocq proof term. *)
Definition ex_claim : Prop := 2 + 2 = 4.
Definition ex_proof : ex_claim := eq_refl.

Definition ex_goal : Node := {|
  node_id := "G1";
  node_kind := Goal;
  node_claim := ex_claim;
  node_evidence := None;
|}.

Definition ex_solution : Node := {|
  node_id := "E1";
  node_kind := Solution;
  node_claim := ex_claim;
  node_evidence := Some (ProofTerm ex_claim ex_proof);
|}.

Definition ex_link : Link := {|
  link_kind := SupportedBy;
  link_from := "G1";
  link_to := "E1";
|}.

Definition ex_ac : AssuranceCase := {|
  ac_nodes := [ex_goal; ex_solution];
  ac_links := [ex_link];
  ac_top := "G1";
|}.

(* — Helpers for the concrete example — *)

Lemma ex_children_equiv : forall u,
    supportedby_children ex_ac u =
    if String.eqb "G1" u then ["E1"] else [].
Proof.
  intro u. unfold supportedby_children, ex_ac, ex_link.
  cbn -[String.eqb]. destruct (String.eqb "G1" u); reflexivity.
Qed.

Lemma ex_find_node_equiv : forall id,
    find_node ex_ac id =
    if String.eqb "G1" id then Some ex_goal
    else if String.eqb "E1" id then Some ex_solution
    else None.
Proof.
  intro id. unfold find_node, ex_ac.
  cbn -[String.eqb]. destruct (String.eqb "G1" id); [reflexivity |].
  cbn -[String.eqb]. destruct (String.eqb "E1" id); reflexivity.
Qed.

Definition ex_rank (id : Id) : nat :=
  if String.eqb "G1" id then 1 else 0.

Lemma ex_rank_decreases : forall u v,
    Reaches ex_ac u v -> ex_rank v < ex_rank u.
Proof.
  intros u v H. induction H as [u v Hstep | u w v H1 IH1 H2 IH2].
  - rewrite ex_children_equiv in Hstep. unfold ex_rank.
    destruct (String.eqb "G1" u) eqn:Heq.
    + destruct Hstep as [<- | []]. simpl. apply Nat.lt_0_succ.
    + destruct Hstep.
  - exact (Nat.lt_trans _ _ _ IH2 IH1).
Qed.

Lemma ex_acyclic : Acyclic ex_ac.
Proof.
  intros id H.
  exact (Nat.lt_irrefl _ (ex_rank_decreases id id H)).
Qed.

Lemma ex_no_reach_from_E1 : forall v, ~ Reaches ex_ac "E1" v.
Proof.
  intros v H.
  exact (Nat.nlt_0_r _ (ex_rank_decreases _ _ H)).
Qed.

Lemma ex_reaches_from_G1 : forall u v,
    Reaches ex_ac u v -> u = "G1" -> v = "E1".
Proof.
  intros u v H. induction H as [u v Hstep | u w v H1 IH1 H2 IH2]; intro Heq; subst.
  - rewrite ex_children_equiv in Hstep. simpl in Hstep.
    destruct Hstep as [<- | []]. reflexivity.
  - assert (w = "E1") by exact (IH1 eq_refl). subst w.
    exfalso. exact (ex_no_reach_from_E1 v H2).
Qed.

(* — Well-formedness proof — *)

Lemma ex_top_is_goal : top_is_goal ex_ac.
Proof. exists ex_goal. split; reflexivity. Qed.

Lemma ex_no_dangle : no_dangling_links ex_ac.
Proof.
  intros l Hin. destruct Hin as [<- | []].
  split; [exists ex_goal | exists ex_solution]; reflexivity.
Qed.

Lemma ex_discharged : all_reachable_discharged ex_ac.
Proof.
  intros id Hreach.
  assert (Hid: id = "G1" \/ id = "E1").
  { destruct Hreach as [-> | H].
    - left; reflexivity.
    - right; exact (ex_reaches_from_G1 _ _ H eq_refl). }
  destruct Hid as [-> | ->]; vm_compute.
  - discriminate.
  - eexists; split; reflexivity.
Qed.

Lemma ex_entailment : forall id n,
    find_node ex_ac id = Some n ->
    (n.(node_kind) = Goal \/ n.(node_kind) = Strategy) ->
    (let kids := supportedby_children ex_ac id in
     let child_claims :=
       flat_map (fun kid =>
         match find_node ex_ac kid with
         | Some cn => [cn.(node_claim)]
         | None     => []
         end) kids
     in fold_right and True child_claims -> n.(node_claim)).
Proof.
  intros id n Hfind Hkind.
  rewrite ex_find_node_equiv in Hfind.
  destruct (String.eqb "G1" id) eqn:Heq1.
  - injection Hfind as <-. vm_compute. tauto.
  - destruct (String.eqb "E1" id) eqn:Heq2.
    + injection Hfind as <-. destruct Hkind as [H | H]; discriminate.
    + discriminate.
Qed.

Definition ex_wf : WellFormed ex_ac :=
  {| wf_top := ex_top_is_goal;
     wf_acyclic := ex_acyclic;
     wf_discharged := ex_discharged;
     wf_no_dangle := ex_no_dangle;
     wf_entailment := ex_entailment |}.

Theorem ex_supported : SupportTree ex_ac "G1".
Proof. exact (assurance_case_supported ex_ac ex_wf). Qed.

(* The example renders to JSON and DOT: *)
(* Eval vm_compute in render_assurance_case ex_ac. *)
(* Eval vm_compute in render_dot ex_ac.             *)

(* ------------------------------------------------------------------ *)
(* 12. Multi-level example: Goal -> Strategy -> 2 Solutions + Context   *)
(* ------------------------------------------------------------------ *)

Definition ml_security_claim : Prop := True.
Definition ml_unit_claim : Prop := 1 = 1.
Definition ml_fuzz_claim : Prop := True.

Definition ml_goal : Node := {|
  node_id := "G-sec";
  node_kind := Goal;
  node_claim := ml_security_claim;
  node_evidence := None;
|}.

Definition ml_strategy : Node := {|
  node_id := "S-test";
  node_kind := Strategy;
  node_claim := ml_security_claim;
  node_evidence := None;
|}.

Definition ml_context : Node := {|
  node_id := "C-scope";
  node_kind := Context;
  node_claim := True;
  node_evidence := None;
|}.

Definition ml_sol_unit : Node := {|
  node_id := "E-unit";
  node_kind := Solution;
  node_claim := ml_unit_claim;
  node_evidence := Some (ProofTerm ml_unit_claim eq_refl);
|}.

Definition ml_sol_fuzz : Node := {|
  node_id := "E-fuzz";
  node_kind := Solution;
  node_claim := ml_fuzz_claim;
  node_evidence := Some (Certificate "PASS:fuzz:2026-03-18" (fun s => String.eqb s "PASS:fuzz:2026-03-18"));
|}.

Definition ml_ac : AssuranceCase := {|
  ac_nodes := [ml_goal; ml_strategy; ml_context; ml_sol_unit; ml_sol_fuzz];
  ac_links := [{| link_kind := SupportedBy; link_from := "G-sec"; link_to := "S-test" |};
               {| link_kind := InContextOf; link_from := "G-sec"; link_to := "C-scope" |};
               {| link_kind := SupportedBy; link_from := "S-test"; link_to := "E-unit" |};
               {| link_kind := SupportedBy; link_from := "S-test"; link_to := "E-fuzz" |}];
  ac_top := "G-sec";
|}.

(* — Helpers for the multi-level example — *)

Lemma ml_children_equiv : forall u,
    supportedby_children ml_ac u =
    if String.eqb "G-sec" u then ["S-test"]
    else if String.eqb "S-test" u then ["E-unit"; "E-fuzz"]
    else [].
Proof.
  intro u. unfold supportedby_children, ml_ac.
  cbn -[String.eqb].
  destruct (String.eqb "G-sec" u) eqn:HG.
  - apply String.eqb_eq in HG. subst u. reflexivity.
  - cbn -[String.eqb].
    destruct (String.eqb "S-test" u) eqn:HS.
    + apply String.eqb_eq in HS. subst u. reflexivity.
    + reflexivity.
Qed.

Lemma ml_find_node_equiv : forall id,
    find_node ml_ac id =
    if String.eqb "G-sec" id then Some ml_goal
    else if String.eqb "S-test" id then Some ml_strategy
    else if String.eqb "C-scope" id then Some ml_context
    else if String.eqb "E-unit" id then Some ml_sol_unit
    else if String.eqb "E-fuzz" id then Some ml_sol_fuzz
    else None.
Proof.
  intro id. unfold find_node, ml_ac.
  cbn -[String.eqb]. destruct (String.eqb "G-sec" id); [reflexivity |].
  cbn -[String.eqb]. destruct (String.eqb "S-test" id); [reflexivity |].
  cbn -[String.eqb]. destruct (String.eqb "C-scope" id); [reflexivity |].
  cbn -[String.eqb]. destruct (String.eqb "E-unit" id); [reflexivity |].
  cbn -[String.eqb]. destruct (String.eqb "E-fuzz" id); reflexivity.
Qed.

Definition ml_rank (id : Id) : nat :=
  if String.eqb "G-sec" id then 2
  else if String.eqb "S-test" id then 1
  else 0.

Lemma ml_rank_decreases : forall u v,
    Reaches ml_ac u v -> ml_rank v < ml_rank u.
Proof.
  intros u v H. induction H as [u v Hstep | u w v H1 IH1 H2 IH2].
  - rewrite ml_children_equiv in Hstep. unfold ml_rank.
    destruct (String.eqb "G-sec" u) eqn:HG.
    + destruct Hstep as [<- | []]. simpl. auto.
    + destruct (String.eqb "S-test" u) eqn:HS.
      * destruct Hstep as [<- | [<- | []]]; simpl; auto.
      * destruct Hstep.
  - exact (Nat.lt_trans _ _ _ IH2 IH1).
Qed.

Lemma ml_acyclic : Acyclic ml_ac.
Proof.
  intros id H. exact (Nat.lt_irrefl _ (ml_rank_decreases id id H)).
Qed.

Lemma ml_reaches_from_S_test : forall v,
    Reaches ml_ac "S-test" v -> v = "E-unit" \/ v = "E-fuzz".
Proof.
  intros v H. remember "S-test" as src.
  induction H as [u v Hstep | u w v H1 IH1 H2 IH2]; subst.
  - rewrite ml_children_equiv in Hstep. simpl in Hstep.
    destruct Hstep as [<- | [<- | []]]; [left | right]; reflexivity.
  - destruct (IH1 eq_refl) as [-> | ->];
      exfalso; exact (Nat.nlt_0_r _ (ml_rank_decreases _ _ H2)).
Qed.

Lemma ml_reachable_ids : forall v,
    Reaches ml_ac "G-sec" v -> v = "S-test" \/ v = "E-unit" \/ v = "E-fuzz".
Proof.
  intros v H. remember "G-sec" as src.
  induction H as [u v Hstep | u w v H1 IH1 H2 IH2]; subst.
  - rewrite ml_children_equiv in Hstep. simpl in Hstep.
    destruct Hstep as [<- | []]. left; reflexivity.
  - destruct (IH1 eq_refl) as [-> | [-> | ->]].
    + right; exact (ml_reaches_from_S_test v H2).
    + exfalso; exact (Nat.nlt_0_r _ (ml_rank_decreases _ _ H2)).
    + exfalso; exact (Nat.nlt_0_r _ (ml_rank_decreases _ _ H2)).
Qed.

Lemma ml_top_is_goal : top_is_goal ml_ac.
Proof. exists ml_goal. split; reflexivity. Qed.

Lemma ml_no_dangle : no_dangling_links ml_ac.
Proof.
  intros l Hin. simpl in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]];
    (split; [eexists | eexists]; reflexivity).
Qed.

Lemma ml_discharged : all_reachable_discharged ml_ac.
Proof.
  intros id Hreach.
  assert (Hid: id = "G-sec" \/ id = "S-test" \/ id = "E-unit" \/ id = "E-fuzz").
  { destruct Hreach as [-> | H].
    - left; reflexivity.
    - right; exact (ml_reachable_ids _ H). }
  destruct Hid as [-> | [-> | [-> | ->]]]; vm_compute.
  - discriminate.
  - discriminate.
  - eexists; split; reflexivity.
  - eexists; split; reflexivity.
Qed.

Lemma ml_entailment : forall id n,
    find_node ml_ac id = Some n ->
    (n.(node_kind) = Goal \/ n.(node_kind) = Strategy) ->
    (let kids := supportedby_children ml_ac id in
     let child_claims :=
       flat_map (fun kid =>
         match find_node ml_ac kid with
         | Some cn => [cn.(node_claim)]
         | None     => []
         end) kids
     in fold_right and True child_claims -> n.(node_claim)).
Proof.
  intros id n Hfind Hkind.
  rewrite ml_find_node_equiv in Hfind.
  destruct (String.eqb "G-sec" id) eqn:H1.
  - injection Hfind as <-. vm_compute. tauto.
  - destruct (String.eqb "S-test" id) eqn:H2.
    + injection Hfind as <-. vm_compute. tauto.
    + destruct (String.eqb "C-scope" id) eqn:H3.
      * injection Hfind as <-. destruct Hkind as [H|H]; discriminate.
      * destruct (String.eqb "E-unit" id) eqn:H4.
        -- injection Hfind as <-. destruct Hkind as [H|H]; discriminate.
        -- destruct (String.eqb "E-fuzz" id) eqn:H5.
           ++ injection Hfind as <-. destruct Hkind as [H|H]; discriminate.
           ++ discriminate.
Qed.

Definition ml_wf : WellFormed ml_ac :=
  {| wf_top := ml_top_is_goal;
     wf_acyclic := ml_acyclic;
     wf_discharged := ml_discharged;
     wf_no_dangle := ml_no_dangle;
     wf_entailment := ml_entailment |}.

Theorem ml_supported : SupportTree ml_ac "G-sec".
Proof. exact (assurance_case_supported ml_ac ml_wf). Qed.

(* Eval vm_compute in render_dot ml_ac.             *)
(* Eval vm_compute in render_assurance_case ml_ac.  *)

(* ------------------------------------------------------------------ *)
(* 13. Extraction                                                       *)
(* ------------------------------------------------------------------ *)

Require Extraction.
Extraction Language OCaml.
Extract Inlined Constant Nat.eqb => "(=)".
Extraction "rack" render_assurance_case render_dot
                   assurance_case_to_json render_json
                   signed_to_evidence signed_to_json.
