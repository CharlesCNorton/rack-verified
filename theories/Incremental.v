(* ------------------------------------------------------------------ *)
(* Incremental checking with indexed data structures                   *)
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
(* Indexed assurance case                                              *)
(* ================================================================== *)

(** An [IndexedAC] wraps an [AssuranceCase] with precomputed indices
    for O(n) worst-case amortized lookup (vs O(n) per lookup without).
    For O(log n), substitute a balanced map; the refinement proofs
    below show the indexed version agrees with the naive version. *)
Record IndexedAC : Type := {
  iac_case       : AssuranceCase;
  iac_node_index : list (Id * Node);
  iac_child_index : list (Id * list Id);
}.

(** Build an indexed case from a plain case. *)
Definition build_indexed (ac : AssuranceCase) : IndexedAC := {|
  iac_case := ac;
  iac_node_index := build_node_index ac;
  iac_child_index := map (fun n =>
    (n.(node_id), supportedby_children ac n.(node_id)))
    ac.(ac_nodes);
|}.

(** Indexed node lookup. *)
Definition iac_find_node (iac : IndexedAC) (id : Id)
  : option Node :=
  find_node_indexed iac.(iac_node_index) id.

(** Indexed children lookup. *)
Fixpoint iac_assoc_find (id : Id) (idx : list (Id * list Id))
  : option (list Id) :=
  match idx with
  | [] => None
  | (k, v) :: rest =>
    if String.eqb k id then Some v
    else iac_assoc_find id rest
  end.

Definition iac_children (iac : IndexedAC) (id : Id)
  : list Id :=
  match iac_assoc_find id iac.(iac_child_index) with
  | Some kids => kids
  | None => []
  end.

(* ================================================================== *)
(* Refinement proofs                                                   *)
(* ================================================================== *)

(** The indexed node lookup agrees with the naive lookup. *)
Theorem iac_find_node_correct : forall ac id,
    iac_find_node (build_indexed ac) id = find_node ac id.
Proof.
  intros ac id. unfold iac_find_node, build_indexed. simpl.
  exact (find_node_indexed_correct ac id).
Qed.

(** The indexed children lookup agrees with the naive lookup. *)
Lemma iac_children_correct_go : forall ac nodes id,
    (forall n, In n nodes -> In n ac.(ac_nodes)) ->
    NoDup (map node_id nodes) ->
    In id (map node_id nodes) ->
    iac_assoc_find id
      (map (fun n => (n.(node_id), supportedby_children ac n.(node_id))) nodes) =
    Some (supportedby_children ac id).
Proof.
  intros ac nodes id Hsub Hnd Hin.
  induction nodes as [|n ns IH]; simpl.
  - destruct Hin.
  - inversion Hnd as [| ? ? Hna Hnd']; subst.
    destruct (String.eqb n.(node_id) id) eqn:Heq.
    + apply String.eqb_eq in Heq. rewrite Heq. reflexivity.
    + apply IH.
      * intros n0 Hn0. apply Hsub. right. exact Hn0.
      * exact Hnd'.
      * destruct Hin as [Hin | Hin].
        -- rewrite Hin in Heq. rewrite String.eqb_refl in Heq.
           discriminate.
        -- exact Hin.
Qed.

(* ================================================================== *)
(* Incremental single-node check                                       *)
(* ================================================================== *)

(** Check a single node after it's been added or updated.
    Uses the indexed case for efficient node lookups.
    Children are computed from the case's links (the index
    optimizes node lookup, not child enumeration). *)
Definition iac_check_node (iac : IndexedAC) (id : Id) : bool :=
  match iac_find_node iac id with
  | None => false
  | Some n =>
    match n.(node_kind) with
    | Solution =>
      match n.(node_evidence) with
      | Some (ProofTerm _ _ _ _) => true
      | Some (Certificate b _ v) => v b
      | None => false
      end
    | Goal | Strategy =>
      negb (match supportedby_children iac.(iac_case) id with
            | [] => true | _ => false end)
    | _ => true
    end
  end.

(** The incremental check agrees with the full check. *)
Theorem iac_check_node_correct : forall ac id,
    iac_check_node (build_indexed ac) id = check_node ac id.
Proof.
  intros ac id. unfold iac_check_node, check_node.
  rewrite iac_find_node_correct. reflexivity.
Qed.

(** Check a single link after it's been added. *)
Definition iac_check_link (iac : IndexedAC) (l : Link) : bool :=
  match iac_find_node iac l.(link_from),
        iac_find_node iac l.(link_to) with
  | Some nf, Some nt =>
    match l.(link_kind) with
    | SupportedBy => true
    | InContextOf =>
      (match nf.(node_kind) with Goal | Strategy => true | _ => false end) &&
      (match nt.(node_kind) with
       | Context | Assumption | Justification => true | _ => false end)
    | Defeater =>
      match nt.(node_kind) with Goal | Strategy => true | _ => false end
    end
  | _, _ => false
  end.

(** The incremental link check agrees with the full check. *)
Theorem iac_check_link_correct : forall ac l,
    iac_check_link (build_indexed ac) l = check_link ac l.
Proof.
  intros ac l. unfold iac_check_link, check_link.
  repeat rewrite iac_find_node_correct. reflexivity.
Qed.

(* ================================================================== *)
(* Batch incremental checking                                          *)
(* ================================================================== *)

(** Check a batch of nodes (e.g., after a delta is applied). *)
Definition iac_check_nodes (iac : IndexedAC) (ids : list Id) : bool :=
  forallb (iac_check_node iac) ids.

(** Check a batch of links. *)
Definition iac_check_links (iac : IndexedAC) (links : list Link) : bool :=
  forallb (iac_check_link iac) links.

(* ================================================================== *)
(* Top-level indexed children correctness theorem                     *)
(* ================================================================== *)

Theorem iac_children_correct : forall ac id,
    NoDup (map node_id ac.(ac_nodes)) ->
    In id (map node_id ac.(ac_nodes)) ->
    iac_children (build_indexed ac) id = supportedby_children ac id.
Proof.
  intros ac id Hnd Hin.
  unfold iac_children, build_indexed. simpl.
  rewrite (iac_children_correct_go ac ac.(ac_nodes) id
             (fun n H => H) Hnd Hin).
  reflexivity.
Qed.

(* ================================================================== *)
(* BST-backed node index with refinement proof                        *)
(* ================================================================== *)

(** Unbalanced BST keyed by string.  For O(log n) average-case
    lookup.  Plug in a balanced variant (AVL, RB) for guaranteed
    O(log n); the refinement proof below transfers unchanged. *)
Inductive NodeBST : Type :=
  | BSTLeaf : NodeBST
  | BSTNode : NodeBST -> Id -> Node -> NodeBST -> NodeBST.

Fixpoint bst_insert (id : Id) (n : Node) (t : NodeBST) : NodeBST :=
  match t with
  | BSTLeaf => BSTNode BSTLeaf id n BSTLeaf
  | BSTNode l k v r =>
    match String.compare id k with
    | Lt => BSTNode (bst_insert id n l) k v r
    | Eq => BSTNode l id n r
    | Gt => BSTNode l k v (bst_insert id n r)
    end
  end.

Fixpoint bst_find (id : Id) (t : NodeBST) : option Node :=
  match t with
  | BSTLeaf => None
  | BSTNode l k v r =>
    match String.compare id k with
    | Lt => bst_find id l
    | Eq => Some v
    | Gt => bst_find id r
    end
  end.

Definition build_bst_index (ac : AssuranceCase) : NodeBST :=
  fold_left (fun t n => bst_insert n.(node_id) n t)
            ac.(ac_nodes) BSTLeaf.

Definition find_node_bst (t : NodeBST) (id : Id) : option Node :=
  bst_find id t.

(** BST ordering invariant: all keys in the left subtree are Lt,
    all keys in the right subtree are Gt. *)
Inductive BST_ordered : NodeBST -> Prop :=
  | BST_leaf : BST_ordered BSTLeaf
  | BST_node : forall l k v r,
      BST_ordered l -> BST_ordered r ->
      (forall id n, bst_find id l = Some n ->
        String.compare id k = Lt) ->
      (forall id n, bst_find id r = Some n ->
        String.compare id k = Gt) ->
      BST_ordered (BSTNode l k v r).

(** Boolean check: the BST agrees with find_node for all node IDs. *)
Definition check_bst_refines (ac : AssuranceCase) : bool :=
  let t := build_bst_index ac in
  forallb (fun n =>
    match find_node_bst t n.(node_id), find_node ac n.(node_id) with
    | Some n1, Some n2 =>
      String.eqb n1.(node_id) n2.(node_id) &&
      NodeKind_eqb n1.(node_kind) n2.(node_kind) &&
      String.eqb n1.(node_claim_text) n2.(node_claim_text)
    | None, None => true
    | _, _ => false
    end) ac.(ac_nodes).

(** Soundness: when the BST insert uses only keys from the node
    list, bst_find returns the same node_id as find_node. *)
(** Reflexivity of String.compare, derived from compare_antisym. *)
Lemma string_compare_refl : forall s, String.compare s s = Eq.
Proof.
  intro s. destruct (String.compare s s) eqn:H.
  - reflexivity.
  - pose proof (String.compare_antisym s s) as Ha.
    rewrite H in Ha. simpl in Ha.
    rewrite Ha in H. discriminate.
  - pose proof (String.compare_antisym s s) as Ha.
    rewrite H in Ha. simpl in Ha.
    rewrite Ha in H. discriminate.
Qed.

Opaque String.compare.

(** [bst_insert] then [bst_find] with the same key returns the value. *)
Lemma bst_insert_find : forall id n t,
    bst_find id (bst_insert id n t) = Some n.
Proof.
  intros id n t. induction t as [| l IHl k v r IHr]; simpl.
  - rewrite string_compare_refl. reflexivity.
  - destruct (String.compare id k) eqn:Hcmp; simpl.
    + apply String.compare_eq_iff in Hcmp. subst k.
      rewrite string_compare_refl. reflexivity.
    + rewrite Hcmp. exact IHl.
    + rewrite Hcmp. exact IHr.
Qed.

(** [bst_insert] preserves lookups for other keys. *)
Lemma bst_insert_find_other : forall id id0 n t,
    String.compare id id0 <> Eq ->
    bst_find id0 (bst_insert id n t) = bst_find id0 t.
Proof.
  intros id id0 n t Hne.
  induction t as [| l IHl k v r IHr]; simpl.
  - destruct (String.compare id id0) eqn:Ho; simpl.
    + exfalso. exact (Hne eq_refl).
    + destruct (String.compare id0 id) eqn:Hi; try reflexivity.
      exfalso. apply String.compare_eq_iff in Hi. subst.
      rewrite string_compare_refl in Ho. discriminate.
    + destruct (String.compare id0 id) eqn:Hi; try reflexivity.
      exfalso. apply String.compare_eq_iff in Hi. subst.
      rewrite string_compare_refl in Ho. discriminate.
  - destruct (String.compare id k) eqn:Hcmp1; simpl.
    + apply String.compare_eq_iff in Hcmp1. subst k.
      destruct (String.compare id0 id) eqn:Hcmp2; try reflexivity.
      exfalso. apply Hne. apply String.compare_eq_iff in Hcmp2.
      subst. exact (string_compare_refl id).
    + destruct (String.compare id0 k); try exact IHl; reflexivity.
    + destruct (String.compare id0 k); try exact IHr; reflexivity.
Qed.

(** BST refinement: [build_bst_index] agrees with [find_node]. *)
Lemma fold_bst_insert_correct : forall ns t id,
    NoDup (map node_id ns) ->
    bst_find id (fold_left (fun t0 n0 => bst_insert n0.(node_id) n0 t0)
                            ns t) =
    match find (fun n0 => String.eqb n0.(node_id) id) ns with
    | Some n0 => Some n0
    | None => bst_find id t
    end.
Proof.
  induction ns as [| n0 rest IH]; intros t id Hnd; simpl.
  - reflexivity.
  - inversion Hnd as [| ? ? Hna Hnd']; subst.
    rewrite IH; try exact Hnd'.
    destruct (String.eqb n0.(node_id) id) eqn:Heq.
    + apply String.eqb_eq in Heq. subst.
      destruct (find (fun n1 => String.eqb n1.(node_id) n0.(node_id)) rest) eqn:Hf.
      * rename n into found.
        apply find_some in Hf. destruct Hf as [Hin Heqb].
        apply String.eqb_eq in Heqb.
        exfalso. apply Hna. apply in_map_iff.
        exists found. exact (conj Heqb Hin).
      * rewrite bst_insert_find. reflexivity.
    + destruct (find (fun n1 => String.eqb n1.(node_id) id) rest);
        try reflexivity.
      rewrite bst_insert_find_other; try reflexivity.
      intro Habs. apply String.compare_eq_iff in Habs.
      rewrite Habs in Heq. rewrite String.eqb_refl in Heq. discriminate.
Qed.

Transparent String.compare.

Theorem build_bst_index_correct : forall ac id,
    NoDup (map node_id ac.(ac_nodes)) ->
    find_node_bst (build_bst_index ac) id = find_node ac id.
Proof.
  intros ac id Hnd.
  unfold find_node_bst, build_bst_index, find_node.
  rewrite fold_bst_insert_correct; try exact Hnd.
  destruct (find (fun n => String.eqb n.(node_id) id) ac.(ac_nodes));
    reflexivity.
Qed.

(* ================================================================== *)
(* BST ordering proof for build_bst_index                              *)
(* ================================================================== *)

Lemma fold_left_preserves : forall {A B : Type} (f : A -> B -> A)
    (P : A -> Prop) (l : list B) (a : A),
    P a -> (forall a' b, P a' -> P (f a' b)) ->
    P (fold_left f l a).
Proof.
  intros A B f P l. induction l as [|x xs IH]; intros a Hp Hstep; simpl.
  - exact Hp.
  - exact (IH (f a x) (Hstep a x Hp) Hstep).
Qed.

Opaque String.compare.

Lemma bst_insert_keys_lt : forall id n t bound,
    (forall id' n', bst_find id' t = Some n' ->
      String.compare id' bound = Lt) ->
    String.compare id bound = Lt ->
    forall id' n', bst_find id' (bst_insert id n t) = Some n' ->
    String.compare id' bound = Lt.
Proof.
  intros id n t bound Hkeys Hid id' n' Hfind.
  destruct (String.compare id id') eqn:Hcmp.
  - apply String.compare_eq_iff in Hcmp. subst.
    rewrite bst_insert_find in Hfind. injection Hfind as <-. exact Hid.
  - rewrite bst_insert_find_other in Hfind;
      [exact (Hkeys id' n' Hfind) | rewrite Hcmp; discriminate].
  - rewrite bst_insert_find_other in Hfind;
      [exact (Hkeys id' n' Hfind) | rewrite Hcmp; discriminate].
Qed.

Lemma bst_insert_keys_gt : forall id n t bound,
    (forall id' n', bst_find id' t = Some n' ->
      String.compare id' bound = Gt) ->
    String.compare id bound = Gt ->
    forall id' n', bst_find id' (bst_insert id n t) = Some n' ->
    String.compare id' bound = Gt.
Proof.
  intros id n t bound Hkeys Hid id' n' Hfind.
  destruct (String.compare id id') eqn:Hcmp.
  - apply String.compare_eq_iff in Hcmp. subst.
    rewrite bst_insert_find in Hfind. injection Hfind as <-. exact Hid.
  - rewrite bst_insert_find_other in Hfind;
      [exact (Hkeys id' n' Hfind) | rewrite Hcmp; discriminate].
  - rewrite bst_insert_find_other in Hfind;
      [exact (Hkeys id' n' Hfind) | rewrite Hcmp; discriminate].
Qed.

Lemma bst_insert_preserves_ordered : forall id n t,
    BST_ordered t -> BST_ordered (bst_insert id n t).
Proof.
  intros id n t. induction t as [|l IHl k v r IHr]; intro Hord.
  - simpl. constructor; try constructor;
      intros id' n' Hf; simpl in Hf; discriminate.
  - inversion Hord as [|? ? ? ? Hl Hr Hkl Hkr]; subst.
    simpl. destruct (String.compare id k) eqn:Hcmp.
    + apply String.compare_eq_iff in Hcmp. subst.
      constructor; assumption.
    + constructor; [exact (IHl Hl) | exact Hr |
        exact (bst_insert_keys_lt id n l k Hkl Hcmp) | exact Hkr].
    + constructor; [exact Hl | exact (IHr Hr) |
        exact Hkl | exact (bst_insert_keys_gt id n r k Hkr Hcmp)].
Qed.

Transparent String.compare.

Theorem build_bst_index_ordered : forall ac,
    BST_ordered (build_bst_index ac).
Proof.
  intro ac. unfold build_bst_index.
  exact (fold_left_preserves _ BST_ordered ac.(ac_nodes) BSTLeaf
           BST_leaf
           (fun t n H => bst_insert_preserves_ordered n.(node_id) n t H)).
Qed.

(* ================================================================== *)
(* AVL-backed node index                                               *)
(* ================================================================== *)

Inductive NodeAVL : Type :=
  | AVLLeaf : NodeAVL
  | AVLNode : NodeAVL -> Id -> Node -> NodeAVL -> nat -> NodeAVL.

Definition avl_height (t : NodeAVL) : nat :=
  match t with AVLLeaf => 0 | AVLNode _ _ _ _ h => h end.

Definition avl_mk (l : NodeAVL) (k : Id) (v : Node)
    (r : NodeAVL) : NodeAVL :=
  AVLNode l k v r (S (Nat.max (avl_height l) (avl_height r))).

Definition avl_rot_right (t : NodeAVL) : NodeAVL :=
  match t with
  | AVLNode (AVLNode ll lk lv lr _) k v r _ =>
    avl_mk ll lk lv (avl_mk lr k v r)
  | _ => t
  end.

Definition avl_rot_left (t : NodeAVL) : NodeAVL :=
  match t with
  | AVLNode l k v (AVLNode rl rk rv rr _) _ =>
    avl_mk (avl_mk l k v rl) rk rv rr
  | _ => t
  end.

Definition avl_balance (l : NodeAVL) (k : Id) (v : Node)
    (r : NodeAVL) : NodeAVL :=
  let hl := avl_height l in
  let hr := avl_height r in
  if Nat.leb (hr + 2) hl then
    match l with
    | AVLNode ll _ _ lr _ =>
      if Nat.leb (avl_height lr) (avl_height ll) then
        avl_rot_right (avl_mk l k v r)
      else avl_rot_right (avl_mk (avl_rot_left l) k v r)
    | AVLLeaf => avl_mk l k v r
    end
  else if Nat.leb (hl + 2) hr then
    match r with
    | AVLNode rl _ _ rr _ =>
      if Nat.leb (avl_height rl) (avl_height rr) then
        avl_rot_left (avl_mk l k v r)
      else avl_rot_left (avl_mk l k v (avl_rot_right r))
    | AVLLeaf => avl_mk l k v r
    end
  else avl_mk l k v r.

Fixpoint avl_insert (id : Id) (n : Node) (t : NodeAVL) : NodeAVL :=
  match t with
  | AVLLeaf => AVLNode AVLLeaf id n AVLLeaf 1
  | AVLNode l k v r h =>
    match String.compare id k with
    | Lt => avl_balance (avl_insert id n l) k v r
    | Eq => AVLNode l id n r h
    | Gt => avl_balance l k v (avl_insert id n r)
    end
  end.

Fixpoint avl_find (id : Id) (t : NodeAVL) : option Node :=
  match t with
  | AVLLeaf => None
  | AVLNode l k v r _ =>
    match String.compare id k with
    | Lt => avl_find id l | Eq => Some v | Gt => avl_find id r
    end
  end.

Definition build_avl_index (ac : AssuranceCase) : NodeAVL :=
  fold_left (fun t n => avl_insert n.(node_id) n t)
            ac.(ac_nodes) AVLLeaf.

Definition find_node_avl (t : NodeAVL) (id : Id) : option Node :=
  avl_find id t.

(* --- In-order element list (rotation-invariant) --- *)

Fixpoint avl_elements (t : NodeAVL) : list (Id * Node) :=
  match t with
  | AVLLeaf => []
  | AVLNode l k v r _ => avl_elements l ++ [(k, v)] ++ avl_elements r
  end.

Arguments avl_elements : simpl never.
Arguments avl_height : simpl never.

Lemma avl_elements_node : forall l k v r h,
    avl_elements (AVLNode l k v r h) =
    avl_elements l ++ [(k, v)] ++ avl_elements r.
Proof. reflexivity. Qed.

Lemma avl_elements_leaf : avl_elements AVLLeaf = [].
Proof. reflexivity. Qed.

Lemma avl_balance_elements : forall l k v r,
    avl_elements (avl_balance l k v r) =
    avl_elements l ++ [(k, v)] ++ avl_elements r.
Proof.
  intros l k v r. unfold avl_balance, avl_rot_right, avl_rot_left, avl_mk.
  destruct (Nat.leb (avl_height r + 2) (avl_height l)) eqn:E1.
  - destruct l as [|ll lk lv lr lh]; [reflexivity |].
    destruct (Nat.leb (avl_height lr) (avl_height ll)) eqn:E2.
    + rewrite !avl_elements_node; rewrite !app_assoc; reflexivity.
    + destruct lr as [|lrl lrk lrv lrr lrh];
        rewrite !avl_elements_node; rewrite !app_assoc; reflexivity.
  - destruct (Nat.leb (avl_height l + 2) (avl_height r)) eqn:E3.
    + destruct r as [|rl rk rv rr rh]; [reflexivity |].
      destruct (Nat.leb (avl_height rl) (avl_height rr)) eqn:E4.
      * rewrite !avl_elements_node; rewrite !app_assoc; reflexivity.
      * destruct rl as [|rll rlk rlv rlr rlh];
          rewrite !avl_elements_node; rewrite !app_assoc; reflexivity.
    + rewrite avl_elements_node. reflexivity.
Qed.

(* --- AVL ordering invariant --- *)

Inductive AVL_ordered : NodeAVL -> Prop :=
  | AVLO_leaf : AVL_ordered AVLLeaf
  | AVLO_node : forall l k v r h,
      AVL_ordered l -> AVL_ordered r ->
      (forall id n, avl_find id l = Some n ->
        String.compare id k = Lt) ->
      (forall id n, avl_find id r = Some n ->
        String.compare id k = Gt) ->
      AVL_ordered (AVLNode l k v r h).

(* --- AVL balance invariant --- *)

Inductive AVL_balanced : NodeAVL -> Prop :=
  | AVLB_leaf : AVL_balanced AVLLeaf
  | AVLB_node : forall l k v r h,
      AVL_balanced l -> AVL_balanced r ->
      h = S (Nat.max (avl_height l) (avl_height r)) ->
      avl_height l <= avl_height r + 1 ->
      avl_height r <= avl_height l + 1 ->
      AVL_balanced (AVLNode l k v r h).

(* --- Boolean refinement check (concrete cases) --- *)

Definition check_avl_refines (ac : AssuranceCase) : bool :=
  let t := build_avl_index ac in
  forallb (fun n =>
    match find_node_avl t n.(node_id), find_node ac n.(node_id) with
    | Some n1, Some n2 =>
      String.eqb n1.(node_id) n2.(node_id) &&
      NodeKind_eqb n1.(node_kind) n2.(node_kind) &&
      String.eqb n1.(node_claim_text) n2.(node_claim_text)
    | None, None => true
    | _, _ => false
    end) ac.(ac_nodes).
