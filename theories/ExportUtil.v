(* ------------------------------------------------------------------ *)
(* JSON importer, hydrate, auto_hydrate, rebuild_claims, streaming      *)
(* ------------------------------------------------------------------ *)

From RACK Require Import Core.
From RACK Require Import Json.
From RACK Require Import Dot.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(* JSON to AssuranceCase importer                                       *)
(* ------------------------------------------------------------------ *)

(* Look up a key in a JSON object's key-value list.                    *)
Fixpoint json_field (key : string) (kvs : list (string * Json))
  : option Json :=
  match kvs with
  | nil => None
  | (k, v) :: rest =>
    if String.eqb k key then Some v else json_field key rest
  end.

Definition json_to_node_kind (j : Json) : option NodeKind :=
  match j with
  | JStr s =>
    if String.eqb s "Goal" then Some Goal
    else if String.eqb s "Strategy" then Some Strategy
    else if String.eqb s "Solution" then Some Solution
    else if String.eqb s "Context" then Some Context
    else if String.eqb s "Assumption" then Some Assumption
    else if String.eqb s "Justification" then Some Justification
    else None
  | _ => None
  end.

Definition json_to_link_kind (j : Json) : option LinkKind :=
  match j with
  | JStr s =>
    if String.eqb s "SupportedBy" then Some SupportedBy
    else if String.eqb s "InContextOf" then Some InContextOf
    else if String.eqb s "Defeater" then Some Defeater
    else None
  | _ => None
  end.

(* Reconstruct a node from JSON.  Evidence and logical claims cannot
   be recovered (ProofTerm proofs are erased, Certificate validators
   are functions).  All parsed nodes get evidence = None and
   claim = True.  Use hydrate_evidence to re-attach evidence.          *)
Definition json_to_node (j : Json) : option Node :=
  match j with
  | JObj kvs =>
    match json_field "id" kvs, json_field "kind" kvs with
    | Some (JStr id), Some kind_json =>
      match json_to_node_kind kind_json with
      | Some nk =>
        let claim_text := match json_field "claim" kvs with
                          | Some (JStr s) => s
                          | _ => EmptyString
                          end in
        let md := match json_field "metadata" kvs with
                  | Some (JObj mkvs) =>
                    flat_map (fun kv =>
                      match snd kv with
                      | JStr v  => [(fst kv, MVString v)]
                      | JNum n  => [(fst kv, MVNat n)]
                      | JBool b => [(fst kv, MVBool b)]
                      | _       => []
                      end) mkvs
                  | _ => []
                  end in
        Some {| node_id := id;
                node_kind := nk;
                node_claim_text := claim_text;
                node_evidence := None;
                node_metadata := md;
                node_claim := True |}
      | None => None
      end
    | _, _ => None
    end
  | _ => None
  end.

Definition json_to_link (j : Json) : option Link :=
  match j with
  | JObj kvs =>
    match json_field "kind" kvs,
          json_field "from" kvs,
          json_field "to" kvs with
    | Some kind_json, Some (JStr from_id), Some (JStr to_id) =>
      match json_to_link_kind kind_json with
      | Some lk =>
        Some {| link_kind := lk;
                link_from := from_id;
                link_to := to_id |}
      | None => None
      end
    | _, _, _ => None
    end
  | _ => None
  end.

Fixpoint json_list_map {A : Type} (f : Json -> option A)
    (js : list Json) : option (list A) :=
  match js with
  | nil => Some nil
  | j :: rest =>
    match f j, json_list_map f rest with
    | Some a, Some as_ => Some (a :: as_)
    | _, _ => None
    end
  end.

Definition json_to_assurance_case (j : Json) : option AssuranceCase :=
  match j with
  | JObj kvs =>
    match json_field "top" kvs,
          json_field "nodes" kvs,
          json_field "links" kvs with
    | Some (JStr top_id), Some (JArr node_jsons), Some (JArr link_jsons) =>
      match json_list_map json_to_node node_jsons,
            json_list_map json_to_link link_jsons with
      | Some nodes, Some links =>
        Some {| ac_nodes := nodes; ac_links := links; ac_top := top_id |}
      | _, _ => None
      end
    | _, _, _ => None
    end
  | _ => None
  end.

(* Re-attach evidence to parsed nodes.  The mapping provides
   evidence for each node ID.  Nodes not in the mapping keep
   their existing evidence (typically None after parsing).             *)
Fixpoint assoc_find_evidence (id : Id) (m : list (Id * Evidence))
  : option Evidence :=
  match m with
  | nil => None
  | (k, v) :: rest =>
    if String.eqb k id then Some v
    else assoc_find_evidence id rest
  end.

Fixpoint hydrate_evidence_list (nodes : list Node)
    (evidence_map : list (Id * Evidence)) : list Node :=
  match nodes with
  | nil => nil
  | n :: rest =>
    let ev := match assoc_find_evidence n.(node_id) evidence_map with
              | Some e => Some e
              | None => n.(node_evidence)
              end in
    {| node_id := n.(node_id);
       node_kind := n.(node_kind);
       node_claim_text := n.(node_claim_text);
       node_evidence := ev;
       node_metadata := n.(node_metadata);
       node_claim := n.(node_claim) |}
    :: hydrate_evidence_list rest evidence_map
  end.

Definition hydrate_evidence (ac : AssuranceCase)
    (evidence_map : list (Id * Evidence)) : AssuranceCase := {|
  ac_nodes := hydrate_evidence_list ac.(ac_nodes) evidence_map;
  ac_links := ac.(ac_links);
  ac_top := ac.(ac_top);
|}.

(** Hydrate preserves links and top. *)
Lemma hydrate_evidence_links : forall ac em,
    (hydrate_evidence ac em).(ac_links) = ac.(ac_links).
Proof. reflexivity. Qed.

Lemma hydrate_evidence_top : forall ac em,
    (hydrate_evidence ac em).(ac_top) = ac.(ac_top).
Proof. reflexivity. Qed.

Lemma hydrate_evidence_list_length : forall nodes em,
    length (hydrate_evidence_list nodes em) = length nodes.
Proof.
  induction nodes as [|n ns IH]; intro em; simpl.
  - reflexivity.
  - f_equal. exact (IH em).
Qed.

Lemma hydrate_evidence_list_ids : forall nodes em,
    map node_id (hydrate_evidence_list nodes em) = map node_id nodes.
Proof.
  induction nodes as [|n ns IH]; intro em; simpl.
  - reflexivity.
  - f_equal. exact (IH em).
Qed.

Lemma hydrate_evidence_list_kinds : forall nodes em,
    map node_kind (hydrate_evidence_list nodes em) = map node_kind nodes.
Proof.
  induction nodes as [|n ns IH]; intro em; simpl.
  - reflexivity.
  - f_equal. exact (IH em).
Qed.

(* ------------------------------------------------------------------ *)
(* Auto-hydrate from a validator registry                               *)
(* ------------------------------------------------------------------ *)

(* Reconstruct Certificate evidence for Solution nodes whose JSON
   contained a tool identifier and blob.  Uses the registry to find
   the matching validator function.  ProofTerm evidence cannot be
   reconstructed (proofs are erased), but is reported as missing.       *)
Fixpoint auto_hydrate_list (nodes : list Node)
    (reg : ValidatorRegistry) : list Node :=
  match nodes with
  | nil => nil
  | n :: rest =>
    let n' :=
      match n.(node_kind), n.(node_evidence) with
      | Solution, None =>
        match find_metadata "tool" n.(node_metadata),
              find_metadata "blob" n.(node_metadata) with
        | Some (MVString tool), Some (MVString blob) =>
          match registry_lookup tool reg with
          | Some v =>
            {| node_id := n.(node_id);
               node_kind := n.(node_kind);
               node_claim_text := n.(node_claim_text);
               node_evidence := Some (Certificate blob tool v);
               node_metadata := n.(node_metadata);
               node_claim := n.(node_claim) |}
          | None => n
          end
        | _, _ => n
        end
      | _, _ => n
      end
    in n' :: auto_hydrate_list rest reg
  end.

Definition auto_hydrate (ac : AssuranceCase)
    (reg : ValidatorRegistry) : AssuranceCase := {|
  ac_nodes := auto_hydrate_list ac.(ac_nodes) reg;
  ac_links := ac.(ac_links);
  ac_top := ac.(ac_top);
|}.

Lemma auto_hydrate_links : forall ac reg,
    (auto_hydrate ac reg).(ac_links) = ac.(ac_links).
Proof. reflexivity. Qed.

Lemma auto_hydrate_top : forall ac reg,
    (auto_hydrate ac reg).(ac_top) = ac.(ac_top).
Proof. reflexivity. Qed.

Lemma auto_hydrate_list_ids : forall nodes reg,
    map node_id (auto_hydrate_list nodes reg) = map node_id nodes.
Proof.
  induction nodes as [|n ns IH]; intro reg; simpl.
  - reflexivity.
  - f_equal; [| exact (IH reg)].
    destruct n.(node_kind); try reflexivity.
    destruct n.(node_evidence); try reflexivity.
    destruct (find_metadata _ _) as [[s1|?|?|?]|]; try reflexivity.
    destruct (find_metadata _ _) as [[s2|?|?|?]|]; try reflexivity.
    destruct (registry_lookup _ _); reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Hydration diagnostics                                                *)
(* ------------------------------------------------------------------ *)

(** Report evidence-map IDs that do not match any node in the case. *)
Definition hydrate_unmatched_ids (ac : AssuranceCase)
    (evidence_map : list (Id * Evidence)) : list Id :=
  let node_ids := map node_id ac.(ac_nodes) in
  map fst (filter (fun kv =>
    negb (mem_string (fst kv) node_ids)) evidence_map).

(** Report Solution nodes that carry [tool] metadata but whose tool
    is absent from the validator registry (auto_hydrate would skip them). *)
Definition auto_hydrate_missing_tools (ac : AssuranceCase)
    (reg : ValidatorRegistry) : list (Id * string) :=
  flat_map (fun n =>
    match n.(node_kind), n.(node_evidence) with
    | Solution, None =>
      match find_metadata "tool" n.(node_metadata) with
      | Some (MVString tool) =>
        match registry_lookup tool reg with
        | Some _ => []
        | None => [(n.(node_id), tool)]
        end
      | _ => []
      end
    | _, _ => []
    end) ac.(ac_nodes).

(* ------------------------------------------------------------------ *)
(* Claim registry: rebuild claims after JSON import                     *)
(* ------------------------------------------------------------------ *)

(* After parsing JSON, all node_claim fields are True.  A ClaimEntry
   maps a node ID to its intended Prop.  rebuild_claims replaces
   node_claim for matched IDs, preserving everything else.
   This is only meaningful inside Rocq — Props are erased at
   extraction.  Use it to reconstruct a valid AssuranceCase from
   parsed JSON, then prove WellFormed about the rebuilt case.          *)
Record ClaimEntry : Type := {
  ce_id    : Id;
  ce_claim : Prop;
}.

Definition ClaimRegistry := list ClaimEntry.

Fixpoint claim_registry_lookup (id : Id) (reg : ClaimRegistry)
  : option Prop :=
  match reg with
  | [] => None
  | entry :: rest =>
    if String.eqb entry.(ce_id) id then Some entry.(ce_claim)
    else claim_registry_lookup id rest
  end.

Fixpoint rebuild_claims_list (nodes : list Node)
    (reg : ClaimRegistry) : list Node :=
  match nodes with
  | nil => nil
  | n :: rest =>
    let claim := match claim_registry_lookup n.(node_id) reg with
                 | Some P => P
                 | None => n.(node_claim)
                 end in
    {| node_id := n.(node_id);
       node_kind := n.(node_kind);
       node_claim_text := n.(node_claim_text);
       node_evidence := n.(node_evidence);
       node_metadata := n.(node_metadata);
       node_claim := claim |}
    :: rebuild_claims_list rest reg
  end.

Definition rebuild_claims (ac : AssuranceCase)
    (reg : ClaimRegistry) : AssuranceCase := {|
  ac_nodes := rebuild_claims_list ac.(ac_nodes) reg;
  ac_links := ac.(ac_links);
  ac_top := ac.(ac_top);
|}.

Lemma rebuild_claims_list_ids : forall nodes reg,
    map node_id (rebuild_claims_list nodes reg) = map node_id nodes.
Proof.
  induction nodes as [|n ns IH]; intro reg; simpl.
  - reflexivity.
  - f_equal. exact (IH reg).
Qed.

Lemma rebuild_claims_list_kinds : forall nodes reg,
    map node_kind (rebuild_claims_list nodes reg) = map node_kind nodes.
Proof.
  induction nodes as [|n ns IH]; intro reg; simpl.
  - reflexivity.
  - f_equal. exact (IH reg).
Qed.

Lemma rebuild_claims_list_evidence : forall nodes reg,
    map node_evidence (rebuild_claims_list nodes reg) = map node_evidence nodes.
Proof.
  induction nodes as [|n ns IH]; intro reg; simpl.
  - reflexivity.
  - f_equal. exact (IH reg).
Qed.

Lemma rebuild_claims_links : forall ac reg,
    (rebuild_claims ac reg).(ac_links) = ac.(ac_links).
Proof. reflexivity. Qed.

Lemma rebuild_claims_top : forall ac reg,
    (rebuild_claims ac reg).(ac_top) = ac.(ac_top).
Proof. reflexivity. Qed.

Lemma rebuild_claims_list_length : forall nodes reg,
    length (rebuild_claims_list nodes reg) = length nodes.
Proof.
  induction nodes as [|n ns IH]; intro reg; simpl.
  - reflexivity.
  - f_equal. exact (IH reg).
Qed.

Lemma rebuild_claims_list_metadata : forall nodes reg,
    map node_metadata (rebuild_claims_list nodes reg) =
    map node_metadata nodes.
Proof.
  induction nodes as [|n ns IH]; intro reg; simpl.
  - reflexivity.
  - f_equal. exact (IH reg).
Qed.

(** [rebuild_claims] preserves [supportedby_children] because it
    only changes [node_claim], not links or node IDs. *)
Lemma rebuild_claims_children : forall ac reg id,
    supportedby_children (rebuild_claims ac reg) id =
    supportedby_children ac id.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Fold-based streaming export                                          *)
(* ------------------------------------------------------------------ *)

(* Process an assurance case with a fold, visiting each node and link
   exactly once.  Useful for streaming output to a file or network
   socket without materializing the entire JSON/DOT string.            *)
Definition fold_assurance_case {A : Type} (ac : AssuranceCase)
    (f_node : A -> Node -> A) (f_link : A -> Link -> A) (init : A) : A :=
  let after_nodes := fold_left f_node ac.(ac_nodes) init in
  fold_left f_link ac.(ac_links) after_nodes.

(* Fold that also passes the node index (0-based). *)
Fixpoint fold_nodes_indexed_go {A : Type}
    (f : A -> nat -> Node -> A) (nodes : list Node)
    (idx : nat) (acc : A) : A :=
  match nodes with
  | [] => acc
  | n :: rest => fold_nodes_indexed_go f rest (S idx) (f acc idx n)
  end.

Definition fold_nodes_indexed {A : Type} (ac : AssuranceCase)
    (f : A -> nat -> Node -> A) (init : A) : A :=
  fold_nodes_indexed_go f ac.(ac_nodes) 0 init.

(* Streaming DOT: emit lines via a fold. *)
Definition stream_dot_lines (ac : AssuranceCase) : list string :=
  ["digraph assurance_case {" ++ nl]
  ++ map render_dot_node ac.(ac_nodes)
  ++ map render_dot_edge ac.(ac_links)
  ++ ["}" ++ nl].

(* Streaming JSON: emit lines via a fold. *)
Definition stream_json_lines (ac : AssuranceCase) : list string :=
  let node_strs := map (fun n => render_json (node_to_json n)) ac.(ac_nodes) in
  let link_strs := map (fun l => render_json (link_to_json l)) ac.(ac_links) in
  ["{" ++ json_quote "top" ++ ":" ++ json_quote ac.(ac_top) ++ ","
   ++ json_quote "nodes" ++ ":["]
  ++ match node_strs with
     | [] => []
     | s :: rest => [s] ++ map (fun x => "," ++ x) rest
     end
  ++ ["]," ++ json_quote "links" ++ ":["]
  ++ match link_strs with
     | [] => []
     | s :: rest => [s] ++ map (fun x => "," ++ x) rest
     end
  ++ ["]}"].
