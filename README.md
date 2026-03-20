# RACK — Rocq Assurance Case Kernel

Machine-checked assurance cases. GSN-inspired typed evidence graphs with proved well-formedness, evidence coverage, acyclicity, and support-tree completeness.

## What it does

RACK is a Rocq 9 library that lets you:

- Define assurance cases as typed graphs of Goals, Strategies, Solutions, Contexts, Assumptions, and Justifications (the six GSN node kinds)
- Attach evidence to Solution nodes as either Rocq proof terms (erased at extraction, claim-text binding survives) or external certificates with decidable validators
- Run a boolean well-formedness checker (`structural_checks`) that is **proved sound**: if it returns `true`, a propositional `WellFormed` witness exists, and the central theorem `assurance_case_supported` gives a complete `SupportTree`
- Export to JSON (compact + pretty-printed), DOT (Graphviz, with layout options and clustering), and SACM 2.2 XML
- Import from JSON with evidence hydration, auto-hydrate from validator registries, and claim rebuilding
- Track traceability (requirements, artifacts, commits, tool runs, ownership) with a typed calculus and invalidation theory
- Apply typed deltas (AddNode, RemoveNode, UpdateEvidence, AddLink, RemoveLink, AddTrace, RemoveTrace) with PR-gating semantics and proved composition laws
- Reason about product-line assurance cases with feature-guarded nodes (And/Or/Not feature expressions, variant projection)
- Compile CONOPS documents to assurance case structures with trace links
- Bridge external formal-methods tools (CBMC, Kani, SAW, Verus, Alloy) as Certificate evidence, with both OCaml FFI shims and a Python driver
- Import SysML/AADL model elements as assurance case nodes with trace-preserving compilation
- Embed VST separation-logic Hoare triples as ProofTerm evidence (via CompCert Clight)
- Express behavioral claims as ITree trace predicates with refinement proofs
- Sign evidence blobs with HMAC-SHA256, including key registries with rotation, revocation, and replay protection
- Classify evidence (Theorem, ModelCheck, Test, Symbolic, Certificate) with class-specific trust requirements, trust envelopes, and freshness checking
- Track proof identity across extraction with typed proof IDs, version consistency, and runtime replay

The entire library extracts to OCaml. The extracted code provides a CLI validator (`rack_cli`), property-based test suites (800 random-graph tests + 270 extended tests), benchmarks, and HMAC-SHA256 signed evidence blobs.

## How it compares

| | RACK | SACM 2.2 | Placidus | Event-B + GSN | AdvoCATE |
|---|---|---|---|---|---|
| Representation | Rocq inductive types | UML/MOF metamodel | Eclipse/MMINT models | Event-B machines | XML + Eclipse |
| Proof of well-formedness | Machine-checked (Rocq) | None (schema only) | Unchecked | Rodin provers | Unchecked |
| Evidence validity | Type-checked ProofTerm + decidable Certificate | Untyped ArtifactReference | Model-level | Refinement proofs | Manual review |
| Acyclicity | Proved (Kahn's topo sort + index monotonicity) | Unchecked | Unchecked | Manual | Unchecked |
| Support-tree completeness | Proved (well-founded induction on DAG height via pigeonhole) | Not addressed | Not addressed | Not addressed | Not addressed |
| Entailment | User obligation + typeclass automation + hint databases | Not addressed | Template instantiation | Refinement | Not addressed |
| Extraction | OCaml (native int, CLI, JSON/DOT/SACM, benchmarks) | XMI interchange | Eclipse plugins | Java codegen | N/A |
| Traceability | Typed calculus with 6 link kinds and invalidation theory | Artifact tracing | Product-line templates | Refinement chain | Manual |
| Delta/CI gating | Typed diffs with composition proofs and PR review bot | Not addressed | Not addressed | Not addressed | Not addressed |
| Product-line | Feature expressions (And/Or/Not) with variant projection | Not addressed | Core contribution | Not addressed | Not addressed |
| CONOPS bridge | Document compiler producing nodes + trace links | Not addressed | Not addressed | Not addressed | Not addressed |
| DeepSpec integration | VST Hoare triples, ITree behavioral refinement | Not addressed | Not addressed | Not addressed | Not addressed |
| Signed evidence | HMAC-SHA256 with key rotation, revocation, replay protection | Not addressed | Not addressed | Not addressed | Not addressed |
| Evidence freshness | Trust envelopes with validity windows and class-specific policies | Not addressed | Not addressed | Not addressed | Not addressed |
| Diagnostics | 16 structured error types with per-node localization | Schema errors | Eclipse markers | Rodin messages | Eclipse markers |

SACM defines the interchange format. Placidus targets product-line template instantiation via Eclipse. Event-B encodes GSN arguments as refinement machines. AdvoCATE provides a NASA-developed graphical editor. RACK encodes the graph, the checker, and the metatheory in a single proof assistant, then extracts a standalone toolchain.

## Central proof chain

```
structural_checks ac = true
        │
        │ build_well_formed (Reflect.v)
        ▼
   WellFormed ac
        │
        │ assurance_case_supported (Main.v)
        ▼
  SupportTree ac ac.(ac_top)
```

The `WellFormed` record has 8 fields: top-is-goal, acyclicity, all-reachable-discharged, no-dangling-links, unique-IDs, entailment, well-typed-context-links, well-typed-defeater-links.

The `SupportTree` proof uses well-founded induction on DAG height. The height bound is established via a pigeonhole argument: extract a maximal descending path, prove it NoDup (acyclicity), prove its elements are all in `ac_nodes` (reachability), therefore length <= |nodes|, therefore height < |nodes|, therefore `Acc` holds.

Acyclicity is proved via `verify_topo_order_acyclic`: a valid topological order (every SupportedBy edge goes from lower to higher index, all nodes present, no duplicates) implies `Acyclic`. The topological order is produced by Kahn's algorithm (`topo_sort`), proved complete (`topo_sort_complete`), NoDup (`topo_sort_nodup`), and edge-valid (`topo_sort_valid`).

## Proof inventory

| Theorem | File | What it proves |
|---|---|---|
| `assurance_case_supported` | Main.v | WellFormed => complete SupportTree |
| `build_well_formed` | Reflect.v | structural_checks = true => WellFormed (given entailment + evidence validity) |
| `verify_topo_order_acyclic` | Reflect.v | Valid topo order => Acyclic |
| `topo_sort_complete` | TopoSort.v | Kahn's output contains all node IDs |
| `topo_sort_nodup` | TopoSort.v | Kahn's output has no duplicates |
| `topo_sort_valid` | TopoSort.v | Kahn's output is a valid topological order |
| `topo_sort_length` | TopoSort.v | Kahn's output has the same length as the node list |
| `check_support_tree_go_sound` | Reflect.v | Boolean support-tree checker => propositional SupportTree |
| `check_support_tree_direct` | Reflect.v | Boolean checker => ComputationalSupportTree (no user obligations) |
| `check_defeaters_sound` | Diagnostics.v | check_defeaters = true => every defeater has a resolved counter-argument |
| `compose_well_formed` | Reflect.v | Compositional assembly preserves WellFormed |
| `compose_no_dangling` | Reflect.v | Composition preserves no-dangling-links |
| `compose_unique_ids` | Reflect.v | Composition preserves unique IDs given disjointness |
| `compose_well_typed_context_links` | Reflect.v | Composition preserves context-link typing |
| `structural_checks_fast_correct` | Incremental.v | BST-indexed checker agrees with linear checker |
| `build_bst_index_correct` | Incremental.v | BST find agrees with linear find_node |
| `bst_insert_preserves_ordered` | Incremental.v | BST insert preserves BST_ordered |
| `escape_unescape_roundtrip` | Json.v | JSON string escape then parse recovers original |
| `render_parse_json_string` | Json.v | render then parse JStr recovers original |
| `render_parse_json_roundtrip_literals` | Json.v | render then parse null/true/false recovers original |
| `signed_evidence_valid` | SignedBlob.v | Valid signed blob => evidence_valid |
| `validate_keyed_blob_sound` | SignedBlob.v | Registry validation => verifier accepted |
| `resolve_revoked_none` | SignedBlob.v | Revoked key => resolve_key returns None |
| `check_all_fresh_correct` | EvidenceClass.v | Boolean freshness check => freshness property |
| `check_all_fresh_complete` | EvidenceClass.v | Freshness property => boolean check passes |
| `check_admissible_sound` | EvidenceClass.v | Boolean admissibility => Admissible witness |
| `registries_consistent_refl` | ProofIdentity.v | Registry consistency is reflexive |
| `registries_consistent_sym` | ProofIdentity.v | Registry consistency is symmetric |
| `typed_proof_id_validates` | ProofIdentity.v | TypedProofId validates against any registry containing its name |
| `iac_find_node_correct` | Incremental.v | Indexed lookup agrees with linear lookup |
| `check_context_links_defeaters` | Diagnostics.v | Context-link check implies well-typed defeater links |
| `check_wf_extended_structural` | Diagnostics.v | Extended check implies structural check |

## Trust boundaries

**What Rocq proves:**
- If `structural_checks ac = true` and the user supplies entailment + evidence validity proofs, then `WellFormed ac` holds and `SupportTree ac ac.(ac_top)` exists.
- If `signed_blob_valid sb` holds (i.e., `sb_verify payload sig = true`), then `evidence_valid n (signed_to_evidence sb)` holds.
- ProofTerm evidence carries a claim-text re-checker (`string -> bool`) that survives extraction and verifies at runtime that the evidence is still bound to the correct node.

**What Rocq does NOT prove:**
- That `sb_verify` implements a cryptographically secure algorithm. The OCaml HMAC-SHA256 in `rack_util.ml` is tested against NIST vectors but not formally verified.
- That the extraction directives (`Extract Inductive nat => "int"`, etc.) preserve semantics for all values within OCaml's native integer range.
- That entailment holds for a specific case — this is an undecidable user obligation that the automation (typeclass resolution, hint databases, `vm_compute; tauto`) attempts to discharge.

## Quick start

```coq
From RACK Require Import Core Main Reflect Export Notation.

Definition my_claim : Prop := 2 + 2 = 4.

Definition my_ac : AssuranceCase :=
  mkCase "G1"
    [mkGoal "G1" "2+2=4" [] my_claim;
     mkSolution "E1" "proved"
       (proof_evidence "pf" "2+2=4" my_claim eq_refl) [] my_claim]
    [supports "G1" "E1"].

(* Boolean check *)
Example ok : structural_checks my_ac = true := eq_refl.

(* Propositional well-formedness *)
Definition wf : WellFormed my_ac.
Proof. prove_well_formed_auto. Qed.

(* Central theorem: well-formed => complete support tree *)
Theorem supported : SupportTree my_ac "G1".
Proof. exact (assurance_case_supported my_ac wf). Qed.
```

## Build

Requires Rocq 9.0 and OCaml >= 4.14.

```
make          # build all 33 .v files + extract rack.ml
make ocaml    # compile OCaml binaries (rack_cli, test_rack, rack_bench, etc.)
make test     # run all test suites (1070 tests)
make deepspec # build DeepSpec bridges (requires coq-vst, coq-compcert, coq-itree)
make doc      # generate coqdoc HTML
```

## CLI

```
cat case.json | ./rack_cli --check         # well-formedness gate (exit 0 = pass)
cat case.json | ./rack_cli --diagnose      # structured error JSON
cat case.json | ./rack_cli --dot | dot -Tpng -o case.png
cat case.json | ./rack_cli --json-pretty   # pretty-printed JSON
cat case.json | ./rack_cli --sacm > case.xml
```

## External tool driver

```
python agent/rack_driver.py cbmc --harness harness.c --unwind 200
python agent/rack_driver.py kani --crate . --harness verify_altitude
python agent/rack_driver.py saw --script check.saw
python agent/rack_driver.py alloy --model system.als --check
```

Each produces a RACK-compatible Certificate evidence JSON blob that can be injected into an assurance case via `hydrate_evidence` or `rack_cli`.

## CI

Four CI jobs run on every push and PR:

1. **Linux build** (docker-coq-action, Rocq 9.0 / OCaml 4.14-flambda): full `make`, OCaml build + 1070 tests, extraction warning check, SACM structure validation, coqdoc generation + GitHub Pages deploy
2. **Python tests**: agent sanitizer tests, driver utility tests
3. **DeepSpec** (custom Docker image with VST 2.16 / CompCert 3.16 / ITree 5.2.1): full base build + `make deepspec`, artifact verification
4. **Windows** (setup-ocaml, opam install rocq-prover): cross-platform build + OCaml tests

The **PR review workflow** runs `rack_cli --check` and `--diagnose` on any JSON case files in the diff and posts a structured review comment.

## Layout

```
theories/               Rocq proof sources (33 files)
  Types.v                 Node kinds, evidence, metadata, link types
  Graph.v                 find_node, reachability, evidence helpers, metadata accessors
  WellFormedness.v        SupportTree, WellFormed, boolean checkers, entailment Ltacs
  TopoSort.v              Kahn's algorithm, structural_checks, completeness proofs
  Diagnostics.v           16 CheckError types, diagnose_*, compose_cases, defeaters
  ValidatorRegistry.v     FFI validator dispatch (tool -> validator mapping)
  Core.v                  Re-exports the above six modules
  Main.v                  assurance_case_supported (the central theorem)
  Reflect.v               Boolean reflection, compositional assembly, BFS lemmas
  Json.v                  JSON AST, escaping, renderer, parser, roundtrip proofs
  Dot.v                   DOT/Graphviz export with layout options and clustering
  SignedBlob.v            HMAC-style signed evidence, key registry, rotation, revocation
  ExportUtil.v            JSON importer, hydrate, auto-hydrate, rebuild, streaming
  Sacm.v                  SACM 2.2 XML export
  Export.v                Re-exports Json/Dot/SignedBlob/ExportUtil/Sacm
  Notation.v              Smart constructors (mkGoal, mkSolutionProved, supports, etc.)
  EvidenceClass.v         Evidence classification, trust envelopes, freshness, Admissible
  ProofIdentity.v         Proof identity tracking, TypedProofId, version consistency
  Entailment.v            Typeclass-based entailment (Entails class), hint databases
  Trace.v                 Traceability calculus, 6 link kinds, invalidation theory
  Delta.v                 Typed diffs, PR-gating, delta application and composition
  Incremental.v           BST/AVL indices, refinement proofs, incremental checkers
  ProductLine.v           Feature models, feature expressions, variant projection
  Serialize.v             Full JSON render/parse for TraceGraph, Delta, ProductLineCase
  Bridge.v                SysML/AADL import, CBMC/Kani/SAW/Verus/Alloy bridges
  Conops.v                CONOPS document compiler
  CaseStudy.v             Memory allocator case study (5 evidence types, benchmarks)
  ConopsExample.v         End-to-end CONOPS compilation example
  Example.v               7 worked examples, negative cases, extraction
  VSTBridge.v             VST semax Hoare triples as ProofTerm evidence
  ITreeBridge.v           Behavioral claims as ITree trace predicates
deepspec/               DeepSpec integration (requires coq-vst, coq-compcert, coq-itree)
  max.c                   C source for case study
  max.v                   clightgen-produced Clight AST
  verif_max.v             Full VST semax_body proof
  DeepSpecVST.v           RACK assurance case wrapping the VST proof
  DeepSpecITree.v         RACK assurance case with ITree behavioral refinement
  ConopsITree.v           CONOPS compiler with ITree behavioral claims
  Dockerfile              CI image with VST/CompCert/ITree preinstalled
ocaml/                  Hand-written OCaml
  rack_util.ml            Coq<->OCaml conversions, SHA-256, HMAC-SHA256
  rack_cli.ml             CLI validator (stdin JSON, --check/--diagnose/--dot/--sacm)
  rack_bridge.ml          FFI shims for CBMC, Kani, SAW, Verus, Alloy
  rack_bench.ml           Benchmark harness (structural_checks at multiple graph sizes)
  rack_sacm_validate.ml   SACM XML structure validator
test/                   OCaml test suites
  test_rack.ml            Unit tests for extracted code
  test_rack_prop.ml       Property-based tests (800 random graphs, 8 properties)
  test_rack_extended.ml   Delta, trace, product-line tests (270 tests)
agent/                  Python tooling
  rack_agent.py           Claude agent with output sanitization
  rack_driver.py          Multi-tool evidence driver (CBMC, Kani, SAW, Alloy)
  rack_review.py          PR review bot for assurance case JSON files
  rack_prompt.txt         Agent system prompt
  schema.md               JSON interchange format documentation
  test_agent.py           Agent sanitizer tests
  test_driver.py          Driver utility tests
```

## License

MIT
