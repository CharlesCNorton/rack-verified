# RACK -- Rocq Assurance Case Kernel

Machine-checked assurance cases. GSN-inspired typed evidence graphs with proved well-formedness, evidence coverage, acyclicity, and support-tree completeness.

## What it does

RACK is a Rocq 9 library that lets you:

- Define assurance cases as typed graphs of Goals, Strategies, Solutions, Contexts, Assumptions, and Justifications (the six GSN node kinds)
- Attach evidence to Solution nodes as either Rocq proof terms (erased at extraction, label survives) or external certificates with decidable validators
- Run a boolean well-formedness checker (`structural_checks`) that is **proved sound**: if it returns `true`, a propositional `WellFormed` witness exists, and the central theorem `assurance_case_supported` gives a complete `SupportTree`
- Export to JSON, DOT (Graphviz), and SACM 2.2 XML
- Import from JSON with evidence hydration and claim rebuilding
- Track traceability (requirements, artifacts, commits, tool runs) with invalidation theory
- Apply typed deltas with PR-gating semantics and proved composition laws
- Reason about product-line assurance cases with feature-guarded nodes
- Compile CONOPS documents to assurance case structures with preservation proofs
- Bridge external tools (CBMC, Kani, SAW, Verus, Alloy) as Certificate evidence
- Embed VST separation-logic Hoare triples as evidence (via CompCert Clight)
- Express behavioral claims as ITree trace predicates with refinement proofs
- Compile CONOPS requirements to ITree-based behavioral specifications

The entire library extracts to OCaml. The extracted code provides a CLI validator (`rack_cli`), property-based test suites, benchmarks, and HMAC-SHA256 signed evidence blobs.

## How it compares

| | RACK | SACM 2.2 | Placidus | Event-B + GSN |
|---|---|---|---|---|
| Representation | Rocq inductive types | UML/MOF metamodel | Eclipse/MMINT models | Event-B machines |
| Proof of well-formedness | Machine-checked (Rocq) | None (schema only) | Rodin provers | Rodin provers |
| Evidence validity | Type-checked ProofTerm + decidable Certificate | Untyped ArtifactReference | Model-level | Refinement proofs |
| Acyclicity | Proved (topo-order + BFS) | Unchecked | Unchecked | Manual |
| Support-tree completeness | Proved (well-founded induction on DAG height) | Not addressed | Not addressed | Not addressed |
| Entailment | User obligation + typeclass automation | Not addressed | Template instantiation | Refinement |
| Extraction | OCaml (native int, CLI, JSON/DOT/SACM) | XMI interchange | Eclipse plugins | Java codegen |
| Traceability | Typed calculus with invalidation theory | Artifact tracing | Product-line templates | Refinement chain |
| Delta/CI gating | Typed diffs with composition proofs | Not addressed | Not addressed | Not addressed |
| Product-line | Feature expressions with projection proofs | Not addressed | Core contribution | Not addressed |
| CONOPS bridge | Compiler with preservation proofs | Not addressed | Not addressed | Not addressed |
| DeepSpec integration | VST Hoare triples, ITree behavioral specs | Not addressed | Not addressed | Not addressed |

SACM defines the interchange format. Placidus targets product-line template instantiation via Eclipse. Event-B encodes GSN arguments as refinement machines. RACK encodes the graph, the checker, and the metatheory in a single proof assistant, then extracts a standalone toolchain.

## Build

Requires Rocq 9.0 and OCaml >= 4.14.

```
make          # build all .vo files + extract rack.ml
make ocaml    # compile OCaml binaries (rack_cli, test_rack, etc.)
make test     # run test suites
make deepspec # build DeepSpec bridges (requires coq-vst, coq-compcert, coq-itree)
```

## Quick start

```coq
From RACK Require Import Core Main Reflect Export Notation.

Definition my_claim : Prop := 2 + 2 = 4.

Definition my_ac : AssuranceCase :=
  mkCase "G1"
    [mkGoal "G1" "2+2=4" [] my_claim;
     mkSolution "E1" "proved" (proof_evidence "pf" my_claim eq_refl) [] my_claim]
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

## CLI

```
cat case.json | ./rack_cli --check
cat case.json | ./rack_cli --diagnose
cat case.json | ./rack_cli --dot | dot -Tpng -o case.png
cat case.json | ./rack_cli --sacm > case.xml
```

## Layout

```
theories/               Rocq proof sources
  Types.v                 Node kinds, evidence, metadata, link types
  Graph.v                 find_node, reachability, evidence helpers
  WellFormedness.v        SupportTree, WellFormed, boolean checkers
  TopoSort.v              Kahn's algorithm, structural_checks, completeness
  Diagnostics.v           CheckError, diagnose_*, compose_cases, defeaters
  ValidatorRegistry.v     FFI validator dispatch
  Core.v                  Re-exports the above six modules
  Main.v                  assurance_case_supported (the central theorem)
  Reflect.v               Boolean reflection, compositional assembly proofs
  Json.v                  JSON AST, renderer, parser
  Dot.v                   DOT/Graphviz export
  SignedBlob.v            HMAC-style signed evidence
  ExportUtil.v            JSON importer, hydrate, rebuild, streaming
  Sacm.v                  SACM 2.2 XML export
  Export.v                Re-exports Json/Dot/SignedBlob/ExportUtil/Sacm
  Notation.v              Smart constructors (mkGoal, supports, etc.)
  EvidenceClass.v         Evidence classification, trust envelopes, freshness
  ProofIdentity.v         Proof identity tracking across extraction
  Entailment.v            Typeclass-based entailment automation
  Trace.v                 Traceability calculus, invalidation theory
  Delta.v                 Typed diffs, PR-gating, composition
  Incremental.v           BST/AVL indices with refinement proofs
  ProductLine.v           Feature models, variant projection
  Bridge.v                SysML/AADL import, Alloy/Verus/Kani/SAW bridges
  Conops.v                CONOPS document compiler
  CaseStudy.v             Memory allocator case study
  ConopsExample.v         End-to-end CONOPS example
  Example.v               7 examples, negative cases, extraction
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
  rack_cli.ml             CLI validator (stdin JSON, --check/--dot/--sacm)
  rack_bridge.ml          FFI shims for CBMC, Kani, SAW, Verus, Alloy
  rack_bench.ml           Benchmark harness
  rack_sacm_validate.ml   SACM XML structure validator
test/                   OCaml test suites
  test_rack.ml            Unit tests for extracted code
  test_rack_prop.ml       Property-based tests (100 random graphs)
  test_rack_extended.ml   Delta, trace, product-line tests
```

## License

MIT
