# RACK JSON Schema

JSON interchange formats for RACK assurance cases, trace graphs, deltas, product-line cases, and evidence driver output.

## Assurance Case

```json
{
  "top": "G1",
  "nodes": [
    {
      "id": "G1",
      "kind": "Goal",
      "claim": "System is safe",
      "evidence": null,
      "metadata": {"confidence": "high"}
    },
    {
      "id": "E1",
      "kind": "Solution",
      "claim": "Proved safe",
      "evidence": {
        "type": "ProofTerm",
        "label": "safety_proof"
      },
      "metadata": {}
    }
  ],
  "links": [
    {"kind": "SupportedBy", "from": "G1", "to": "E1"}
  ]
}
```

### Node kinds
`Goal`, `Strategy`, `Solution`, `Context`, `Assumption`, `Justification`

### Link kinds
`SupportedBy`, `InContextOf`, `Defeater`

### Evidence types

**ProofTerm** (Rocq proof — label survives extraction, proof erased):
```json
{"type": "ProofTerm", "label": "theorem_name"}
```

**Certificate** (external tool result):
```json
{"type": "Certificate", "blob": "payload_string", "tool": "CBMC"}
```

## Trace Graph

```json
{
  "case": { ... },
  "requirements": ["REQ-001", "REQ-002"],
  "artifacts": ["src/controller.c"],
  "commits": ["abc123"],
  "tool_runs": ["cbmc-run-001"],
  "owners": ["alice"],
  "trace_links": [
    {"kind": "Satisfies", "source": "REQ-001", "target": "G1"},
    {"kind": "VerifiedBy", "source": "G1", "target": "E1"},
    {"kind": "ProducedBy", "source": "E1", "target": "cbmc-run-001"},
    {"kind": "CommittedIn", "source": "src/controller.c", "target": "abc123"},
    {"kind": "ImplementedBy", "source": "G1", "target": "src/controller.c"},
    {"kind": "OwnedBy", "source": "G1", "target": "alice"}
  ]
}
```

### Trace link kinds
`Satisfies`, `ImplementedBy`, `VerifiedBy`, `ProducedBy`, `CommittedIn`, `OwnedBy`

## Assurance Delta

```json
{
  "node_changes": [
    {"op": "AddNode", "node": { ... }},
    {"op": "RemoveNode", "id": "E-old"},
    {"op": "UpdateEvidence", "id": "E1", "evidence": {"type": "Certificate", "blob": "...", "tool": "CBMC"}}
  ],
  "link_changes": [
    {"op": "AddLink", "link": {"kind": "SupportedBy", "from": "G1", "to": "E2"}},
    {"op": "RemoveLink", "from": "G1", "to": "E-old"}
  ],
  "trace_changes": [
    {"op": "AddTrace", "trace_link": {"kind": "ProducedBy", "source": "E2", "target": "cbmc-run-002"}},
    {"op": "RemoveTrace", "trace_link": {"kind": "ProducedBy", "source": "E-old", "target": "cbmc-run-001"}}
  ],
  "commit": "def456",
  "description": "Replace E-old with fresh CBMC evidence"
}
```

### Node change ops
- `AddNode` — add a node (full node object)
- `RemoveNode` — remove by ID (also removes incident links)
- `UpdateEvidence` — replace evidence on an existing node (note: `UpdateEvidence` cannot be parsed from JSON because the Certificate validator is a function; use `hydrate_evidence` after import instead)

### Link change ops
- `AddLink` — add a link (full link object)
- `RemoveLink` — remove by `from`/`to` pair

### Trace change ops
- `AddTrace` — add a trace link
- `RemoveTrace` — remove a matching trace link

## Product-Line Case

```json
{
  "top": "G1",
  "nodes": [
    {
      "node": {"id": "G1", "kind": "Goal", "claim": "System safe", "evidence": null, "metadata": {}},
      "feature": {"type": "True"}
    },
    {
      "node": {"id": "E-radar", "kind": "Solution", "claim": "Radar verified", "evidence": null, "metadata": {}},
      "feature": {"type": "Atom", "feature": "radar"}
    }
  ],
  "links": [
    {
      "link": {"kind": "SupportedBy", "from": "G1", "to": "E-radar"},
      "feature": {"type": "Atom", "feature": "radar"}
    }
  ],
  "feature_model": {
    "features": ["radar", "lidar", "gps"],
    "mandatory": ["gps"],
    "constraints": [
      {"type": "Or", "left": {"type": "Atom", "feature": "radar"}, "right": {"type": "Atom", "feature": "lidar"}}
    ]
  }
}
```

### Feature expression types
- `{"type": "Atom", "feature": "name"}` — feature is enabled
- `{"type": "True"}` — always present (family-wide)
- `{"type": "False"}` — never present
- `{"type": "And", "left": ..., "right": ...}` — conjunction
- `{"type": "Or", "left": ..., "right": ...}` — disjunction
- `{"type": "Not", "expr": ...}` — negation

## Evidence Driver Output

Output of `rack_driver.py` — merge into assurance case via `hydrate_evidence`.

```json
{
  "type": "Certificate",
  "tool": "CBMC",
  "blob": "cbmc:verified:harness.c:unwind=200:2026-03-19T12:00:00Z",
  "verdict": "verified",
  "artifact_hash": "a1b2c3...",
  "timestamp": "2026-03-19T12:00:00Z",
  "metadata": {
    "harness": "harness.c",
    "unwind": "200",
    "returncode": 0
  }
}
```

### Merge procedure

1. Run `rack_driver.py <tool> <args>` to produce evidence JSON.
2. Build an evidence map: `[(node_id, Certificate blob tool validator)]`.
3. Call `hydrate_evidence ac evidence_map` (Rocq) or inject via `rack_cli`.
4. The `blob` field becomes the Certificate payload; `tool` becomes the tool ID.
5. The validator function must be provided at hydration time (from a `ValidatorRegistry`).

### Verdict values
`verified`, `falsified`, `unknown`

## Trust Envelope Metadata Keys

Canonical key names for node metadata fields used by `TrustEnvelope` (from `EvidenceClass.v`). Use these exact strings for interop with `trust_envelope_of_metadata`, `evidence_fresh`, `diagnose_metadata_expiry`, and `diagnose_required_keys`.

| Key | Type | Meaning |
|---|---|---|
| `tool` | `MVString` | Originating tool identifier (e.g. `"CBMC"`, `"SAW"`) |
| `version` | `MVString` | Tool version string |
| `timestamp` | `MVTimestamp` | When the evidence was produced (ISO 8601) |
| `valid_from` | `MVTimestamp` | Evidence validity start (ISO 8601) |
| `valid_until` | `MVTimestamp` | Evidence validity expiry (ISO 8601) |
| `replay` | `MVString` | Command to re-run validation |
| `confidence` | `MVString` | Confidence level (`"high"`, `"medium"`, `"low"`) |
| `blob` | `MVString` | Raw evidence payload (for auto-hydration) |
| `undeveloped` | `MVBool` | Node is intentionally undeveloped |
| `assumption_status` | `MVString` | `"active"` or `"invalidated"` |
| `weight` | `MVString` | Node importance weight |

These keys are also defined as Rocq constants (`te_key_tool`, `te_key_version`, etc.) in `Serialize.v` for use in Rocq-side metadata construction.
