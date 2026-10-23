# Independent finite audit and source review

The finite audit is self-contained. It needs Python 3 and only the standard library. It imports no repository Python, invokes no compiler, and makes no network requests.

From the archive root:

```sh
python3 research/audit_left_frames.py \
  --inputs inputs \
  --out /tmp/k215-left-frame-audit.json
```

A checkout-based route remains available:

```sh
python3 research/audit_left_frames.py \
  --repo /path/to/ProveIt \
  --out /tmp/k215-left-frame-checkout-audit.json
```

Choose exactly one of `--inputs` and `--repo`. Both modes verify the same exact reviewed byte counts and SHA-256 hashes before parsing any data. A checkout need not be at that commit if all required input bytes are identical; changed inputs are rejected rather than silently treated as the reviewed machine.

## Scope of the result

The audit independently checks:

- expansion of the 202-node source DAG to all 4,751 published leaves;
- routing through the maintained 234-role decoder to every primitive entry;
- all 430 native/formal transition actions under the explicit label translation;
- equality of those actions with the effective maintained Rocq table;
- all 444 symbolic steps of the 35 recorded control templates, including every safe-left guard;
- exact right endpoint normalization, source-action guards, gap changes, and scanner premises;
- all 1,422 template uses, the exact three exceptional controls, and complete control coverage;
- the 6,176 original outcomes and projected 4,789 distinct expensive replay bodies;
- a concrete counterexample to dropping the safe-left guard.

`PASS` is independent finite evidence. It is not a Lean/Rocq proof, a complete source-occurrence assembly theorem, an endpoint rebuild, or an internal ZFC derivation. The universal theorems and accepted compiler checks are supplied elsewhere in the archive.

## Flat input mapping

All eleven input files are byte-identical copies from ProveIt commit
`cbf94cb552a3b49509e0eee80e7455d4eb5974c6`. They total 638,902 bytes. The full repository paths, exact hashes, and byte counts are in `inputs/PROVENANCE.json`, embedded in the audit script, and repeated in its output. No full repository checkout, endpoint archive, or compiler distribution is needed for this audit.

| Audit key | Flat filename under `inputs/` | Purpose |
|---|---|---|
| `sites` | `sites215.json` | Exact published source leaves |
| `native` | `k215.native.tm` | Native transition table |
| `formal_table` | `KTable215.lean` | Maintained Lean formal-label table |
| `decoder` | `K215Decoder.lean` | Source DAG and decoder roles |
| `templates` | `FORMAL_TEMPLATES.json` | Earlier round13 template bodies and recorded steps |
| `assignments` | `LEFT_FRAME_DISCOVERY.json` | Earlier round13 occurrence assignments and three fallbacks |
| `runtime` | `KRuntimeCore.lean` | Reviewed symbolic-runtime source identity |
| `simulation` | `KSim.lean` | Reviewed maintained coverage-interface identity |
| `endpoint` | `KEndpoint.lean` | Reviewed maintained endpoint-interface identity |
| `rocq_table` | `Table230.v` | Maintained Rocq table literals |
| `rocq_machine` | `TM230.v` | Maintained Rocq disabled labels and table selection |

The runtime, simulation, and endpoint sources are retained as exact context for the independent transcription and interface review. The Python audit hashes those files; it does not parse their theorem proofs or establish their soundness. The remaining eight files provide the finite data that the audit parses and checks.

The 35-template discovery and its occurrence map are prior work from `round13-left-frame`. Their inclusion is reproduction of the reviewed input, not a claim to have newly discovered them. Preserve the inherited notices in the archive.

## Review and inventory evidence

- `independent_source_review.md` reviews the statements and guards of the four new Lean modules at the exact hashes listed in that note.
- `frame_contract_review.md` develops the tape formulas, source-action guards, counterexamples, and semantic-consumer integration boundary. It records a review captured during development; the archive's accepted compiler results determine the final compilation status.
- `evidence/left_frame_audit.json` is the successful bundled-input replay result. `evidence/left_frame_audit.stdout.txt` records its output.
- `evidence/current_endpoint_inventory_independent.json` records the independent static 174-module endpoint census and comparisons with historical phase15 inventories. It is a source inventory, not a new endpoint compilation; reproducing the full import walk requires the pinned checkout.
- `evidence/independent_provenance_review.json` records the reviewed proof dependencies and prior proposal inputs, together with hashes and attribution scope. It is not a compiler receipt or a reinterpretation of inherited licenses.

The JSON inventory and provenance files above are at the archive root's `evidence/` directory, not inside `research/`.
