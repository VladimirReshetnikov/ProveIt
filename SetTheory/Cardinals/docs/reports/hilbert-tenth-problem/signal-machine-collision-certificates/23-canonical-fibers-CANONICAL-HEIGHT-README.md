# Canonical outer height, with a fixed native extension fiber

This separate packet adds one positive slack and one affine row to the complete five-gate folded unbounded clean-clock construction. It leaves the frozen base, folding addendum, and Report21 unchanged.

The new row is `eta+kappa=S+1`, with `S=n_initial+n_target+theta` and retained `h=S+eta`. Positive integer slacks and the retained native dyadicity force exactly the least power of two **strictly greater** than S. Every genuine history still fits: its quotient digits are below its positive physical clock theta. The known infinite family from arbitrarily enlarging the outer height is removed.

Every accepted nonempty fiber has unique outer coordinates and projects bijectively onto its entire 22-coordinate positive native AND-extension fiber at fixed padded ports and prescribed scale. This packet proves no cardinality theorem for that native fiber. It does not establish finite-foldness, full witness uniqueness, a universal ordinary-input loader, or a materialized positive Pell tuple.

## Complete emitted results

Native/spatial and phase4 models each have these totals:

| Fixture | M | A | Total | Positive coordinates | Exact degree |
|---|---:|---:|---:|---:|---:|
| INC2;DEC2 | 240 | 368 | 608 | 61 | 2344 |
| ZERO3 | 185 | 298 | 483 | 59 | 1192 |
| NOP | 183 | 298 | 481 | 59 | 1192 |
| POSITIVE3 | 190 | 294 | 484 | 59 | 1192 |

Each complete nonempty circuit has two natural input ports, 21 comparisons, and the entire 62-gate SOS finalizer. The added 1M+4A is fully paid. S was not originally materialized: a verified single-consumer two-addition reassociation materializes it without extra gates while preserving every old residual polynomial on all tuples. The new full polynomial is the folded parent's polynomial plus `(eta+kappa−S−1)^2` on every integer tuple.

The two four-gate no-witness initially halted JSON circuits are copied byte-identically from the frozen base and remain separate from the positive-theta packet.

## Files

- `THEOREM.md`: general eligible-source proof, no-wrap, canonical completeness, exact domain boundaries, native-fiber bijection and literal circuit construction
- `circuits/`: eight complete canonical JSON circuits and textual DAGs, plus two unchanged zero-step JSON circuits
- `emit_canonical_clocks.py`: own standard-library emitter/replayer, using only authenticated arithmetic JSON data
- `audit/CANONICAL-HEIGHT-PROOF-AUDIT.md`: independent mathematical/interface audit and finite outer-history evidence
- `audit/CANONICAL-HEIGHT-CIRCUIT-AUDIT.md`: independent complete circuit audit
- `audit/check_canonical_height_proof.py`: independent semantic/interface checker
- `audit/check_canonical_height.py`: independent complete DAG, identity, ledger, degree and corruption checker
- `reference/`: manifest-pinned frozen circuit and theorem inputs; no upstream Python is imported or executed
- `receipts/`: emission and fresh replay records
- `MANIFEST.json`, `verify_manifest.py`: integrity seal and read-only verifier

## Portable replay

From this directory, using standard Python 3:

```sh
python emit_canonical_clocks.py --check
python audit/check_canonical_height_proof.py --expect audit/canonical_height_proof_checks.json
python audit/check_canonical_height.py --expect audit/independent-canonical-height-audit.json
python verify_manifest.py
```

The same commands also pass under `python -O`: checks use explicit errors rather than optimization-removable assertions. To run from a different current directory, use absolute or correctly relative paths for each script and its receipt. All data paths resolve from the script's packet root, so the replay needs no original absolute workspace path or live frozen sibling. Optional live-source integrity checks are described in the audit notes.

The exact-degree audit independently recomputes all univariate coefficients modulo 1000003 and matches a nonzero coefficient at the formal upper degree. Signed/modular checks and finite canonical outer histories supplement the algebraic proofs; they are not numerical full positive native witnesses.
