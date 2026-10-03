# Standalone verifier metadata-binding audit

Audit date: 2026-10-03 UTC. Result: PASS for the requested hardening. Read-only audit of the research bundle and v1 backup; execution used Python `-B` (and separately `-B -O`). All audit outputs are under the sibling replay directory. No compiler/circuit edits, upstream execution, installation, or publication.

## Requirements and evidence

- `verify_example.py` imports only `pathlib`, `json`, and `hashlib`. Independent probes installed an import guard rejecting compiler/circuit imports and passed.
- Counts use `type(value) is int`, rejecting bools/floats. Input and target must be equally sized lists of exact integers. Both input counts must equal `4*n`.
- The total arity equals both list lengths (`values` and unique string `variable_names`) and is at least the input arity. Every assignment value, including the last auxiliary value, must be an exact nonnegative integer.
- The external prefix must equal canonical positive/negative signed pairs for input followed by target metadata. Noncanonical signed pairs and stale metadata are rejected.
- All three top-level key sets and both format strings are checked. Sparse coefficients and indices are exact integers; monomials have valid bounds, sorted indices, no duplicates, and degree at most 4 (quartic) or 2 (residual). The supplied example actually has degree 4.
- Independently expanded residual squares must equal the serialized polynomial coefficient-for-coefficient. Every residual and the quartic are evaluated at the supplied natural assignment and required to vanish. Normal and optimized runs both pass for 1,502 variables, 1,502 residuals, and 12,595 quartic monomials; all 1,494 single-coordinate `+1` auxiliary mutations make the quartic positive.
- Final bundled suite: **37/37 rejected in both modes**, including bool/float input and total counts, disagreement, mismatched metadata, the exact combined `quartic.input_count=True` plus `witness.target=[100,200]` case, and full wrong-target mutation alone. The earlier 35-case run preceded the two-case regression addition; final receipts reflect 37 cases.
- Independent suite: **31/31 additional negatives rejected in both modes**, including last-element naturalness, shared wrong input counts, residual coefficient/degree errors, literal-SOS mismatch, and a nonzero auxiliary residual. Valid and rejected verification calls left caller data unchanged.

## Exact scope and limitations

This is a standalone algebraic certificate checker, not an independent reconstruction of the compiler, automaton semantics, reachability, or source provenance. It checks the supplied polynomial/residuals/assignment and metadata binding. It does not pin the inputs to the example file hashes; hashes below identify what was audited.

`exact_schema_checked` is not a claim of deep ledger validation: `ledger` need only be a dict. Arbitrary ledger contents and arbitrary unique string display names are accepted. Dimension-zero empty certificates and degree below 4 are also accepted by the generic checker. These acceptance probes are recorded explicitly; none contradicts the stated requirements. The +1 witness perturbations are finite example checks, not exhaustive uniqueness or soundness proofs. The JSON loader uses ordinary `json.loads`; duplicate JSON object-key rejection and resource-exhaustion limits are not implemented.

## Integrity and exact hashes

- `verify_example.py`: `d94aaee61d794f0c8ff8febc9334675f23f6c238df43eb88609982ae3026a9bd`
- `test_example_validation.py`: `a7717135b8ad46880770cfc71050f66c88906f180c937f1a4f072fcd932b607f`
- `example-pair-quartic.json`: `ddd6973f1285d60c2ae663b6b47cd933827e9e86c332cb69148c1ef45c27dca1`
- `example-pair-sos.json`: `96715e468c3af4b489a1ce881ea0c09cdae7bffa0efca762d8e5a308c2ddbae0`
- `example-pair-witness.json`: `ef49bb8c56731827374123e215c608dd0d1468c8ee5fe234c2dd32524d0c2095`
- `compiler.py`: `133d811972b6332ddc2fadfa8a7e34f3076b4712affa7c757d60e90d3ea2f5aa`
- `circuit.py`: `dca31e8c2de8f6f4c1ae3bd17b8fbe614d67a92debd3b6b782f2d75704c83066`
- v1 `verify_example.py`: `ab7b7d01f4918e7461a3285a4b2f6be1f960cf5e318fdf08300dac20974b3956`

Initial read-only audit comparison found all 71 current-source files and all 66 v1 files identical in bytes, size, mode, and mtime. Across the regression update, final comparison records source changed paths: `['MANIFEST.json', 'PROVENANCE.json', 'README.md', 'REPLAY.md', 'RESULTS.md', 'SHA256SUMS', 'bundle-verification-optimized.json', 'bundle-verification.json', 'example-validation-receipt-optimized.json', 'example-validation-receipt.json', 'resource-ledger.json', 'test_example_validation.py']`. The audit itself made no source-tree writes. v1 remained `UNCHANGED`. Compiler, circuit, and verifier hashes stayed unchanged.

Reproducible evidence in `verifier-audit/`: bound 37-case receipts, standalone normal/optimized results, `probe_binding.py`, independent normal/optimized receipts, initial/final source snapshots, v1 snapshot, and integrity comparisons.

Portability note: probe_binding.py now accepts --source-dir and defaults to the sibling source reference instead of an absolute workspace path. Its mathematical probes are unchanged; all 31 probes were rerun normally and under -O after this input-routing-only change, with both passing.
