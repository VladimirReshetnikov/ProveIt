# Fixed-scale native witness multiplicity

**Result: infinite, independently reviewed.** Every nonempty positive fiber of the inherited prescribed-scale native AND64 circuit contains an infinite family with its ports, scale and nineteen of twenty-two native witness coordinates fixed. Only `j`, `o`, and `y_aux` vary.

The proof applies an integral norm-preserving matrix congruent to the identity modulo `R*c*f`. It does not vary the history height or use deterministic-computation uniqueness. It requires only one native positive seed, already supplied by prescribed-scale completeness.

- `THEOREM.md`: exact statement, source equations, parameter family and all positivity/integrality checks
- `REVIEW.md`: independent proof and literal-source review, PASS
- `check_native_fibers.py`: new local code auditing the pinned arithmetic JSON as data
- `CHECK-RECEIPT.json`: four literal dependency checks and five finite auxiliary-only family terms
- `source/native_blocks.json`: exact native gate/witness/comparison extracts from the authenticated complete receipt
- `source/provenance.json`: pinned public Markdown links, Git blob IDs, byte counts and SHA-256 hashes
- `MANIFEST.json`: integrity hashes for this workspace's final deliverables

Reproduce the local arithmetic audit with `python3 -B check_native_fibers.py --check`. It reads the immutable source receipt at `../inherited-source/three_mass_unbounded_interface.json` and verifies its SHA-256 with an explicit error check before parsing it. The numerical example is explicitly auxiliary-only; no complete native Pell tuple is materialized. No upstream Python is imported or executed.

All work is local. No frozen report or circuit was edited; no publishing, commits or pull requests were performed.

## Portable delivery adaptation

The original frozen manifest is retained as `original-MANIFEST.json`. The local checker is adapted to a portable data path and read-only receipt comparison. Every original assertion is an explicit error check, so all substantive checks remain active under `python3 -O`. `MANIFEST.json` seals the delivered subset; root `delivery-provenance.json` records original and delivered hashes.
