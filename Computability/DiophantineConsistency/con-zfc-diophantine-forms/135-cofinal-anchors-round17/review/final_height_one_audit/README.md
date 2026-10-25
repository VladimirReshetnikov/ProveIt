# Independent final height-one audit

This portable checker closure consists of exactly three Python files:

- verify_final.py: fixed-final selection, exact direct-source bindings, literal polynomial roundtrip, complete audits, mutation controls.
- audit_height_one.py: independently written exact coefficient and universal symbolic graph-lift checker. Imports no producer or vendor code.
- audit_affine_factor.py: exact complete affine refactorization and original-row pullback checker.

Only Python3's standard library is required. No files under the source or release are changed. Supply an output receipt path outside the sealed release.

From the complete Round17 packet root, with the selected height-one release at height_one/ and the direct package at direct/:

    python3 -B review/final_height_one_audit/verify_final.py --release height_one --direct direct --output /tmp/height-one-final-audit.json
    python3 -B -O review/final_height_one_audit/verify_final.py --release height_one --direct direct --output /tmp/height-one-final-audit-optimized.json

In the working research tree the release remains nested at height_one/release; use --release height_one/release there. The driver binds exactly compact793, balanced806, and sparse994, and verifies their copied original sources against direct/strict_grouped_centered/equation.json and direct/strict_sparse_centered/equation.json byte for byte.

Each mode checks all three final expansions, all three full symbolic graph lifts, both complete affine source maps, all three literal text equations,30 deliberate graph corruptions, and8 deliberate affine-map corruptions. The graph audit verifies the universal identity P(L(x))=[sum R_r(x)^2+(sum R_r(x))^2]/2. It does not infer that identity from sampled tuples.

The resulting receipts establish finite algebra, complete integer-zero-set transformations and exact artifact binding. The underlying strict arithmetic source's consistency calibration is audited separately. The final ordinary mathematical proof is the release's report/proof_body.tex, independently reviewed in the accompanying final audit note.
