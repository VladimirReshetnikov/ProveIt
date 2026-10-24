# Fresh scoped upstream replay

Pinned repository commit: 7e533c33819ee1f703b69f2778a767cdc069940d. Replayed 24 October 2026 at approximately 03:40 UTC, after inspecting the release entry points, recursive import/IO surface, finite coefficient recipe, output destinations, and declared subprocess allowlist. No network, installation, whole-repository build, Lean invocation, or consistency-polynomial zero search occurred. Imported code was confined to the copied release; source-relative imports remain portable.

## Results

- Rootfusion complete release, ordinary Python: PASS, six complete norm DAGs, four quotient companions, 92 manifest entries, six actual coefficient reconstructions, generic norm identities, exact degree certificates and operation-preserving corruption rejection.
- Rootfusion complete release, optimized Python: PASS, same coverage. Its six norm points are (variables,degree,operations): (13,1088,195), (13,1392,186), (13,1408,185), (14,696,150), (14,792,137), (15,344,131).
- First parity family complete ordinary release: PASS, all 11 authored stages, 316 manifest entries, 28 byte-identical rebuilt specifications and 615883 raw coefficient bytes. It includes the primitive15-variable degree204/128-operation endpoint and degree352/124 SOS alternative.
- First parity optimized whole driver: EXPECTED POLICY REJECTION, exit1 with explicit instruction to run without -O. This is not a successful optimized whole release.
- All seven designated parity algebraic auditors under optimized Python: PASS. Scripts: audit.py, audit_norm_family.py, audit_shift.py, audit_compact_kernel.py, independent_checks.py, independent_graph_audit.py, independent_compact_audit.py.
- Both original release trees stayed byte-unchanged:93 rootfusion files and317 parity files.
- Fresh independent SymPy resultant derivation of the primitive parity norm and its equivalent compact expression: PASS. No upstream builder/auditor imported. This establishes a universal local identity, not the complete semantic reduction.

## Exact records

- Portable orchestrator: replay/run_upstream_audits.py.
- Consolidated result: replay/results/REPLAY_SUMMARY.json.
- Full rootfusion receipts: replay/results/rootfusion_normal/release.json and rootfusion_optimized/release.json.
- Full ordinary parity receipt: replay/results/parity_normal/release.json.
- Optimized parity rejection and all seven stage outcomes: replay/results/parity_optimized/summary.json, with stdout/stderr files per stage.
- Independent identity checker: replay/check_parity_identity.py; receipts replay/results/PARITY_IDENTITY.json and PARITY_IDENTITY_OPTIMIZED.json.

The full replay ran in19.245 seconds wall time with four independent temporary copies. Normal/optimized rootfusion took6.344/5.959 seconds in this concurrent run; parity ordinary took17.668 seconds. Absolute timings are not mathematical complexity claims.

Other downloaded archives were authenticated and selectively read, but NOT freshly replayed: fixed-prime radicals, second parity family, prime separation, radical-residue, polynomial shears, centered-Pell norms, the dependency Joint Guards archive, and other candidate directories. Their reported verification status in SOURCE_MAP.md is explicitly inherited from pinned upstream review documents. Only the above scopes are fresh local replay results.

Ordinary mathematical proofs and the named native/compiler/Pell/refutation calibration remain distinct from these finite checks. No new internal-ZFC derivation, proof-assistant certificate, global minimum, or consistency conclusion is claimed.
