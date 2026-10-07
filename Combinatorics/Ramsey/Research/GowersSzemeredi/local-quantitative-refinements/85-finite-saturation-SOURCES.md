# Sources and provenance for Report 297

## Exact public inventory

Twelve authored or incorporated source files:

1. README.md
2. REPRODUCING.md
3. SOURCES.md
4. Report297.tex
5. build.py
6. companion/README.md
7. companion/classify.py
8. companion/exact_checks.py
9. companion/compact_certificate.json
10. companion/finite_certificate.json
11. tests/test_build.py
12. tests/test_companion.py

A distribution adds Report297.pdf and MANIFEST.sha256, for fourteen archive members under Report297/. The final ZIP pin is external to the archive; logs, receipts, build directories and rendered page previews are not public members.

## Mathematical dependency

Report 295, Exact Fourth Norms and Two-Valued Extremizers, 7 October 2026, is the frozen predecessor. The imported analytic input is its complete reflection fourth-norm/equality theorem over real and complex scalars. Report 297 states that input explicitly, then proves the integer comparator, all-order unique multiplicity, both saturation classification routes, and the rational/indicator corollary. It includes a concise proof of the Fourier point-spike and subgroup-spike criteria so the energy link can be checked from the stated operator theorem.

The full general mean-perturbation proof from Report 295 is not repeated. It remains a substantive cited mathematical dependency, though no Report 295 files or companion execution are required to run this report's integer verifier. The manuscript's reference to Report 295 is a report-series citation rather than an external literature-priority claim. Reports 1–296 were not modified.

## Reviewed input hashes

SHA-256 values of the reviewed source inputs, recorded for traceability:

- Frozen Report295 TeX source: `8822372da46e17c10a12727fcd0b53fa8995d6f38f3ba67eadf62679240cdd8c`
- Frozen Report295 guarded builder: `f43a53bd890aae18f36ce418bea63471b9693b67f42869d6be629243fd6edcc9`
- Frozen Report295 builder regression suite: `1bb6845960d95b82e4079288d25aafa29215795576bf084a77fd77c2243f4f8e`
- Classification proof including rational/indicator corollary: `71b2e503aff2e6c22484c92cfa955f5aad941a623d0042ed650f089c34e5a817`
- Classification proof audit: `59a2daab366c9196bdc33ad46e99463ffce5a27c7e7213fbf7b7cd011706d5c4`

The classification proof and both its finite verification routes received an independent mathematical audit before manuscript packaging. The independent audit was a conventional mathematical and exact-arithmetic review, not a formal proof-assistant certificate. An independent verifier imported no author code, used an alternative polynomial expression, and recomputed all 351,648 branches and all compact boundary values. Audit logs are not included as mathematical dependencies or represented as user-facing proof.

## Unchanged incorporated classifier and certificates

- companion/classify.py: `f90232ba9eea3bc2b07ccced2cf45f516c72dff4de52fe3dea09f5a899d63b41`
- companion/compact_certificate.json: `9b98497b6ade91d40a2921c9e6a8816129caec3c150c69b84d75750e1a9a5c88`
- companion/finite_certificate.json: `ed8b6fce10f4d30a96cd177536529d945327ce285e3d9f377131837a93e13763`

These three files are byte-for-byte copies of the frozen audited classification materials. The classifier documentation refers to its original PROOF.md; the corresponding reader-facing proof is now Report297.tex and Report297.pdf. The classifier's source file is intentionally unchanged to preserve the audited bytes.

## Integration and builder provenance

The Report295 builder and its test suite were adapted only for this report's identity, actual inventory and receipt description; the guarded filesystem and process behavior was preserved. The exact inventory removes companion/__init__.py and replaces the earlier interval-certificate entry with the classifier and its two integer certificates. This changes the authored-source count from eleven to twelve. All affected allowlist/count expectations in the tests were updated.

The new exact_checks.py wrapper invokes the frozen classifier in --verify mode against its own two bundled certificates, then verifies the finite rational support cases and the displayed n=27/n=81 comparator gaps. It is read-only and refuses extra arguments. The upstream five grouped regression tests were relocated to tests/test_companion.py, their subprocesses made isolated and bounded, and nine integration/mathematical tests added. The inherited builder suite remains separate.

## Limits

No finite computation is claimed to establish an all-order statement by extrapolation. No comparison of decimal radicals chooses a multiplicity. No full nontrivial-kernel equality classification, actual nonsaturating minimum, exact indicator minimum, arbitrary-exponent theorem, formal verification, novelty, priority or global Ramsey/Szemeredi improvement is asserted. SHA-256 checks provide integrity, not authorship authentication or digital signatures.
