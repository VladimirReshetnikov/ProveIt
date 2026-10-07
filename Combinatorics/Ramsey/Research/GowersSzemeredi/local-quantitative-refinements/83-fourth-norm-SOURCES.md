# Sources and exact inventory

Report295 is an independent article prepared on 7 October 2026. All the mathematical arguments required for its results are reproduced in Report295.tex. Earlier reports are comparison context, not runtime dependencies.

## Audited proof bindings

The authoring inputs were frozen research derivations, independently audited before final release. Their SHA-256 bindings are:

- General fourth-norm extremizers, PROOF.md: ecec37549c5ede6746a4726a3cc297a3fa18e78e7a34dd7867c64e2a07fa3b07
- All-order reflection formula, corrected final PROOF.md: c26c095a6c037a695acfbf169ba81d7bcd3d0c766ceb7738e7536c83a5717264
- Point-spike and finite-index saturation, PROOF.md: 9f25d66a23aa9cfd9b365a794ef252c07b370e5bfaf35aad369b2dfab0e14d71

The reflection audit initially bound the preceding version 9ccfecffb1d8dd56ea324c65f26cf5a318fd6190b468ec396d04b9c277b68ce2. Its final binding verifies that the sole change was inserting “nonzero ” into the n=1,2 ratio statement. Zero satisfies homogeneous equality but has no defined ratio. The audit applies unchanged to the final source above.

The article uses its own beta_n for the constant-transition parameter and eta_n for the energy bound, avoiding the collision between the separate derivations. Its dimension-free threshold and the order 27 indicator corollary are direct stated consequences of the proved formulas. Neither computation is used as evidence for a broader conjecture.

These source bindings document provenance. The mathematical proofs are in the article, and the exact checker does not open source notes or depend on their paths. Hashes are integrity identifiers, not digital signatures.

## Primary literature inspected

1. Ludovick Bouthat, Javad Mashreghi and Frédéric Morneau-Guérin, On the norm of normal matrices, RIMS Kôkyûroku Bessatsu B93 (2023), 183–222. Primary indexed PDF Conjecture 5.6, journal page 210, and Theorem 5.10, page 215, were checked directly. Full direct PDF retrieval was unreliable; the indexed primary passages were available. The conjecture has the all-real-maximizer quantifier, and its arbitrary-p scope is broader than the theorem proved in this report.
   https://r-libre.teluq.ca/2603/1/B93-10.pdf
   Publisher repository: https://repository.kulib.kyoto-u.ac.jp/bitstream/2433/284879/1/B93-10.pdf

2. Cordian Riener, On the degree and half degree principle for symmetric polynomials, Journal of Pure and Applied Algebra 216 (2012), 850–856. Theorem 1.3 in the primary arXiv v2 PDF was inspected. It credits Timofte and supplies the at-most-two-valued nonnegativity test for symmetric quartics. This gives existence of a two-valued norming vector, not by itself classification of every equality vector.
   https://arxiv.org/pdf/1001.4464
   https://doi.org/10.1016/j.jpaa.2011.08.012

3. Olga Holtz and Michael Karow, Real and complex operator norms, manuscript dated 2004, arXiv posting 2005. Theorem 3.1 and Lemma 3.4 were inspected in the primary text. These include equality of real and complex norms when p=q and the phase-average identity.
   https://arxiv.org/html/math/0512608v1

4. ProveIt research report294, Sharp Weighted Energy Gaps and the Target Torsion Dichotomy, prepared for Vladimir Reshetnikov, 7 October 2026. Used for context and the earlier nine-point constant. Report295 reproves the operator and spike arguments it needs. Report294 was read only and remains unchanged.

This is a bounded primary-source review. No exhaustive later-literature, novelty or publication-priority conclusion is made.

## Builder and checker provenance

build.py and tests/test_build.py are adapted locally from the frozen public Report294 builder and corresponding tests. Changes are report-identity substitutions, the archive basename, and replacement of companion/midpoint_certificate.json with companion/interval_certificate.json in the exact allowlist and tests. The eleven-source-file and thirteen-archive-entry counts are unchanged. Guarded filesystem operations, exclusive-output policy, resource limits, subprocess isolation, source-immutability checks, optimization checks, PDF gates and deterministic archive logic are retained.

The mathematical companion is standalone. It uses exact integer and rational arithmetic, no external computer-algebra package, no floating-point optimizer, and no import from an earlier report or research directory. Its README identifies the complete finite checking scope. A successful test suite is not a formal mathematical proof certification.

## Exact public source allowlist

The eleven authored files are:

- README.md
- REPRODUCING.md
- SOURCES.md
- Report295.tex
- build.py
- companion/__init__.py
- companion/README.md
- companion/exact_checks.py
- companion/interval_certificate.json
- tests/test_build.py
- tests/test_companion.py

The final distribution adds Report295.pdf and MANIFEST.sha256. No logs, receipts, compiled Python, audit scratch files, rendered page images, absolute-path dependencies, or earlier report files are included in the public ZIP.
