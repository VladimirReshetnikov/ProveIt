# Independent review of the timed orbit corollary

Review date: 3 October 2026

Reviewed delivery proof SHA-256: 103fe38f7c6d941995e579d7d73dd42ab3836a012666ba16858b158ff698d4c5

## Finding

Conditional acceptance. No mathematical gap was found in the chart-to-quartic corollary, assuming NF supplies the complete effective phase data stated in the proof.

The review checked the following points:

- Half-open phases and lexicographic first-difference refinements preserve exactly one chart and parameter point per exact time
- Constant-term lifting, natural selectors and inactive-branch gates give the stated witness and sum-of-squares counts at ordinary total degree at most four
- Anchored and translated pattern refinements correctly handle prescribed zeros; complete comparison matrices and first-success selection prevent placement multiplicity
- Signed-coordinate complementarity gives canonical external pairs
- All-zero and empty translated patterns are handled separately and correctly
- Exact-time uniqueness is distinguished from potentially infinite witness fibers after existentially forgetting time

The finite checks also passed in the focused review. Normal and optimized Python reruns of the delivered test script produced identical results. Those tests include 208 full drift-restored two-dimensional shuttle states, 325 lexicographic refinements, 1,215 finite witness-cube evaluations, and additional gating, domain, signed-pair and pattern-placement fixtures.

## Scope

This acceptance does not establish NF, a general implemented CA-to-chart compiler, real or rational witness exactness, a uniform-over-input arity bound, or untimed finite-fold representations.

The delivered proof's mathematical core and all text before §9 were separately verified byte-identical to the initially reviewed research source. Only the provenance presentation in §9 changed. No prior release was modified.
