# Independent source review: natural-82 model-transfer plan

The [model-transfer audit](../../research/ordinary14-natural82-model-transfer-audit/README.md) accurately describes the inspected source interfaces and a sound mathematical route, conditional on those interfaces elaborating with the asserted meanings. It identifies the missing predecessor property and does not infer it from the arbitrary-ring graph identity. Its receipt reproduces. The route is a plan, not a Lean-checked theorem or an iPRA derivation.

The independent checker rehashes the 16 pinned source files and checks the relevant declaration signatures, including the exact beta cast and positivity assumptions, slots 0, 6 and 7, and the three separate residue hypotheses of `factor_units_of_zero`. It checks that the three-predecessor property is explicitly assumed in the proposed 82-to-86 existential equivalence, that `SameNoZero` quantifies over the stated models and supports the indicated bridge direction, and that the ring unit/discreteness ingredients carry their stated hypotheses. The checker does not elaborate Lean or exhaustively search for other lemmas.

As an independent mathematical control, the checker compares the literal external 82 and 74 graphs after the proposed partial valuation shift. It checks all unchanged gate rows and proves the small `qF`, `r0` and combined guard cancellations using sparse formal integer polynomials. These cuts, together with the topological graph correspondence, establish the partial-shift polynomial identity for those external JSON graphs over any commutative ring. They do **not** prove that the Lean expressions elaborate, denote those JSON graphs, or satisfy the corresponding model-level identity.

The partially shifted valuation makes the 74 inputs at indices 0, 6, and 7 successors and preserves indices 3, 8, and 11. Conditional on the cited own-zero and residue declarations, the stated first, strong, and auxiliary unit equations yield nonzero values in those latter indices by the arguments in the plan. To exclude `y=0`, the relevant ring of differences must be discrete; an arbitrary ordered ring can have units greater than one. The plan correctly calls out the need to supply discreteness and to turn nonzero model values into successor witnesses.

Since the audit was written, [additional source-only drafts](../../research/ordinary14-natural-forced82-predecessor-draft/README.md) have proposed the partial-shift identity, factor cuts, and the predecessor discharge from a represented positive beta. Their presence does not make these obligations checked: none has been elaborated, and their proof scripts, dependencies and integration into the endpoint remain open. This review observes their stated scope; its receipt does not validate those newer drafts.

The model-theoretic and internal-theory distinction is essential. Even a successful all-model transfer must be connected to the existing endpoint interfaces, their coherent providers and the actual iPRA derivability/axiom check. Neither this review nor the external graph checks bind symbolic ports to physical coefficient bytes or the displayed PDF.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural82-model-transfer-audit-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural82-model-transfer-audit-independent/result.json
```
