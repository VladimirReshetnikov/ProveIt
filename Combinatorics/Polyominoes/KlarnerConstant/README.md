# Klarner's polyomino growth constant

This project gives an exact rational certificate for the upper bound

\[
  \boxed{\lambda \leq \frac{9047}{2000}=4.5235}
\]

on Klarner's constant, improving the `4.5238` bound in Vuong Bui's 2026
seventeen-neighborhood recurrence system.  A detailed English proof is in
[`Research/klarner-bound-4.5235.md`](Research/klarner-bound-4.5235.md).

The `4.5235` bound appears to be new based on the dated public-source search
recorded in the research report; that novelty assessment is separate from the
proof.

The improvement changes no geometric recurrence.  It replaces Bui's rational
supersolution at `ζ = 1/4.5238` by a new, exact supersolution at
`ζ = 1/4.5235 = 2000/9047`.  Its seventeen coordinates have the common
denominator `10^7`, so the entire new numerical contribution is a short exact
arithmetic certificate.

## Formal and computational artifacts

```
Lean/KlarnerConstant.lean
Lean/KlarnerConstant/Asymptotic.lean
Lean/KlarnerConstant/Audit.lean
Lean/KlarnerConstant/BuiSystem.lean
Lean/KlarnerConstant/Certificate.lean
Lean/KlarnerConstant/CoefficientSystem.lean
Lean/KlarnerConstant/Concatenation.lean
Lean/KlarnerConstant/Counting.lean
Lean/KlarnerConstant/Convolution.lean
Lean/KlarnerConstant/GeometricComplete.lean
Lean/KlarnerConstant/GeometricDeletion.lean
Lean/KlarnerConstant/GeometricFourFiveCore.lean
Lean/KlarnerConstant/GeometricFourFiveGeometryCore.lean
Lean/KlarnerConstant/GeometricFourFiveGeometry.lean
Lean/KlarnerConstant/GeometricFourFive.lean
Lean/KlarnerConstant/GeometricLinear.lean
Lean/KlarnerConstant/GeometricPBasics.lean
Lean/KlarnerConstant/GeometricPCore.lean
Lean/KlarnerConstant/GeometricPEndpoint.lean
Lean/KlarnerConstant/GeometricPGeometry.lean
Lean/KlarnerConstant/GeometricPPartition.lean
Lean/KlarnerConstant/GeometricProfile.lean
Lean/KlarnerConstant/GeometricQ.lean
Lean/KlarnerConstant/GeometricQCore.lean
Lean/KlarnerConstant/GeometricQEndpoint.lean
Lean/KlarnerConstant/GeometricQGeometry.lean
Lean/KlarnerConstant/GeometricTwoDeletion.lean
Lean/KlarnerConstant/GeometricUCore.lean
Lean/KlarnerConstant/GeometricUGeometry.lean
Lean/KlarnerConstant/GeometricU.lean
Lean/KlarnerConstant/GeometricVCore.lean
Lean/KlarnerConstant/GeometricVGeometryCore.lean
Lean/KlarnerConstant/GeometricVGeometry.lean
Lean/KlarnerConstant/GeometricV.lean
Lean/KlarnerConstant/GeometricVW.lean
Lean/KlarnerConstant/GeometricWCore.lean
Lean/KlarnerConstant/GeometricWGeometryCore.lean
Lean/KlarnerConstant/GeometricWGeometry.lean
Lean/KlarnerConstant/GeometricW.lean
Lean/KlarnerConstant/Growth.lean
Lean/KlarnerConstant/Main.lean
Lean/KlarnerConstant/Patterns.lean
Lean/KlarnerConstant/Polyomino.lean
Lean/KlarnerConstant/PublishedSystem.lean
Lean/KlarnerConstant/Recurrence.lean
Lean/KlarnerConstant/SeededPartition.lean
Lean/KlarnerConstant/TranslationClasses.lean
Support/verify_certificate.py
Support/verify_certificate.wl
Research/klarner-bound-4.5235.md
```

- `Certificate.lean` defines Bui's exact seventeen-variable polynomial map and
  checks the new supersolution with ordinary kernel-reduced `norm_num` proofs.
  `Convolution.lean`, `Recurrence.lean`, and `BuiSystem.lean` prove the finite
  Cauchy-product estimates and monotone weighted-prefix argument; they never
  appeal to floating-point arithmetic or to convergence of a generating
  function.
- `CoefficientSystem.lean` states the seventeen pointwise coefficient
  recurrences term by term and derives the weighted-prefix system.
  `PublishedSystem.lean` records Bui's presentation literally—exact
  degree-one values and recursive inequalities for `n ≥ 2`—and provides a
  checked adapter to the all-index algebraic encoding.
- `Growth.lean` proves the generic passage from a pointwise exponential bound
  to the supremum of positive-index nth roots.  `Main.lean` deliberately keeps
  this part reusable: its `9047/2000` theorems accept either
  `WeightedBuiRecurrences` or `BuiCoefficientRecurrences` together with the
  required domination.  `PublishedSystem.lean` supplies the literal
  paper-facing `PublishedBuiRecurrences` adapter and endpoints.
- `Polyomino.lean`, `Patterns.lean`, and `Counting.lean` define finite
  edge-connected square-lattice animals, southwest normalization, Bui's
  required/forbidden offset patterns, finite normalized counts, and the
  marked-occurrence counts used as the actual seventeen coefficient
  sequences.
- `TranslationClasses.lean` constructs translation equivalence as a quotient,
  proves that every class has a unique southwest-normalized representative,
  and identifies `fixedPolyominoCount n` with the cardinality of the quotient.
- `SeededPartition.lean` proves the reusable finite lemma that grows disjoint
  nonempty seeds inside a connected cell set into disjoint connected
  territories covering the set.  The decomposition modules use those
  territories as the factors in explicit finite injections.
- `GeometricProfile.lean` packages the actual seventeen marked-occurrence
  sequences, proves their initial values and nonnegativity, and supplies the
  type-`G` domination of fixed-polyomino counts.
- `GeometricLinear.lean` proves the five same-size occupancy partitions for
  `F`, `G`, `H`, `R`, and `T`; `GeometricDeletion.lean` proves the `C`, `D`,
  and `E` inequalities by injective marked-leaf deletion.
- The `GeometricPBasics` → `GeometricPCore` → `GeometricPGeometry` →
  `GeometricPEndpoint` chain proves the multi-branch `P` inequality;
  `GeometricPPartition.lean` preserves its original combined import surface.
  The analogous
  `GeometricQCore` → `GeometricQGeometry` → `GeometricQEndpoint` chain proves
  `Q`, with `GeometricQ.lean` as its compatibility facade.
- The `GeometricFourFiveCore` → `GeometricFourFiveGeometryCore` →
  `GeometricFourFiveGeometry` → `GeometricFourFive` chain proves `S`.  The
  analogous `GeometricUCore` → `GeometricUGeometry` → `GeometricU` chain
  proves `U`.  The `GeometricVCore` → `GeometricVGeometryCore` →
  `GeometricVGeometry` → `GeometricV` chain and its corresponding `W` chain
  separately prove `V` and `W`; `GeometricVW.lean` preserves their former
  combined import surface.  Each convolution branch is
  an explicit map to a finite product or sum of marked connected territories,
  together with a recovery argument establishing injectivity.
- `GeometricTwoDeletion.lean` proves the `X`, `Y`, and `Z` inequalities by
  one- and two-cell deletion maps that retain enough marked coordinate data to
  reconstruct the source.
- `Concatenation.lean` gives an injective vertical stacking map and hence
  supermultiplicativity of `fixedPolyominoCount`.  `Asymptotic.lean` applies
  Fekete's lemma to negative logarithms, identifies the resulting limit with
  `growthSup`, and proves convergence of the conventional real nth roots.
- `GeometricComplete.lean` is the unconditional terminal composition.  It
  assembles all seventeen geometric recurrences for the actual coefficient
  profile and derives the pointwise bound, the `growthSup` bound, and nth-root
  convergence for `fixedPolyominoCount`, with no recurrence or domination
  hypotheses in those endpoint theorem statements.
- `Audit.lean` reports the assumptions of the principal public theorems.
- The Python and Wolfram Language scripts independently replay all seventeen
  inequalities using exact rational arithmetic.  They are reproducibility
  aids; Lean's kernel is the formal certificate boundary.

Focused validation from the repository root is:

```powershell
$env:LEAN_NUM_THREADS = '0'
lake build +KlarnerConstant
lake build +KlarnerConstant.Audit
py Combinatorics\Polyominoes\KlarnerConstant\Support\verify_certificate.py
wolfram -script Combinatorics\Polyominoes\KlarnerConstant\Support\verify_certificate.wl
```

## Trust boundary

The formal argument introduces no project axioms, `sorry`, `unsafe`
definitions, or `native_decide` boundary.  `Main.lean` exposes recurrence and
domination hypotheses because it is the reusable theorem for arbitrary
sequences.  They are not assumptions of the endpoint in
`GeometricComplete.lean`: the concrete finite geometry supplies them for the
actual polyomino counts before the certificate theorem is applied.  The
assumption surface of these constructions is limited to Lean/mathlib's
standard logical axioms such as `propext`, `Classical.choice`, and
`Quot.sound`.

There is one ordinary source-transcription boundary.  Lean proves all
geometric statements relative to the seventeen finite coordinate tables in
`Patterns.lean`; its kernel does not visually read Bui's PDF.  Those
required/forbidden offset tables were manually compared, entry by entry,
with the neighborhood diagrams on page 15 of Bui v2.  Once transcribed, the
local occurrence partitions, deletion and connected-decomposition maps,
normalization/recovery arguments, finite cardinal inequalities, translation
quotient, stacking injection, and Fekete endpoint are formal objects checked
from those coordinates.

## Source

Vuong Bui, [*A convolutional approach to bounding the number of
polyominoes*](https://arxiv.org/abs/2511.00461v2), arXiv:2511.00461v2,
6 May 2026.  Section 4 and Appendix B give the seventeen neighborhood types
and coefficient inequalities used here.
