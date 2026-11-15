# Effective analytic interfaces

`AnalyticInterfaces.lean` is an **uncompiled specification and proof outline**.
Its propositions ending in `Goal` are obligations, not proved theorems. The
file contains no added axioms or placeholder proofs. It supplements the finite
definitions in `Outline.lean`; if the files are moved into a qualified Lake
namespace, update its `import Outline` accordingly.

## Names and the first-order schema

`RawName` is a precision-indexed pair of rational endpoints. `ValidName`
requires pairwise compatibility and interval width at most `2^(-k)`.
Pairwise compatibility works without constructing a real-number completion.
`nameLE` and `nameEq` express represented order and equality. `PositiveBound`
contains an actual positive rational and a finite interval witnessing its
validity; it never searches indefinitely for evidence that a denominator is
nonzero.

The structures quantify over Lean functions only in the external specification
language. For the internal iPRA schema, fix each primitive recursive sampling
family and modulus, compile that specific program, and translate its contracts
to first-order assumptions. An arbitrary function `Nat → Rat` is not thereby
primitive recursive. The code does not assert a primitive recursive universal
evaluator for every primitive recursive program.

Pointwise interval addition, multiplication, powers, and absolute value are
defined. They preserve enclosures but can enlarge the width multiplier.
`boundedRaw` records both a numerical endpoint bound and that multiplier;
`rootName` explicitly reindexes the input and uses a bounded rational root
scan. `RootGoal` asks for its enclosure, compatibility, and power identities.
Every later use must establish the indicated bound, not silently assume that
all interval operations preserve normalized precision.

All parameters called `pi` must be instantiated with the particular circle
constant constructed in the planar paper and its verified interval name.
The file now gives its actual finite algorithm as `canonicalPiLower` and
`canonicalPiName`: iterate dyadic lower square roots of `(1+c)/2`, enlarge
the final cosine approximation by the stated error, and compute the lower
polygonal sine approximation. `CanonicalPlanarGoal`, `CanonicalWignerGoal`,
and `CanonicalCapGoal` fix this algorithm explicitly. `CanonicalPiGoal` and
the identification with circle perimeter/area remain proof obligations.
Merely choosing an arbitrary positive named number is insufficient for planar
isoperimetry or the support-function interpretation. The elementary Taylor
functions are explicit finite sums; the conversion between them and the
dyadic-circle name is an obligation of the elementary-constants module.

## Presentation records and their obligations

| Definition | Supplied data | Required bridge or theorem |
|---|---|---|
| `PolygonalPresentation` | Rational polygons, certified upper edge lengths, area and length names, explicit errors | `PlanarPresentationGoal`; additionally the report's compatible Jordan-domain or lower-real interpretation for a claim about a geometric boundary |
| `SupportC2Presentation` | Rational support polynomials, samples of derivatives of orders 0–2, uniform approximation and bounds, a positive curvature-radius bound, named geometric quantities | Finite trigonometric and polygonal-area identities establish the quantity bridges; `WignerPresentationGoal` gives the improved inequality and constant-width equality |
| `BoxAlgorithms` | Common-grid dissection and finite containment programs | `BoxAlgorithmsGoal`, proved by endpoint sorting, occupied-cell testing, and positive-volume box semantics |
| `omegaName` | Explicit inner/outer dyadic grids in `[-2,2]^d` | `BallGridGoal`, including positive volume of the inner grid and the `3*d^2*4^d*2^(-m)` error bound |
| `OuterVolumePresentation` | Named volume/perimeter, positive volume certificate, inner boxes, outer boxes, containments, and a tube modulus | `OuterIsoperimetricGoal`, using finite Brunn–Minkowski and the report's precision budget |
| `LayeredData` | Ordered positive levels, nested volume names, perimeter names and each layer's isoperimetric inequality | `LayeredSobolevGoal`, through finite weighted Hölder/Minkowski and the named-root routine |
| `SobolevApproximation` | Named target norm and gradient integral, layered approximants, explicit norm and variation inequalities | `SobolevPresentationGoal`; the variation condition must be proved for the intended analytic family |
| `CapData` | Positive radius, named angle in `[0,pi]`, explicit sine/cosine approximation | `SphericalCapGoal`, in the denominator-free form `R²L² = 4*pi*R²*A − A²` |

The outer-volume record does not assume positive volume for every coarse inner
approximation. Before invoking the finite Brunn–Minkowski theorem, select a
precision with `2^(-k)` smaller than half the supplied volume lower bound.
The approximation contract then proves that the first box union has positive
volume. `BallGridGoal` and the positive rational dilation prove positive volume
of the second input. This addresses the nonempty-input requirement even when
the rational Brunn–Minkowski parameter is zero.

`LayeredData` stores only the numerical content of nested regions. Its layer
isoperimetric hypotheses are discharged by the outer-volume theorem (or by a
direct finite theorem for a decidably empty layer). Its norm uses

```text
t^(d/(d-1)) = root_(d-1)(t^d),
norm = root_d(moment^(d-1)),
```

so no arbitrary real exponent operator is needed. The deliberately large
`layerBudget` must still be proved to majorize the intermediate endpoint and
width bounds. Finite grid functions additionally require the common-grid
face-incidence construction. `GridCoareaGoal` is the exact equality between
the layered jump sum and the face sum `area * abs(value_plus-value_minus)`;
the supplied face list must be checked against that incidence construction.
An arbitrary face list does not satisfy the goal. The source makes this
explicit with `GridCoareaCertificate`: adjacent values are nonnegative and
are zero or listed levels, and each layer perimeter equals the sum of exactly
the faces crossing that level. `GridCoareaGoal` is conditional on this finite
incidence certificate. The geometric face builder must also be checked
against the actual common-grid cell adjacency and exterior zero values.

For a classical `W^{1,1}` interpretation, prove the explicit `normApprox` and
`variationApprox` fields. Axis-aligned step approximations alone can converge
to anisotropic variation and do not automatically establish the Euclidean
gradient bound. The record makes this missing implication visible.

Spherical cap unions require the finite geometric contract that interiors are
disjoint and boundary lengths add. Sum the individual cap identities; the
remaining deficit is the explicitly nonnegative sum of cross terms in the
report. The complement changes area to `4*pi*R²-A` and leaves the polynomial
right side invariant. No general spherical rearrangement theorem is supplied.

## Completion order

1. Elaborate the two outline modules in the pinned Lean/Mathlib environment.
   Fix syntax/API issues before describing any file as compiled.
2. Complete the natural-number codecs and the internally proved rational
   arithmetic, interval, bounded-search, and root routines.
3. Complete the finite theorem kernels from `Outline.lean`, especially the
   polygon theorem, Wigner coefficient identities, and rational-box theorem.
4. Prove the enclosure and primitive recursive majorant obligations for every
   analytic interface above. Validate the actual geometry-to-data bridges.
5. For each fixed presentation, introduce the requested precision, compute the
   finite index prescribed in the report, and prove its rational inequality
   using quantifier-free induction on bounded Boolean folds.
6. Construct the actual embedded `Prf PRAAx [] ...` derivations and only then
   apply the repository's `pra_iff_native` translation. Record build logs and
   audit axioms. External Mathlib theorems and executable tests are distinct
   evidence and cannot replace this step.
