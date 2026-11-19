# Lean formalization outline

`CuboidSurface.lean` gives explicit definitions and theorem statements for the
same mathematical problem as the report. It is an **uncompiled outline**;
it is not a machine-checked proof. Every substantial unfinished theorem has
an explicit `sorry`. No unfinished theorem is disguised as an `axiom`, and
no numerical optimizer is assumed to return a correct answer.

## Target environment

- Lean: `leanprover/lean4:v4.36.0`.
- Mathlib commit: `6c9a0a07bbbce9b0205b16c83a17b8458f4bcdf9`.

The APIs below were inspected in the source at that exact commit:

1. [`Mathlib/Topology/EMetricSpace/BoundedVariation.lean`](https://github.com/leanprover-community/mathlib4/blob/6c9a0a07bbbce9b0205b16c83a17b8458f4bcdf9/Mathlib/Topology/EMetricSpace/BoundedVariation.lean)
   defines `eVariationOn`, `BoundedVariationOn`, and the interval variation
   machinery. Its blob SHA is `c4b5ad4ac4e19ed0b732ac20b521f0f8b30410cd`.
2. [`Mathlib/Analysis/ConstantSpeed.lean`](https://github.com/leanprover-community/mathlib4/blob/6c9a0a07bbbce9b0205b16c83a17b8458f4bcdf9/Mathlib/Analysis/ConstantSpeed.lean)
   develops constant-speed parameterization and `naturalParameterization`.
   Its blob SHA is `5a8bcfad3af7c317380df08eb6cdefde1bc4c7b8`.
3. [`Mathlib/Analysis/InnerProductSpace/PiL2.lean`](https://github.com/leanprover-community/mathlib4/blob/6c9a0a07bbbce9b0205b16c83a17b8458f4bcdf9/Mathlib/Analysis/InnerProductSpace/PiL2.lean)
   defines `EuclideanSpace` with the L² norm and the notation `!₂[x,y,z]`.
   Its blob SHA is `0d550d11f9ab01d02d446129a5eb5972551c17f5`.

Source inspection validates the named APIs, not the compilation of the
whole outline. In a project pinned to those versions, the intended check is
`lake env lean CuboidSurface.lean`. The remaining `sorry` declarations must
then be replaced and the resulting complete file checked again. No Lean
installation or project cache was available during preparation of this
archive, so no successful compilation is claimed.

## Why these definitions express the actual question

`Surface` is the boundary of the closed rectangular box in
`EuclideanSpace ℝ (Fin 3)`. Using the default norm on `Fin 3 → ℝ` would
silently give a sup norm; the outline deliberately uses the Euclidean L²
space instead.

A `SurfaceCurve` is continuous on `[0,1]`, has fixed endpoints, and stays on
that boundary at every parameter value. Its extended length is
`eVariationOn γ (Icc 0 1)`, the supremum of all finite partition sums of
Euclidean chord lengths. Thus curved paths and infinite-length paths are
included, and a path through the solid interior is inadmissible.

`intrinsicEDist` is the infimum of those lengths in `ENNReal`. The theorem
`intrinsicEDist_ne_top` must be established before reasoning with its real
value `intrinsicDist`. This avoids relying on the convention
`ENNReal.toReal ⊤ = 0`. The main statements explicitly restrict every
endpoint to `Surface`.

The scalar root is not an abstract oracle: `rootFunction` is the exact sum
of three clipped square roots in the report, `rootCut` is its explicitly
defined upper level set, and `rootSquared` is the infimum of that set.
`root_existsUnique`, `rootSquared_spec`, and `rootSquared_comparison` give
existence, the exact equation, a finite bracket, and the comparison rule
needed for certified bisection. Every endpoint coordinate is then an
explicit arithmetic expression in that uniquely determined real number.

## Dependency plan

| Milestone | What to formalize | Method |
|---|---|---|
| M1 | Finite intrinsic distances, shortest curves, reflection isometry | Explicit face/edge paths; constant-speed compactness; variation lower semicontinuity; reflect admissible curves |
| M2 | Exact four-image fixed-vertex distance | Prove no repeated face; exclude internal positive-curvature vertices; enumerate ten face words; six domination identities; C/D validity inequalities |
| M3 | Fixed-vertex global maximum and equality cases | Convex nearest-image cells; boundary formulas; only interior vertices U,W; polynomial gap factorization |
| M4 | Exact five-image antipodal distance | Enumerate simple face words; retain validity conditions; dominance on the quarter-face |
| M5 | Reduction of the global diameter to antipodal quarter-face pairs | Compactness; invariant Jordan curve and Brouwer fixed-point argument; local flat continuation for the stronger antipodal theorem; explicit bounds on the other faces |
| M6 | Scalar optimum and coordinates | Square-root signs; monotonicity and intermediate value; root cutoff; five inequalities and equality at the witness |
| M7 | Optional radical simplification | Substitute, retain all nonnegative sign conditions, then use `ring` and `nlinarith` |

The full human proofs of the geometry and optimization are in the report.
The formal plan does not treat those arguments as already provided by
Mathlib. In particular, M2, M4, and M5 are the main geometric development
work, not routine `simp` steps. M5 may be replaced by a direct finite
cuboid-specific diameter certificate if that is easier than importing and
adapting the relevant topological results; either route must establish the
same stated theorem.

For M1 one can alternatively begin with finite facewise polygonal paths,
prove equality with the continuous-path metric by local flattening and
polygonal replacement, and then prove the finite-word unfolding formulas.
That is a proof strategy, not a change in the final distance definition.

## Main theorem interfaces

- `fixed_vertex_maximum`: the selected witness is farthest from the origin,
  and its distance is the displayed `vertexRadius`.
- `fixed_vertex_all_maximizers`: includes the two-point transition case.
- `free_endpoints_maximum`: the two displayed antipodal witnesses realize
  the global diameter and have distance `diameterValue`.
- `strict_improvement_iff`: allowing both endpoints to move gives a strict
  improvement exactly when `rootFunction s (baseSq s) < s.c`.

Sorting and the choice of starting vertex cause no geometric restriction.
After these theorems, add signed coordinate permutations as explicit
Euclidean isometries, transport surface curves through them, and apply
`intrinsicEDist` invariance. The report and Python program already spell
out the corresponding coordinate conversion.

The only complete-looking tactic proofs supplied are short real-polynomial
identities and basic definitional facts. They are useful starting points,
but even these are not advertised as compiled in this deliverable.
