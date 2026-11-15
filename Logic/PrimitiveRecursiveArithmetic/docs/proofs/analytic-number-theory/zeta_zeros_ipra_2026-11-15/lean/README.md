# Lean roadmap and exact completion target

**Status: uncompiled interface, not an implemented analytic formalization.**

The inspected ProveIt snapshot is
`b5a3ad037723c44d69a3d5b28a950c554327a989`. It specifies Lean and mathlib
`v4.32.0`. The exact inspected import is:

```lean
import ConciseIPRA.NativeBiInterpretation
```

The namespace is `LeanProofs.ConciseIPRA`. The required proof object for a
closed arithmetic sentence `phi` is:

```lean
Prf PRAAx [] phi
```

The existing `pra_iff_native` transports it into
`NPrf [] (NFm.ofPRA phi)`. A theorem in ambient Lean about `Complex`, an
evaluation of a Python program, or a proof of the standard-model semantics
of a PR program is not that object-language proof.

## Interface supplied

`ObjectTargets.lean` supplies finite rational/contour data types, sentence
constructors for a fixed PR checker, a separate validity sentence for the
contour generator, and a `Completed` structure containing the required
internal proofs. No instance of `Completed` is constructed. The generic
PR terms in its interface must be replaced by the actual compiled programs
and proved to implement the contracts in the report. Choosing an arbitrary
constant-one checker would not satisfy those semantic obligations.

## Implementation order

| Proposed module | Work and exit criterion |
| --- | --- |
| `ZetaZeros/Arithmetic.lean` | Compile integer/rational/list codes, exact complex-rational arithmetic, gcd, bounded loops, finite products and rational comparisons into `PR`. Prove their defining equations and order/error lemmas in `Prf PRAAx`. |
| `ZetaZeros/ElementaryEnclosures.lean` | Formalize log/exp/pi approximation schedules, dyadic rounding and L1 ball propagation. Keep Euclidean-to-L1 conversion explicit. Each exported routine has a symbolic precision theorem. |
| `ZetaZeros/EulerMaclaurin.lean` | Prove finite summation-by-parts identities, Bernoulli recurrence, the rational coefficient bound, and finite zeta error/derivative estimates. |
| `ZetaZeros/ThetaXi.lean` | Implement the included functional-equation proof and its finite contracts: Gaussian theta, Mellin identification, reciprocal gamma, xi symmetry and entire approximants. The upstream ZIP is not already a kernel-checked implementation. |
| `ZetaZeros/PolynomialAlgebra.lean` | Compile squarefree gcd, coefficient bounds, coordinate annihilator matrices, bounded real-root bisection, characteristic-polynomial zero tests, frozen-derivative Newton, and the finite root-list argument from the report. The degree is a variable numerical input. |
| `ZetaZeros/Winding.lean` | Implement the signed rational ray-crossing sum; prove subdivision, homotopy and product invariance by finite edge cancellation. Formalize polynomial counts and transfer through positive-margin approximation. |
| `ZetaZeros/MinimumModulus.lean` | Prove finite polynomial Jensen, Blaschke factor cancellation, the explicit Harnack Fourier-series estimate and the degree-independent lower bound. |
| `ZetaZeros/RegularHeights.lean` | Compile candidate heights, predetermined precision and mesh. Prove a candidate passes, then prove complete xi contour validity and integer count. This is separate from conditional count soundness. |
| `ZetaZeros/GammaArgument.lean` | Formalize the finite complex Euler--Maclaurin log-gamma identity, its real normalization constant, and the explicit theta error. Do not reset the argument to a principal value. |
| `ZetaZeros/Counting.lean` | Prove the exact winding identity, the real polynomial crossing bound, and the finite `CountCheck` sentence stated in the report. |
| `ZetaZeros/Consequences.lean` | Prove monotonicity, local counts, separated positive-count bands, growing-window inequalities and the reciprocal-tail/Cauchy sentences. |
| `ZetaZeros/RootNames.lean` | Compile the global minimum-modulus subdivision, positive-child selection and explicit Cauchy/residual schedule, obtaining pairwise apart zero names in the disjoint height bands. |
| `ZetaZeros/Transfer.lean` | Construct the actual final `Prf PRAAx [] phi` terms and apply `pra_iff_native`. Audit kernel dependencies and compile at the pinned toolchain. |

The dependency between polynomial algebra and winding is not circular:
polynomial root existence uses only elementary finite polygon winding;
the polynomial argument principle is proved after root-list completeness.
Jensen/Harnack and analytic zero selection come after that.

## Quantifier-free induction discipline

Freeze numerical size and precision parameters before induction. Use
invariants about coefficient arrays, rational inequalities, integer partial
sums, degree decreases, or Boolean folds. Compile bounded conjunctions as
fixed PR characteristic functions. Do not apply induction to a statement
quantifying over every approximation precision. Fixed analytic functions
and fixed Cauchy-name definitions give schemas; no universal evaluator for
arbitrary PR program codes is introduced.

## Suggested first implementation milestone

Implement the exact-rational simple-zero certificate and its local
contraction proof first. Its three zeta evaluations, rational error
inequalities and division by an explicitly nonzero rational slope provide
a small vertical slice through arithmetic, Euler--Maclaurin and named
roots. This is useful independently of the far larger general contour
constructor. It does not replace the uniform distribution proof.

## Build placement

Place the new modules under the existing ConciseIPRA Lean project, using
its pinned `lakefile` and dependency configuration. Then add the interface
module to that project's build targets. This package deliberately does not
ship a second independent, untested lake configuration or copied transitive
dependencies.

Completion requires kernel-checked internal derivations, no `sorryAx`, and
no added analytic axioms. This delivery reports none of those future gates
as already passed.
