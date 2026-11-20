# Analytic constructions: definitions and Lean proof path

This is a formalization blueprint, not a compiled analytic module. The compiled
finite rational kernel is in `lean/`. The complete human arguments are in
Sections 7 and 8 of the report (use the table of contents if numbering changes).
Every `Nat → ...` producer below must be specialized to a fixed primitive
recursive implementation, or represented by a bounded trace with a fixed clock,
before obtaining an object-iPRA theorem.

## 1. Rectangular kernels and their norm

Reuse `Step` from `MeasureBlueprint.md`. Define:

```lean
structure KernelStep where
  xLevel : Nat
  tLevel : Nat
  entries : Array Rat
  size_eq : entries.size = 2^xLevel * 2^tLevel
```

Flatten `(i,j)` as `i * 2^tLevel + j`. `refineKernel` repeats rows and columns
with the exact dyadic multiplicities. For an input step `u`, first refine
its level and the kernel's t-level to their maximum. `applyKernel K u` has
the kernel's x-level and row entries `sum_j K[i,j]*u[j] / 2^tLevel`.

`columnNorm K` is the maximum of the nonnegative rational values
`sum_i |K[i,j]| / 2^xLevel`. The maximum over an empty array is irrelevant
here because every dyadic dimension has at least one cell. Prove:

1. refinement invariance of `columnNorm` and `applyKernel`;
2. linearity of `applyKernel` in the input and kernel;
3. `norm1 (applyKernel K u) ≤ columnNorm K * norm1 u`;
4. the corresponding difference bound for two kernels;
5. compatibility with the L1-name equivalence relation.

The proof of 3 has a nested prefix-sum invariant. For each processed row,
bound the absolute weighted row sum by the row sum of absolute terms. Then
interchange the finite sums and use the certified column bounds. All
denominators are positive powers of two times the input denominators.

## 2. Neumann construction

Define `iterateOperator K 0 u := u` and
`iterateOperator K (n+1) u := applyKernel K (iterateOperator K n u)`.
The input/output levels may differ, so each application performs the defined
common refinement. Define `neumann K g n` by a primitive recursive accumulator
holding both the current iterate and the partial sum; this avoids recomputing
all earlier iterates.

Finite theorem targets:

- `iterate_norm`: the n-th iterate has norm at most `q^n * M`.
- `partial_norm`: the partial sum has norm at most `M/(1-q)`.
- `finite_residual`: `neumann - g - K(neumann) = -K^n(g)` as finite steps.
- `power_difference`: the telescoping identity for `A^n-B^n`.
- `neumann_perturb`: error at most
  `b*inputDifference + M*b^2*operatorDifference`.
- `geometric_block`: from `q≤1-1/b`, `b≥2`, derive `q^(bR)≤2^(-R)`.

The last result uses the finite Bernoulli inequality with the rational
number `1/(b-1)`, not analytic logarithms. Give PR symbols for the dyadic
shift `h`, source precision `s(k)`, and iteration count `N(k)` from the report.
The output sequence is `neumann (K (s k)) (g (s k)) (N k)`.

Prove the pairwise regularity estimate directly from finite comparisons at
two indices. Only then define its external completion interpretation. The
residual equation and uniqueness follow by the explicit error bounds; no
Banach fixed-point axiom is needed inside the arithmetic calculus.

## 3. Complex rational guards and quadrature

Represent a complex rational by two rationals. Define addition and
multiplication componentwise and inversion by
`(a,-b)/(a^2+b^2)` with a required positive denominator certificate.
The total coding convention uses zero for invalid inversions, but every
theorem has the nonzero guard in its antecedent.

`CNormLe z R` abbreviates `0≤R ∧ re(z)^2+im(z)^2≤R^2`.
Prove triangle, product, and guarded inverse inequalities by polynomial
identities and rational order. No exact rational square root is assumed.

For a real step `f` and a complex rational `z`, define `midpointTransform`
by refinement to level m and the sum of
`f[i] / (1-z*(i+1/2)/2^m) / 2^m`.
Define the derivative quadrature with kernel
`t/(1-z*t)^2`. The finite difference identities in the report prove:

- kernel magnitude bounds `b` and `b^2`;
- t-Lipschitz bounds `b^2` and `5*b^4`;
- transform input stability `b*norm1(f-g)`;
- transform z-stability `M*b^2*distance(z,w)`;
- the derivative remainder `M*b^3*|h|^2`.

For a represented input in `|z|≤r<1`, evaluate its approximants using the
wider guard `r'=(1+r)/2`. Require the input error below `r'-r`; its effect is
then bounded by the z-Lipschitz estimate. The wider guard also supplies all
small directions needed for complex differentiation at `|z|=r`.

## 4. Moments and Taylor output

`moment f j` is the exact rational sum
`sum_i f[i] * (right[i]^(j+1)-left[i]^(j+1))/(j+1)`.
Prove its agreement with finite polynomial integration by telescoping cell
antiderivatives. Then derive `|moment f j-moment g j|≤norm1(f-g)` using
`0≤t^j≤1` and finite integration.

The polynomial output uses one step approximant and one shared moment table.
Prove the finite geometric identity with remainder before invoking any
completion interpretation. The tail bound is `M*b*r^N`, and the same explicit
block-power schedule as the Neumann construction applies. A comparison of
two source precisions and two truncation lengths proves regularity.

## 5. Reverse error propagation

Use an array of graph nodes in topological order. Each node records its
predecessor indices, nonnegative rational sensitivities, and local error.
An output index selects the requested observation. The reverse loop starts
with output weight one and propagates `weight[v]*L[v,u]` to predecessors.

The invariant is the inequality expressing output error as processed local
residuals plus weighted unprocessed errors. Store both parts as finite sums
over explicit PR arrays. The successor proof substitutes exactly one
already proved local inequality. This yields the sum of weighted residuals
in O(V+E) rational operations without enumerating paths.

For a fixed graph, object proof compilation is finite application of
`Prf.subst` and `Prf.trans`. A uniform graph compiler needs its own bounded
checker and proof; it is a remaining implementation task. It cannot be
justified by reflecting arbitrary semantic Lean inequalities into iPRA.
