# Lean formalization roadmap (not checked)

The upstream package is the vendored readable edition of lsernau/grh-lean,
commit 72fead102f663d5c7a407964a13dc0cf9d977207, Lean 4.35.0 and Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679. Do not import it from ProveIt's
root project without resolving the toolchain/Mathlib mismatch. Work in the
separate Lake project. The following exact interface is present in its
`src/Main.lean` (as inspected via GitHub):

```
riemannHypothesis : RiemannHypothesis
LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf
LFunction_eq_zero_re : DirichletLZerosOnLine
```

Suggested modules and obligations:

1. **FiniteDesign** (Mathlib only). Use finite index types `I` (samples) and `J`
   (characters). Define a matrix `A : I → J → ℂ`, weights `μ : I → ℝ`,
   `0 < μ i`, `∑ i, μ i = 1`, and `‖A i j‖ = 1`. Define finite weighted
   absolute sums, restriction sums, and `A h` by finite sums. Define the
   Gram entry `∑ i, (μ i : ℂ) * conj (A i j) * A i l`. Abstractly assume
   diagonal one, off-diagonal norm at most δ (δ nonnegative). For character
   matrices derive this by the quotient character formula.
2. **CalibratedDecoder** (unconditional). First prove the coordinate inequality
   `(1+δ)*‖h j‖ ≤ weightedL1 (A h) + δ * l1 h` from the Gram identity.
   Sum over a finite set `S` with `S.card ≤ k`; use triangle inequalities
   on S and its complement to bound the coefficient objective difference.
   For a finite error set E prove the residual difference using the reverse
   triangle inequality on E, and the dense-noise inequality off E.
   Combine by ring normalization and inequalities to get, for all z,
   `(1+δ)*(J z - J c) ≥ Γ * l1 (z-c) - 2*(1+δ)*tail - 4*k*η`,
   with `Γ = 1-(2*k-1)*δ-4*k*α` (cast k to real before subtraction).
   The estimate for a minimizer uses only `J z ≤ J c`; compactness and
   coercivity can be proved separately. This formulation avoids an API
   dependency on optimization solvers.
3. **Sharpness** (unconditional). Prove the Gram lower bound for a vector
   with support cardinality ≤ r via finite Cauchy--Schwarz; the upper bound
   on each row follows from norm-one entries. For a character subgroup H,
   prove the finite character sum over H is its cardinality on H-perp and
   zero elsewhere (multiply the sum by a nontrivial character value).
   Prove the exact biased design and the lightest-coset collision separately.
4. **PrimeBias** (analytic). Define the C² compactly supported polynomial bump
   w; define g_X and its Mellin transform; prove endpoint decay and uniform
   estimates by two integrations by parts. State the classical explicit
   formula as a lemma to be proved, not an axiom. Use conductor reduction,
   zero counts, and `LFunction_eq_zero_re` and `riemannHypothesis` from
   `Main` to get the smoothed bound; remove prime powers with Chebyshev.
   Normalize positive weights and prove the quantitative bias corollary.
5. **Thinning** (finite probability). Formalize independent Bernoulli
   variables on the finite Boolean cube, exponential potential, and the
   conditional-expectation choice by induction on the sample set. The
   existence argument is simpler than formalizing certified numerical
   approximations. Combine with PrimeBias and CalibratedDecoder.

No Lean executable was installed in the working environment, so this is a
roadmap, not an executable or verified formalization. The analytic bridge is
a substantial formalization task even though the classical proof is short.
