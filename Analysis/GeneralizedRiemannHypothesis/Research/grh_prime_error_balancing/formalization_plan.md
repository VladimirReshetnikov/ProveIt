# Lean formalization plan (not compiled)

Use `grh-compact` at revision `72fead102f663d5c7a407964a13dc0cf9d977207`; toolchain Lean v4.35.0 and Mathlib revision 56a005855ea17e0b0958f73ec801ae140b0a1679 as reported in README. The existing theorem `LFunction_eq_zero_re : DirichletLZerosOnLine` supplies zero location. Avoid importing `Challenge.lean`.

## Suggested decomposition

1. `RampError.lean`: finite ramp sums indexed by reduced residue classes, continuity at integer cutoffs, Dirichlet-series character inversion, Laurent regular part at 1. Compare `New.Endgame.PrimeError` and `isPolar_primeError`. Establish the ramp Mellin kernel independently.
2. `CriticalExpansion.lean`: use completed-function local partial fractions and the classical zero-count bound, contour shift to any `δ ∈ (0,1/2)`, and absolute summability of grouped multiplicity vectors. Give separate lemmas for the imprimitive Euler factors and horizontal contour heights.
3. `SpectralRank.lean`: Hadamard logarithmic derivative; cancellation of noncentral multiplicities; gamma recurrence; rational-function/exponential-decay rigidity; uniqueness of Dirichlet series; Dirichlet character orthogonality. No GRH hypothesis for this module's main rank theorem. Use primitive induction to transfer to all characters of a fixed modulus.
4. `UniformMoments.lean`: generic theorem on absolutely summable `c : Γ → (ι → ℂ)` with signed frequency map, reality symmetry and full real rank. Uniform average of a nonconstant exponential ≤ `1 / (H * |ω|)`. Prove uniform first and second moments via finite truncation and product series. Establish the positive minimum of the quadratic form on the real unit sphere. Add the decaying remainder and separation theorem.
5. `ConvexBalance.lean`: use finite-dimensional compactness, convex separation and Carathéodory. The main shape is `closedBall bias r ⊆ convexHull ℝ (F '' Set.Icc (T-H) (T+H))`, in the Euclidean vector space indexed by reduced classes; the finite witness has at most `Fintype.card ι + 1` terms.
6. `ZeroKernel.lean`: convolution of uniform probability measures, support addition, Fourier transform sinc identity, product bound, sum-integral interchange, zero count and partial summation.
7. `NonSplitApplication.lean`: finite class weights and geometric tails for exceptional prime powers; transfer the vector theorem to the repository's `primeError`.

The module names and mathematical statement shapes are proposed interfaces, not verified Lean identifiers. Substantial analytic infrastructure is required, especially contour shifting, Hadamard factorization, completed Dirichlet L-functions and zero counting. Check existing Mathlib and `src/Lib` before implementing. Validate dependencies via `#print axioms` on each exported theorem. No `sorry`-filled executable Lean file is supplied or represented as a proof.
