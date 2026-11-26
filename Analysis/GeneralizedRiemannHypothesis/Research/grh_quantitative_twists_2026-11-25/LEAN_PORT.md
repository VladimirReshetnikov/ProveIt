# Proposed Lean port (not compiled)

Target: readable `grh/` project, pinned source in `SOURCE_AUDIT.md`.

No Lean or Lake executable is available in this environment; this is a dependency map rather than a claimed verified `.lean` file. Do not import `Challenge.lean` (it intentionally contains `sorry` and is not imported by the proof).

## New univariate lemma

Use the source's `New.Selmer.gaussVal`, `rootRadius`, `radiusExponents`, `rootsOfValuation`, and `ellVal_eval_add_card_mul`. Prove a replacement lemma, with a finite index type `ι`, integral univariate polynomials `g : ι → (intQpBar ℓ)[X]`, a radius `ρ > 0`, budgets `B : ι → ℝ≥0`, tolerances `δ : ι → ℝ≥0` all positive, and `η : ℝ≥0` with `0 < η ≤ 1`.

The input uses a finite interval `Icc hmin H` with `1 ≤ hmin` and `rootRadius ℓ hmin ≤ ρ`; the conclusion is one `h` in the interval and strictly more than `(1-η) * totient (ℓ^h)` primitive roots satisfying the simultaneous valuation bounds relative to `gaussVal ρ (g i) + δ i`.

Use rational or nonnegative real arithmetic for shell weights and budgets. A finite budget ensures all Gauss valuations are finite; keep `ellVal` in `ℝ≥0∞` for evaluations and cap the excess before converting to finite reals.

1. **Capped root average.** For a root α of valuation `rootRadius ℓ h`, maximize the valuation of `ζ - 1 - α` on the finite primitive-root set. Use the ultrametric inequality and factorization of the cyclotomic polynomial derivative. Alternatively reuse the source's `gaussVal_eq_add_sum_roots` proof of `sum_min_ellVal_sub_le`, replacing radius 1 by the cap `C` (for `C ≥ 1`), to obtain the weaker sufficient bound `h+C` without a derivative API. Since `min (v(diff)-r_h) C ≤ min (v(diff)) C`, that proof also suffices.
2. **Root weight and slack.** For each `i,h`, define `w i h := card (rootsOfValuation (g i) (rootRadius ℓ h)) * rootRadius ℓ h` and `W i h` as the partial sum. Apply the source's Gauss root identity to show `W ≤ B i` and `gaussVal ρ (g i) - gaussVal (rootRadius ℓ h) (g i) ≥ (1-1/ℓ) * W i (h-1)`. Ensure the difference is finite and nonnegative before converting. The inequality follows from `rootRadius ℓ h ≤ rootRadius ℓ k / ℓ` for `k<h`.
3. **Bad-shell lemma.** Define good primitive roots by a decidable finite predicate requiring all valuation inequalities; if the bad count is at least `η * card`, sum the capped-excess ratios. At a bad point at least one ratio is strictly greater than one. Use `sum_lt_sum` and the averaging bound to derive the strict lower bound in equation (2.7) (see the labeled bad-shell inequality in `report.tex`). Handle infinite evaluations via the finite cap `C > B i + δ i`.
4. **Potential.** For `P h = ∏ i, (1 + c * W i h / δ i)`, prove `P h / P (h-1) > 1 + c*η/(h+C)` whenever a shell is bad. Use induction on a finite product to show `∏ i (1+x i) ≥ 1+∑ i x i` for nonnegative values. The easiest core sufficient hypothesis is the exact finite product `∏ h in Icc hmin H, (1+c*η/(h+C)) ≥ ∏ i (1+c*B i/δ i)`. The contradiction is then finite algebra. Derive the stated closed form separately using concavity of `Real.rpow` or a Bernoulli inequality.

## Coordinate and power wrappers

Reuse the architecture of `exists_ellVal_eval_update_le_add`, `exists_ellVal_eval_piecewise_le_add`, and `exists_rootsOfUnity_ellVal_eval_le_add`, but use per-constraint budgets instead of just the sum. Induct on the chosen coordinates. For multiplicity, return a finite set of good tuples; for each good prefix choose a set of at least `K` good extensions. Fibers of different prefixes are disjoint. The empty-coordinate case has one tuple.

For simultaneous powers, reuse the polynomial substitution and root-witness construction in `GeneralTheorem.lean:325–374` (`Ppow`, `exists_one_add_pow_eq`). Duplicate budgets across the type `ι × Set.Icc 1 m` and use depth `r/m`.

## Arithmetic wrapper

Retain the source's `exists_twistPolynomials` quantifier order. Choose `H` from budgets and error before selecting `N ≥ H` and `X`. In `Line.lean`, expose `X.auxPrimes.Nonempty` in the return of the construction or strengthen the structure: its actual `auxPrimes := J`, and `IsTiedPrimes.first_mem` gives the witness. Apply `X.isSmallTwist_twist` to every power of each selected tuple. To establish injectivity choose one `g_v` via `X.exists_eq_ofAdd_one v` and show all other `primeChar` are trivial there, as in `exists_mem_inertiaAbove_twist_eq`. Then `twist ζ g_v = ζ v` is independent of choice of tuple. Derive `ψ ^ ℓ ^ H = 1` directly from the product, not from the weaker internal `N` bound.

## Checks for a completed port

- Build with pinned `lean-toolchain` and Mathlib as described by upstream; use `lake env lean` for the new file and `#print axioms` for the new exported statements.
- Do not change upstream RH/GRH statements or assumptions.
- Verify that the strengthened theorem retains every source `IsSmallTwist` field; do not silently replace the source Selmer hypotheses by a generic elliptic-curve claim.
- Verify exact `H` (not internal `N`), common auxiliary set, count of distinct characters, and nonempty support. The arithmetic conductor statement may require a separate local character conductor lemma; it is not needed for the numerical selector itself.
