# Lean integration blueprint (not yet elaborated)

Target: readable package `grh/` at upstream commit `72fead102f663d5c7a407964a13dc0cf9d977207` (the current ProveIt import record points to `Analysis/GeneralizedRiemannHypothesis/Lean/grh`). This is a plan, not a compiled Lean patch. Preserve the original verified proof until the replacement passes the same checks.

## 1. Generic finite-dimensional lemma

In `New/Spanning/SecondMoment/FewTranslates.lean`, reuse the Hilbert–Schmidt vector, adjoint, trace, orthogonal-projection and norm identities. The generic statement should take:

- a finite group acting unitarily on a finite-dimensional complex inner-product space `T`;
- a symmetric equivariant projection `pr₀`, with `d = finrank ℂ (range pr₀)`;
- a map `P : S →ₗ[ℂ] T`, with `h = finrank ℂ S > 0`, and `Sram : Submodule ℂ S`;
- `IsNearIsometry (pr₀ ∘ₗ P) ε` and `d * (∑ g, ‖P* g P‖HS²) ≤ card G * ((1+ν)*h²)`;
- `h - finrank ℂ Sram ≤ γ*h`, all casts to reals, `0 ≤ ε < 1`, `0 ≤ ν`, `0 ≤ γ`.

Suggested new lemmas (names are proposals, not existing API):

1. `centered_orbit_covariance`: define `K0 = (card G)⁻¹ • ∑ g, (g ∘ₗ P) ∘ₗ (g ∘ₗ P).adjoint`; compress into `range pr₀` to obtain `K`. Establish `‖K‖HS² ≤ (1+ν)*h²/d` by grouping ordered pairs of group elements using the identity already in `inner_hilbertSchmidtVector_translate`. Use `hilbertSchmidtNorm_comp_orthoProj_le` twice, via adjoints. Prove `tr K ≥ (1-ε)*h`, `(tr K)² ≤ d*‖K‖HS²`. Expand the squared norm of `K - (tr K/d) • id` to get `≤ (ν+2*ε)*h²/d`. For the kernel use the near-isometry bound with `U = ker (pr₀ ∘ₗ P)`; this proves `h ≤ d/(1-ε)`.
2. `exists_centered_rank_increment`: for `F ≤ range pr₀`, let `u = 1 - finrank ℂ F / d` and `Ug = Sram ⊓ comap (Ag) F` with `Ag = (pr₀ ∘ₗ g ∘ₗ P).rangeRestrict` in the appropriate codomain. Use rank-nullity after restricting `Ag` to `Sram` and quotienting by `F`. Prove `dim Ug - ε*h ≤ tr (projF ∘ₗ Ag ∘ₗ Ag.adjoint)`. Average over `g`. Cauchy–Schwarz on the centered operators gives `tr(projF K) ≤ h*((1-u)*√(1+ν)+√((1-u)*u*(ν+2ε)))`. Use `Real.sqrt` monotonicity and `(√(1+ν))² = 1+ν` to prove `√(1+ν) ≤ 1+ν/2`. Obtain the precise real inequality (7) in the report. Use the mean-value principle over a nonempty finite group to choose one `g`.
3. `exists_centered_cover`: abstract the iteration as a finite set recursion with state `(J,F)` and `F = ⨆ g ∈ J, map Ag Sram`. When deficit is greater than `θ`, add a translate with positive gain at least `c*h*u`. Since the gain is positive, `g ∉ J`. If the goal holds, freeze the state. For `N = ceil ((d / (c*h)) * log (1/θ))` prove `deficit ≤ max θ (exp (-N*c*h/d))` by induction; `1-z ≤ exp(-z)` for `z ≥ 0`. This can also reuse the general iteration infrastructure without retaining the particular `IsSpread` wrapper. Use `h ≤ d/(1-ε)` for the ceiling cost. All ranks must be over ℂ; no rational bases or integer vector norms are needed.

The report's deterministic proof uses no spectral decomposition. The random-product alternative is optional and should be a separate proof if implemented.

## 2. Bridge to existing automorphic hypotheses

`New/Spanning/SecondMoment/SpanningTheorem.lean`:

- `isNearIsometry_e₀_comp_scaledPoincare` (line 257), epsilon `5*b⁻⁴`;
- `targetDim_mul_sum_hilbertSchmidtNorm_sq_le` (line 288), nu `9*b⁻⁴`;
- `finrank_targetForms_ne_zero` (line 307);
- `comap_scaledPoincare_eq_comap_goodPoincare` (line 314), nonzero scaling and source coordinate equivalence.

In `New/Reduction/ShortAndEnough.lean` transport the ramified source submodule to `S` via `D.sourceFormCoords`. Use the codimension bound from the current `exists_le_finrank_iSup_range_normalizedPoincare` (line 410): `h-h_r ≤ D.f/(D.N-1)*h ≤ b⁻⁸*h`. `range_normalizedPoincare` (line 386) identifies the relevant images. Specialize the generic lemma at `c=1-5/b`, `θ=(1+2*D.x₁^2*D.b)⁻¹`.

Suggested replacement statement, in mathematical notation (all casts need elaboration):

```
exists J : Finset D.chosenGL,
  |J| * finrank ℂ D.ramifiedSourceForms ≤ 3 * D.targetDim * D.logB
  and (1-θ)*D.targetDim ≤ finrank ℂ (sup over J of normalizedPoincare ranges)
```

The original `enough_forms` can be retained unchanged or derived with a smaller target `b⁻²` in the new lemma. Do not weaken the near-isometry or moment inputs without a separate proof.

## 3. Weaken only the completion step of Theorem C

`New/Determinant/Twist/LongForms.lean`, `integral_forms_long` (line 214): copy its theorem and proof with the rank hypothesis replaced by

```
h_budget : (D.targetDim - n : ℝ) * (2 * D.x₁^2 * D.b^2 + D.b)
           ≤ D.targetDim * D.b
```

Here the subtraction must be in reals, or establish `n ≤ D.targetDim` first and use a natural-number subtraction with the appropriate cast. After `exists_extend_basis_of_span_eq_top` provides `n'`, obtain `n' = D.targetDim - n` as a real equality from `h_card`. The proof preceding `h_nonneg` does not use the original `hn`; retain it. Replace the use of `mul_completion_cost_le hn h_card` by the supplied budget and keep the same final `linarith`. The existing theorem can become a wrapper using the old completion-cost lemma. Do not alter `HasSmallRatios`, `HeightLe`, `IndexLe` or `CovolumeLe`.

## 4. Top-level substitution

`New/Reduction/MainInequality.lean`: reuse the basis selection from the union of images of short source vectors, the bound on each conjugate norm, and `TwistedLattice.covolumeLe_of_normSqAt_le`. Use new translate count to get an index allowance `6*D.targetDim*D.f*D.a*D.logB^4` (not `6 * errorUnit`). Derive budget with `θ = (1+2*x₁²*b)⁻¹`. Use the budget theorem from step 3. The arithmetic at the end is

```
n * (m * rem) ≤ D.targetDim * (16 * loss)
n ≥ (32/33) * D.targetDim > 0
=> m * rem ≤ 17 * loss
```

This proof uses `D.mainAmount_nonneg`, so the `n-D.targetDim` main term may be discarded with the correct sign. Prove the needed large-scale real inequalities via `D.le_of_hasLogBound` or the eventual threshold in `OneSidedBound`; the exact rational parts are tested by the bundled script.

Keep `star_inequality` as a wrapper if `17 ≤ D.logB` is available. Alternatively use `star_inequality_centered` directly in the next file.

`New/Reduction/OneSidedBound.lean`: change `Data.primeRemainder_le` to the RHS `17*φ(q₀)*D.logB^5/D.m + abs(...) + D.logB*abs(...)`. In `eventually_primeRemainder_natCast_le`, use `544*φ(q₀)+3` and `-1/2+5*ε` in place of the old constants. Choose the smaller positive exponent `ε` before passing to the real statement. Keep `New.grh` and `New/Reduction/Zeros/Criterion.lean` unchanged, as well as the five public theorem types.

## 5. Acceptance checklist

1. Verify anchors: `python3 verify_sources.py /path/to/upstream/grh`.
2. Use the exact pinned Lean v4.35.0 and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679` with the existing `lake-manifest.json`.
3. `lake exe cache get`, `lake build`, `lake env lean scripts/PrintAxioms.lean`.
4. Check that the exported statements match the challenge and no new axioms occur. `lake comparator --paranoid` in a suitable sandbox. The readable edition's external checker has substantial memory requirements; see Sutherland's report.
5. Trace imports from `Main.lean` to ensure the new proof is actually used, rather than the verified old proof being called to establish the result. Preserve old proof as a reference, not as a dependency of the new upper-level inequality.
6. Compare source, elaborated proof term, reachable declaration counts and checker time separately. The note asserts mathematical savings, not measured implementation speedup.
