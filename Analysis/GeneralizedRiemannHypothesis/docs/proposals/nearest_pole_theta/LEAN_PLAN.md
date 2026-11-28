# Lean integration plan (specification, not checked Lean code)

Baseline: ProveIt `ef7d441dcb37ea944b7ac15731bb766f2e1354ea`. See `source_anchors.tsv`.

## Minimal drop-in change

Keep the exact public type in `src/Lib/Analytic/Landau.lean:217`:

```lean
lemma IsPolar.landau {r : ℂ → ℂ} (h : IsPolar E r) {β : ℝ} (hβ : 0 < β)
    (hr : ∀ x : ℝ, β < x → 0 ≤ (r x).re)
    (hE_le : ∀ᶠ v : ℝ in atTop, E v ≤ Real.exp ((β - 1) * v))
    {ρ : ℂ} (hρ : β < ρ.re) : r ρ = 0 := by
  -- Replace body via the lemmas below, after formalizing them.
```

The snippet reproduces the source interface only; it is not a complete Lean file. No new axioms, `sorry`, or unverified compiled module are supplied. Retain the declaration name initially; no call-site change in `Criterion.lean` is required.

## Stage 1: generic complex-analysis lemmas

1. **Genuine poles.** For a meromorphic total function `f`, work with its punctured germ at every point. If the limit of `(z-w)*f z` is nonzero, the singularity is a genuine simple pole. If the limit is zero, there is a removable representative; do NOT assert that the original assigned value equals this representative. Use the meromorphic order, or local analytic numerator/denominator factorization. Prove that the set of genuine poles is locally finite on the open domain. On a closed disk contained in the domain it is finite (compactness and local finiteness). At each point outside the genuine poles, choose its unique limiting value to construct a holomorphic representative; compatibility follows from uniqueness of limits. If Mathlib already supplies normalization, use it instead.
2. **Radial norm inequality.** On an open disk with `AnalyticOnNhd` holomorphic representative, use `hasSum_taylorSeries_on_ball` (already used in old `Landau.lean`) to express `G z` by its Taylor coefficients. If all coefficients are nonnegative reals, prove `‖G z‖ ≤ (G (‖z‖ : ℂ)).re` via finite partial sums, triangle inequality and limits, or existing `norm_tsum_le_tsum_norm`. Also prove the imaginary part of the real-axis value is zero. Explicitly assume `‖z‖ < r`.
3. **Nearest pole.** Choose a pole of minimal distance `r` to 0 from the finite nonempty set in the closed disk. The open disk of radius `r` has no genuine pole. For a nearest pole `w`, let `z(t)=(t/r)•w` for `0<t<r`. Apply the previous lemma, multiply by `r-t`, and pass to the left limit at `r`. The residue identity gives the left limit `‖Res w‖`; the right limit is `-(Res r).re`, including zero for removable `r`. This yields a strict contradiction if `(Res r).re ≥ 0`. One can state this as a lemma with an explicitly supplied residue function and punctured limits, avoiding a separate divergence theorem. For the full domination inequality, additionally note that the real-axis limit is real. Since `G` is the holomorphic representative on the open disk, use eventual germ equality along the radial paths; to avoid an issue with arbitrary pointwise values on the path, use the normalized representative from step 1. The normalized representative has the same residues (local holomorphic equality on punctured neighborhoods after filling removable points).

## Stage 2: derive local Taylor positivity

Reuse `exists_mul_exp_le` and optionally `exists_measure_laplace_eq` at one real center, never define the abscissa of convergence. For `A > max 2 β`, put `F(s)=K/(s-β)-Φ(s)` and `G(z)=F(A-z)`. The source's `IsPolar` includes the identity for `Re s > 2`. For all sufficiently small `z`, `G z = ∫ D(v) exp ((z-A)*v) dv` where `D(v) ≥ 0`.

Two alternative implementations:

- **Likely shortest:** retain the existing positive-measure constructor and the `iteratedDeriv_complexMGF` identity. Show `A` belongs to the interior of the exponential-integrability set using the already available convergence bound strictly to its right and left (take `A > β+2` if using that constructor literally). The sign of `X(v)=-|v|` and the composition `A-z` give coefficients `∫ |v|^k exp (-A*|v|) dμ / k! ≥ 0`. This uses only a local neighborhood of `A`; no global integrability proof, Taylor extension, supremum, or half-plane identity theorem is required.
- **Measure-light:** obtain the local integral identity directly using `integrableOn_laplace_of_abs_le` and the integral of the elementary exponential. Expand the integrand with domination as in the report, or prove finite-forward-difference positivity and take its limit to get the Taylor coefficients. The latter needs only finite sums of integrals and the elementary binomial finite-difference identity. Prefer whichever route is shorter with available Mathlib lemmas. Do not implement both in the initial port.

The theorem's arbitrary real β is positive, not necessarily <1; choose A larger than β+2 as necessary, in addition to the disk geometry requirement.

## Stage 3: geometry and source adapter

If `u=ρ.re > β`, choose real `A > max (β+2) (β+((u-β)^2+ρ.im^2)/(2*(u-β)))`. The disk centered at A of radius `‖(A:ℂ)-ρ‖` lies strictly in the half-plane β. Algebra on squared norms proves this directly; no choice of a convergence abscissa. If `ρ=A` its residue is zero by initial-domain analyticity. Otherwise use Stage 1 with `G(z)=F(A-z)`. The residue of `G` at `z=r` equals `rΦ(A-r)` (two minus signs). This is obtained by changing variables in the punctured limit. Apply `hr` because `A-r ≥ A-‖A-ρ‖ > β`. Contradiction. Preserve old `IsPolar.landau` signature.

## Stage 4: optional weaker criterion

Extract a separate lemma accepting `A` and sign control for `x ∈ Icc (A-‖(A:ℂ)-ρ‖) A`. Prove a variant of `New.LFunction_ne_zero_of_primeRemainder_le` with a supplied `d` satisfying `n_d(ρ) ≠ n(ρ)` and `n_d(x) ≤ n(x)` on the real interval in the report, rather than box zero-freeness. `isPolar_primeRemainder` supplies residues and the existing `entireL_ne_zero` handles real `x≥1`. This does not need a new selector: the old one proves the stronger contract. Implement only after the drop-in version builds.

## Validation gates

- Verify source manifest via `python3 verify_sources.py /path/to/ProveIt` (requires a local checkout at the pinned commit).
- Run `lake exe cache get`, `lake build`, `lake env lean scripts/PrintAxioms.lean` from `Analysis/GeneralizedRiemannHypothesis/Lean/grh` with its pinned toolchain. Compare with baseline on the same checkout; run `lake comparator --paranoid` following the upstream instructions. Check that all five public statements and the axiom set are unchanged. The upstream check record is https://math.mit.edu/~drew/shortgrh/; it does not certify this replacement or the modified determinant source in the current snapshot.
- Before deleting old auxiliary lemmas, search the entire checkout for all uses of each declaration. Measure non-comment proof lines and clean/warm build time before and after. Do not claim savings from deleting the old file before showing the replacement compiles and has no other callers.
- In tests of the generic lemma include `1/(1-z^4)` (sharp residue domination), `1/(1+z^2)` (positivity missing), an arbitrary assigned value at a removable point, and the real negative residue model for the original transform. The exact Python script tests finite algebra only.
