import FabiusFunction.SpectralZetaWeighted
import FabiusFunction.NewtonBasisGeneratingFunction

/-!
# The spectral zeta of a Newton-basis weight

The exponent-sequence volume's Newton--Rvachev factorization theorem
gives the spectral zeta of a polynomial weight in closed form:

`Z_P(s) = ζ(s) · ∑_{r ≤ d} c_r · 2^s / (2^s - 1)^{r+1}`   (`p1:eq:ZP`)

This is the composite of two identities that are already formal, and
nothing else is needed:

* `SpectralZetaWeighted` gives `Z_a(s) = ζ(s) · A(2^{-s})` for any
  admissible weight, and
* `NewtonBasisGeneratingFunction` evaluates `A_P(q)` in the Newton
  basis as `∑_{r ≤ d} c_r q^r/(1-q)^{r+1}`.

Substituting `q = 2^{-s}` and clearing the negative powers turns each
Newton term into `2^s/(2^s-1)^{r+1}`, which is the volume's display.
That last step is the only arithmetic in this module, and it is
isolated as `newton_term_eq`.

The `ζ` factor is inherited as its own `p`-series `∑' n, (n+1)^{-s}`,
not as `riemannZeta`; `SpectralZetaWeighted` explains why, and nothing
here is conditional on that identification.

The hypotheses are those of the two inputs, and both are genuine: `P`
must be nonnegative on `ℕ` — the volume's standing assumption on an
admissible exponent sequence — and `s > 1`.  The summability of
`A_P(2^{-s})`, which `SpectralZetaWeighted` must assume in general
because a weight may grow arbitrarily fast, is here *discharged* from
`summable_newtonPoly`: a polynomial weight is always admissible at a
dyadic base.  That is the one place where the composite is stronger
than a mechanical juxtaposition of its two inputs.

* `rpow_neg_natCast_mul_two` — the bridge `2^{-h·s} = (2^{-s})^h`;
* `newton_term_eq` — the arithmetic step `q^r/(1-q)^{r+1} =
  t/(t-1)^{r+1}` at `q = t⁻¹`;
* `summable_newtonPoly_rpow` — polynomial weights are admissible;
* `tsum_newtonPoly_spectral_zeta` — **the volume's `p1:eq:ZP`**.

The probabilistic cumulants `p1:eq:kappaP` of the same theorem remain
unformalized because they need the random-variable model behind `Φ_P`.
The analytic Euler--zeta expansion of the logarithmic product kernel is
formalized downstream in `FabiusFunction.GeneralizedSincZeta`, built on
`FabiusFunction.WeightedEulerTransform`; that transform-side identity does
not construct the random variable, its moments, or its cumulants.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The bridge between the `rpow` form used by the spectral zeta and
the natural-power form used by the generating function:
`2^{-h·s} = (2^{-s})^h`. -/
theorem rpow_neg_natCast_mul_two (h : ℕ) (s : ℝ) :
    (2 : ℝ) ^ (-(h : ℝ) * s) = ((2 : ℝ) ^ (-s)) ^ h := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (-s)) h,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- The arithmetic step.  At `q = t⁻¹` with `t > 1`, a Newton-basis
term clears its negative powers:
`q^r/(1-q)^{r+1} = t/(t-1)^{r+1}`. -/
theorem newton_term_eq {t : ℝ} (ht : 1 < t) (r : ℕ) :
    t⁻¹ ^ r / (1 - t⁻¹) ^ (r + 1) = t / (t - 1) ^ (r + 1) := by
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t - 1 ≠ 0 := by linarith
  have hsub : 1 - t⁻¹ = (t - 1) / t := by field_simp
  have hkey : t⁻¹ ^ r * t ^ (r + 1) = t := by
    rw [inv_pow, pow_succ]
    field_simp
  rw [hsub, div_pow, div_div_eq_mul_div, hkey]

/-- `1 < 2^s` for `s > 0`. -/
theorem one_lt_two_rpow {s : ℝ} (hs : 0 < s) :
    (1 : ℝ) < (2 : ℝ) ^ s :=
  (Real.one_lt_rpow_iff_of_pos (by norm_num)).mpr
    (Or.inl ⟨by norm_num, hs⟩)

/-- **Polynomial weights are admissible at a dyadic base.**  The
summability hypothesis that `SpectralZetaWeighted` must carry in
general is automatic for a Newton-basis polynomial, because
`|2^{-s}| < 1`. -/
theorem summable_newtonPoly_rpow (c : ℕ → ℝ) (d : ℕ) {s : ℝ}
    (hs : 0 < s) :
    Summable fun h : ℕ =>
      newtonPoly c d h * (2 : ℝ) ^ (-(h : ℝ) * s) := by
  have hq : |(2 : ℝ) ^ (-s)| < 1 := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-s) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hlt : (2 : ℝ) ^ (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    rw [abs_of_pos hpos]
    exact hlt
  have hsum := summable_newtonPoly c d hq
  refine hsum.congr fun h => ?_
  rw [rpow_neg_natCast_mul_two]

/-- **The volume's `p1:eq:ZP`.**  For a Newton-basis polynomial weight
that is nonnegative on `ℕ`, the spectral zeta has the closed form

`Z_P(s) = ζ(s) · ∑_{r ≤ d} c_r · 2^s/(2^s-1)^{r+1}`,

the `ζ` factor being carried as its own `p`-series.  The summability
hypothesis of the general theorem is discharged here rather than
assumed. -/
theorem tsum_newtonPoly_spectral_zeta (c : ℕ → ℝ) (d : ℕ) {s : ℝ}
    (hs : 1 < s) (hnn : ∀ h, 0 ≤ newtonPoly c d h) :
    (∑' n : ℕ, weightedScaleMultiplicity 2 (newtonPoly c d) (n + 1)
        * ((n : ℝ) + 1) ^ (-s))
      = (∑' n : ℕ, ((n : ℝ) + 1) ^ (-s))
        * ∑ r ∈ range (d + 1),
            c r * ((2 : ℝ) ^ s / ((2 : ℝ) ^ s - 1) ^ (r + 1)) := by
  have hs0 : (0 : ℝ) < s := lt_trans zero_lt_one hs
  have hA := summable_newtonPoly_rpow c d hs0
  have hzeta := tsum_weightedScaleMultiplicity_succ_rpow_two
    (newtonPoly c d) s hs hnn hA
  have hq : |(2 : ℝ) ^ (-s)| < 1 := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-s) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hlt : (2 : ℝ) ^ (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    rw [abs_of_pos hpos]
    exact hlt
  have hlayer : (∑' h : ℕ,
      newtonPoly c d h * (2 : ℝ) ^ (-(h : ℝ) * s))
      = ∑ r ∈ range (d + 1),
          c r * ((2 : ℝ) ^ s / ((2 : ℝ) ^ s - 1) ^ (r + 1)) := by
    have hcongr : (∑' h : ℕ,
        newtonPoly c d h * (2 : ℝ) ^ (-(h : ℝ) * s))
        = ∑' h : ℕ, newtonPoly c d h * ((2 : ℝ) ^ (-s)) ^ h :=
      tsum_congr fun h => by rw [rpow_neg_natCast_mul_two]
    rw [hcongr, tsum_newtonPoly c d hq, newtonGF]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hinv : (2 : ℝ) ^ (-s) = ((2 : ℝ) ^ s)⁻¹ :=
      Real.rpow_neg (by norm_num) s
    rw [hinv, newton_term_eq (one_lt_two_rpow hs0) r]
  rw [hzeta, hlayer]

end Fabius
