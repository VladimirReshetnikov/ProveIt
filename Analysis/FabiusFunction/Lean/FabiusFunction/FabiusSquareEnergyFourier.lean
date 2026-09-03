import FabiusFunction.FabiusLegendreEnergy
import FabiusFunction.PoissonSummation
import FabiusFunction.SincProductPositive
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Fourier and sinc-product formulas for the Fabius square energy

The Legendre expansion identifies the square energy

`A₂ = ∫ t in 0..1, F(t) ^ 2`

with an exact coefficient series.  This module supplies the complementary
Fourier face.  Plancherel for a Schwartz realization of Rvachev's compactly
supported function first identifies the full real-axis Fourier energy with
`2 * A₂`.  Evenness then gives the positive-half-line formula, and the real
dyadic sinc product plus the substitution `t = 2 * π * ξ` yields the two
improper-integral displays used in the reconstruction report.
-/

set_option autoImplicit false

open scoped BigOperators FourierTransform SchwartzMap
open MeasureTheory Set

namespace Fabius

noncomputable section

/-- Plancherel identifies the full real-axis squared Fourier mass of
Rvachev's function with twice the Fabius square energy. -/
theorem integral_norm_sq_rvachevFourier_eq_two_mul_fabiusSquareEnergy
    (F : BoundedFabius) (hF : IsFabius F) :
    (∫ ξ : ℝ, ‖rvachevFourier F (ξ : ℂ)‖ ^ 2) =
      2 * fabiusSquareEnergy F := by
  let φ : SchwartzMap ℝ ℂ :=
    scaledRvachevSchwartz F hF 1 (by norm_num)
  have hfourier (ξ : ℝ) :
      𝓕 φ ξ = rvachevFourier F (ξ : ℂ) := by
    dsimp only [φ]
    simpa using fourier_scaledRvachevSchwartz F hF
      (by norm_num : (0 : ℝ) < 1) ξ
  have hsupp :
      Function.support (fun x : ℝ => (rvachevUp F x) ^ 2) ⊆
        Function.support (rvachevUp F) := by
    intro x hx
    change rvachevUp F x ≠ 0
    intro hzero
    exact hx (by simp [hzero])
  have htruncate :
      (∫ x : ℝ, (rvachevUp F x) ^ 2) =
        ∫ x in (-1 : ℝ)..1, (rvachevUp F x) ^ 2 :=
    (intervalIntegral.integral_eq_integral_of_support_subset
      (hsupp.trans ((support_rvachev_subset_Ioo F hF).trans
        Ioo_subset_Ioc_self))).symm
  calc
    (∫ ξ : ℝ, ‖rvachevFourier F (ξ : ℂ)‖ ^ 2) =
        ∫ ξ : ℝ, ‖𝓕 φ ξ‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [hfourier]
    _ = ∫ x : ℝ, ‖φ x‖ ^ 2 :=
      SchwartzMap.integral_norm_sq_fourier φ
    _ = ∫ x : ℝ, (rvachevUp F x) ^ 2 := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [φ]
      rw [scaledRvachevSchwartz_apply]
      norm_num [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ = ∫ x in (-1 : ℝ)..1, (rvachevUp F x) ^ 2 := htruncate
    _ = 2 * fabiusSquareEnergy F :=
      integral_sq_rvachevUp_eq_two_mul_fabiusSquareEnergy F hF

/-- The Fabius square energy is the positive-half-line squared Fourier mass
of Rvachev's function. -/
theorem fabiusSquareEnergy_eq_integral_Ioi_norm_sq_rvachevFourier
    (F : BoundedFabius) (hF : IsFabius F) :
    fabiusSquareEnergy F =
      ∫ ξ in Ioi (0 : ℝ), ‖rvachevFourier F (ξ : ℂ)‖ ^ 2 := by
  let g : ℝ → ℝ := fun ξ => ‖rvachevFourier F (ξ : ℂ)‖ ^ 2
  have habs (ξ : ℝ) : g |ξ| = g ξ := by
    by_cases hξ : 0 ≤ ξ
    · rw [abs_of_nonneg hξ]
    · rw [abs_of_neg (lt_of_not_ge hξ)]
      dsimp only [g]
      rw [show (((-ξ : ℝ) : ℂ)) = -(ξ : ℂ) by norm_num]
      rw [rvachevFourier_neg F hF]
  have hsplit :
      (∫ ξ : ℝ, g ξ) = 2 * ∫ ξ in Ioi (0 : ℝ), g ξ := by
    simpa only [habs] using integral_comp_abs (f := g)
  rw [integral_norm_sq_rvachevFourier_eq_two_mul_fabiusSquareEnergy F hF]
    at hsplit
  linarith

/-- The Fabius square energy is the positive-half-line integral of the
squared real dyadic sinc product. -/
theorem fabiusSquareEnergy_eq_integral_Ioi_tprod_sinc_sq
    (F : BoundedFabius) (hF : IsFabius F) :
    fabiusSquareEnergy F =
      ∫ ξ in Ioi (0 : ℝ),
        ∏' j : ℕ, (Real.sinc (Real.pi * ξ / 2 ^ j)) ^ 2 := by
  rw [fabiusSquareEnergy_eq_integral_Ioi_norm_sq_rvachevFourier F hF]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro ξ _hξ
  change ‖rvachevFourier F (ξ : ℂ)‖ ^ 2 =
    ∏' j : ℕ, (Real.sinc (Real.pi * ξ / 2 ^ j)) ^ 2
  rw [rvachevFourier_eq_product F hF,
    rvachevFourierProduct_ofReal_eq_tprod_sinc]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [(multipliable_sinc_two_pow (Real.pi * ξ)).tprod_pow 2]

/-- After the substitution `t = 2 * π * ξ`, the Fabius square energy is
`1 / (2 * π)` times the positive-half-line integral of the squared sinc
product indexed from one. -/
theorem fabiusSquareEnergy_eq_scaled_integral_Ioi_tprod_sinc_sq
    (F : BoundedFabius) (hF : IsFabius F) :
    fabiusSquareEnergy F =
      (1 / (2 * Real.pi)) *
        ∫ t in Ioi (0 : ℝ),
          ∏' r : ℕ, (Real.sinc (t / 2 ^ (r + 1))) ^ 2 := by
  let G : ℝ → ℝ := fun t =>
    ∏' r : ℕ, (Real.sinc (t / 2 ^ (r + 1))) ^ 2
  have hfactor (ξ : ℝ) :
      G ((2 * Real.pi) * ξ) =
        ∏' r : ℕ, (Real.sinc (Real.pi * ξ / 2 ^ r)) ^ 2 := by
    dsimp only [G]
    apply tprod_congr
    intro r
    congr 2
    rw [pow_succ]
    field_simp
  have hscale := integral_comp_mul_left_Ioi G (0 : ℝ)
    (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)
  calc
    fabiusSquareEnergy F =
        ∫ ξ in Ioi (0 : ℝ),
          ∏' r : ℕ, (Real.sinc (Real.pi * ξ / 2 ^ r)) ^ 2 :=
      fabiusSquareEnergy_eq_integral_Ioi_tprod_sinc_sq F hF
    _ = (1 / (2 * Real.pi)) * ∫ t in Ioi (0 : ℝ), G t := by
      simpa only [hfactor, mul_zero, one_div, smul_eq_mul] using hscale
    _ = (1 / (2 * Real.pi)) *
          ∫ t in Ioi (0 : ℝ),
            ∏' r : ℕ, (Real.sinc (t / 2 ^ (r + 1))) ^ 2 := rfl

end

end Fabius
