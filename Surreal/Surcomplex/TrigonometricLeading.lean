import Surreal.Surcomplex.TrigonometricOrder
import Surreal.Surcomplex.PowerSeriesTruncation
import Surreal.Foundations.SignSequenceFiniteUnits

/-!
# Exact infinitesimal trigonometric expansions

The expansions, valuations and algebraic asymptotic equivalents of
`trigonometry:prop:leading` concern a single actual infinitesimal. The
remainders have finite normalized quotients; no sequence limit is involved.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

/-- At an infinitesimal angle, finite sine is evaluation of its series at zero. -/
theorem finiteSin_eq_powerSeries_of_isInfinitesimal (θ : SignSequence.FiniteElement.{u})
    (hθ : SignSequence.IsInfinitesimal θ.val) :
    finiteSin θ = SignSequence.powerSeriesEvaluation θ.val hθ (Analytic.taylorSeries Real.sin 0) := by
  rw [← sinFunction_eq_finiteSin, sinFunction,
    SignSequence.analyticLiftFunction_of_domain _ _ θ.property Real.analyticAt_sin]
  simp only [SignSequence.analyticLift, SignSequence.analyticTaylorEvaluation,
    (SignSequence.standardPart_eq_zero_iff θ.property).mpr hθ, map_zero, sub_zero]

/-- At an infinitesimal angle, finite cosine is evaluation of its series at zero. -/
theorem finiteCos_eq_powerSeries_of_isInfinitesimal (θ : SignSequence.FiniteElement.{u})
    (hθ : SignSequence.IsInfinitesimal θ.val) :
    finiteCos θ = SignSequence.powerSeriesEvaluation θ.val hθ (Analytic.taylorSeries Real.cos 0) := by
  rw [← cosFunction_eq_finiteCos, cosFunction,
    SignSequence.analyticLiftFunction_of_domain _ _ θ.property Real.analyticAt_cos]
  simp only [SignSequence.analyticLift, SignSequence.analyticTaylorEvaluation,
    (SignSequence.standardPart_eq_zero_iff θ.property).mpr hθ, map_zero, sub_zero]

/-- Sine through degree five has an exact finite seventh-order remainder. -/
theorem finiteSin_expansion (θ : SignSequence.FiniteElement.{u})
    (hθ : SignSequence.IsInfinitesimal θ.val) :
    ∃ R : SignSequence.{u}, SignSequence.IsFinite R ∧ SignSequence.standardPart R = -1 / 5040 ∧
      finiteSin θ = θ.val - θ.val ^ 3 / 6 + θ.val ^ 5 / 120 + θ.val ^ 7 * R := by
  obtain ⟨R, hR, hr, he⟩ := SignSequence.exists_finite_powerSeries_remainder θ.val hθ
    (Analytic.taylorSeries Real.sin 0) 7
  rw [← finiteSin_eq_powerSeries_of_isInfinitesimal θ hθ] at he
  norm_num [Finset.sum_range_succ, Analytic.coeff_taylorSeries_sin_zero,
    map_div₀, map_neg] at hr he
  refine ⟨R, hR, by simpa only [neg_div] using hr, ?_⟩
  linear_combination he

/-- One minus cosine through degree four has an exact finite sixth-order remainder. -/
theorem one_sub_finiteCos_expansion (θ : SignSequence.FiniteElement.{u})
    (hθ : SignSequence.IsInfinitesimal θ.val) :
    ∃ R : SignSequence.{u}, SignSequence.IsFinite R ∧ SignSequence.standardPart R = 1 / 720 ∧
      1 - finiteCos θ = θ.val ^ 2 / 2 - θ.val ^ 4 / 24 + θ.val ^ 6 * R := by
  obtain ⟨R, hR, hr, he⟩ := SignSequence.exists_finite_powerSeries_remainder θ.val hθ
    (Analytic.taylorSeries Real.cos 0) 6
  rw [← finiteCos_eq_powerSeries_of_isInfinitesimal θ hθ] at he
  norm_num [Finset.sum_range_succ, Analytic.coeff_taylorSeries_cos_zero,
    map_div₀, map_neg] at hr he
  refine ⟨-R, SignSequence.finite_neg hR, ?_, ?_⟩
  · rw [SignSequence.standardPart_neg, hr]
    norm_num
  · linear_combination -he

/-- Infinitesimal-angle cosine is a unit of the finite ring, with residue one. -/
theorem standardPart_finiteCos_of_isInfinitesimal (θ : SignSequence.FiniteElement.{u})
    (hθ : SignSequence.IsInfinitesimal θ.val) : SignSequence.standardPart (finiteCos θ) = 1 := by
  rw [standardPart_finiteCos, SignSequence.standardPartHom_apply,
    (SignSequence.standardPart_eq_zero_iff θ.property).mpr hθ,
    Real.cos_zero]

/-- Tangent through degree five has an exact finite seventh-order remainder. -/
theorem finiteTan_expansion (θ : SignSequence.FiniteElement.{u})
    (hθ : SignSequence.IsInfinitesimal θ.val) :
    ∃ R : SignSequence.{u}, SignSequence.IsFinite R ∧
      finiteTan θ = θ.val + θ.val ^ 3 / 3 + 2 * θ.val ^ 5 / 15 + θ.val ^ 7 * R := by
  obtain ⟨S, hS, _, hs⟩ := finiteSin_expansion θ hθ
  obtain ⟨C, hC, _, hc⟩ := one_sub_finiteCos_expansion θ hθ
  have hstd := standardPart_finiteCos_of_isInfinitesimal θ hθ
  have hn : SignSequence.standardPart (finiteCos θ) ≠ 0 := by rw [hstd]; norm_num
  have hci := SignSequence.finite_inv_of_standardPart_ne_zero (isFinite_finiteCos θ) hn
  have hne : finiteCos θ ≠ 0 := by intro h; exact hn (by simp [h])
  let Q : SignSequence.{u} := S + SignSequence.ofReal (19 / 360) -
    θ.val ^ 2 * SignSequence.ofReal (1 / 180) +
    C * (1 + θ.val ^ 2 * SignSequence.ofReal (1 / 3) + θ.val ^ 4 * SignSequence.ofReal (2 / 15))
  have hQ : SignSequence.IsFinite Q := by
    apply SignSequence.finite_add
    · exact SignSequence.finite_sub (SignSequence.finite_add hS (SignSequence.finite_ofReal _))
        (SignSequence.finite_mul (SignSequence.finite_pow θ.property _) (SignSequence.finite_ofReal _))
    · exact SignSequence.finite_mul hC (SignSequence.finite_add
        (SignSequence.finite_add SignSequence.finite_one
          (SignSequence.finite_mul (SignSequence.finite_pow θ.property _) (SignSequence.finite_ofReal _)))
        (SignSequence.finite_mul (SignSequence.finite_pow θ.property _) (SignSequence.finite_ofReal _)))
  refine ⟨Q * (finiteCos θ)⁻¹, SignSequence.finite_mul hQ hci, ?_⟩
  apply (mul_right_cancel₀ hne)
  simp only [finiteTan, add_mul, mul_assoc, inv_mul_cancel₀ hne, mul_one,
    div_mul_cancel₀ _ hne]
  dsimp [Q]
  norm_num only [map_div₀, map_ofNat, map_one]
  linear_combination hs + (θ.val + θ.val ^ 3 / 3 + 2 * θ.val ^ 5 / 15) * hc

/-- The normalized sine factor is finite with standard part one. -/
theorem finiteSin_leading_factor (θ : SignSequence.FiniteElement.{u})
    (hθ : SignSequence.IsInfinitesimal θ.val) :
    ∃ R : SignSequence.{u}, SignSequence.IsFinite R ∧ SignSequence.standardPart R = 1 ∧
      finiteSin θ = θ.val * R := by
  obtain ⟨R, hR, hr, he⟩ := SignSequence.exists_finite_powerSeries_remainder θ.val hθ
    (Analytic.taylorSeries Real.sin 0) 1
  rw [← finiteSin_eq_powerSeries_of_isInfinitesimal θ hθ] at he
  norm_num [Finset.sum_range_succ, Analytic.coeff_taylorSeries_sin_zero] at hr he
  exact ⟨R, hR, hr, he⟩

/-- One minus cosine has a finite quadratic factor with standard part one half. -/
theorem one_sub_finiteCos_leading_factor (θ : SignSequence.FiniteElement.{u})
    (hθ : SignSequence.IsInfinitesimal θ.val) :
    ∃ R : SignSequence.{u}, SignSequence.IsFinite R ∧ SignSequence.standardPart R = 1 / 2 ∧
      1 - finiteCos θ = θ.val ^ 2 * R := by
  obtain ⟨R, hR, hr, he⟩ := SignSequence.exists_finite_powerSeries_remainder θ.val hθ
    (Analytic.taylorSeries Real.cos 0) 2
  rw [← finiteCos_eq_powerSeries_of_isInfinitesimal θ hθ] at he
  norm_num [Finset.sum_range_succ, Analytic.coeff_taylorSeries_cos_zero] at hr he
  refine ⟨-R, SignSequence.finite_neg hR, ?_, ?_⟩
  · rw [SignSequence.standardPart_neg, hr]
    norm_num
  · linear_combination -he

/-- Tangent also has a finite linear factor with standard part one. -/
theorem finiteTan_leading_factor (θ : SignSequence.FiniteElement.{u})
    (hθ : SignSequence.IsInfinitesimal θ.val) :
    ∃ R : SignSequence.{u}, SignSequence.IsFinite R ∧ SignSequence.standardPart R = 1 ∧
      finiteTan θ = θ.val * R := by
  obtain ⟨S, hS, hs, he⟩ := finiteSin_leading_factor θ hθ
  have hc := standardPart_finiteCos_of_isInfinitesimal θ hθ
  have hn : SignSequence.standardPart (finiteCos θ) ≠ 0 := by rw [hc]; norm_num
  have hci := SignSequence.finite_inv_of_standardPart_ne_zero (isFinite_finiteCos θ) hn
  refine ⟨S * (finiteCos θ)⁻¹, SignSequence.finite_mul hS hci, ?_, ?_⟩
  · rw [SignSequence.standardPart_mul hS hci,
      SignSequence.standardPart_inv_of_ne_zero (isFinite_finiteCos θ) hn, hs, hc]
    norm_num
  · rw [finiteTan, he, div_eq_mul_inv, mul_assoc]

/-- Exact sine valuation at any infinitesimal angle, including zero. -/
theorem valuation_finiteSin_of_isInfinitesimal (θ : SignSequence.FiniteElement.{u})
    (hθ : SignSequence.IsInfinitesimal θ.val) :
    SignSequence.valuation (finiteSin θ) = SignSequence.valuation θ.val := by
  obtain ⟨R, hR, hr, he⟩ := finiteSin_leading_factor θ hθ
  have hv := (SignSequence.valuation_eq_zero_iff_standardPart_ne_zero hR).mpr
    (by rw [hr]; norm_num)
  rw [he, SignSequence.valuation_mul, hv, add_zero]

/-- Exact tangent valuation at any infinitesimal angle, including zero. -/
theorem valuation_finiteTan_of_isInfinitesimal (θ : SignSequence.FiniteElement.{u})
    (hθ : SignSequence.IsInfinitesimal θ.val) :
    SignSequence.valuation (finiteTan θ) = SignSequence.valuation θ.val := by
  obtain ⟨R, hR, hr, he⟩ := finiteTan_leading_factor θ hθ
  have hv := (SignSequence.valuation_eq_zero_iff_standardPart_ne_zero hR).mpr
    (by rw [hr]; norm_num)
  rw [he, SignSequence.valuation_mul, hv, add_zero]

/-- The cosine defect has exactly twice the input valuation. -/
theorem valuation_one_sub_finiteCos_of_isInfinitesimal (θ : SignSequence.FiniteElement.{u})
    (hθ : SignSequence.IsInfinitesimal θ.val) :
    SignSequence.valuation (1 - finiteCos θ) = 2 • SignSequence.valuation θ.val := by
  obtain ⟨R, hR, hr, he⟩ := one_sub_finiteCos_leading_factor θ hθ
  have hv := (SignSequence.valuation_eq_zero_iff_standardPart_ne_zero hR).mpr
    (by rw [hr]; norm_num)
  rw [he, SignSequence.valuation_mul, hv, add_zero, SignSequence.valuation.map_pow]

/-- Algebraic sine equivalence: the normalized relative error is infinitesimal. -/
theorem infinitesimal_finiteSin_div_sub_one (θ : SignSequence.FiniteElement.{u})
    (hθ : SignSequence.IsInfinitesimal θ.val) (hne : θ.val ≠ 0) :
    SignSequence.IsInfinitesimal (finiteSin θ / θ.val - 1) := by
  obtain ⟨R, hR, hr, he⟩ := finiteSin_leading_factor θ hθ
  rw [he, mul_div_cancel_left₀ _ hne]
  simpa only [hr, map_one] using SignSequence.infinitesimal_sub_standardPart hR

/-- Algebraic tangent equivalence: the normalized relative error is infinitesimal. -/
theorem infinitesimal_finiteTan_div_sub_one (θ : SignSequence.FiniteElement.{u})
    (hθ : SignSequence.IsInfinitesimal θ.val) (hne : θ.val ≠ 0) :
    SignSequence.IsInfinitesimal (finiteTan θ / θ.val - 1) := by
  obtain ⟨R, hR, hr, he⟩ := finiteTan_leading_factor θ hθ
  rw [he, mul_div_cancel_left₀ _ hne]
  simpa only [hr, map_one] using SignSequence.infinitesimal_sub_standardPart hR

/-- The cosine defect is algebraically equivalent to half the square of the input. -/
theorem infinitesimal_one_sub_finiteCos_div_sub_one (θ : SignSequence.FiniteElement.{u})
    (hθ : SignSequence.IsInfinitesimal θ.val) (hne : θ.val ≠ 0) :
    SignSequence.IsInfinitesimal ((1 - finiteCos θ) / (θ.val ^ 2 / 2) - 1) := by
  obtain ⟨R, hR, hr, he⟩ := one_sub_finiteCos_leading_factor θ hθ
  have h2 : SignSequence.IsFinite (2 : SignSequence.{u}) := by
    simpa only [map_ofNat] using SignSequence.finite_ofReal (2 : ℝ)
  have hf := SignSequence.finite_mul h2 hR
  have hs : SignSequence.standardPart (2 * R) = 1 := by
    rw [SignSequence.standardPart_mul h2 hR, hr]
    have hh : SignSequence.standardPart (2 : SignSequence.{u}) = 2 := by
      simpa only [map_ofNat] using SignSequence.standardPart_ofReal (2 : ℝ)
    rw [hh]
    norm_num
  have hq : (1 - finiteCos θ) / (θ.val ^ 2 / 2) = 2 * R := by
    rw [he]
    field_simp [hne]
  rw [hq]
  simpa only [hs, map_one] using SignSequence.infinitesimal_sub_standardPart hf

/-- The three displayed remainders have finite quotients, the source's exact `O(h^n)` meaning. -/
theorem finite_trigonometric_remainder_quotients (θ : SignSequence.FiniteElement.{u})
    (hθ : SignSequence.IsInfinitesimal θ.val) (hne : θ.val ≠ 0) :
    SignSequence.IsFinite ((finiteSin θ - (θ.val - θ.val ^ 3 / 6 + θ.val ^ 5 / 120)) / θ.val ^ 7) ∧
    SignSequence.IsFinite (((1 - finiteCos θ) - (θ.val ^ 2 / 2 - θ.val ^ 4 / 24)) / θ.val ^ 6) ∧
    SignSequence.IsFinite ((finiteTan θ - (θ.val + θ.val ^ 3 / 3 + 2 * θ.val ^ 5 / 15)) / θ.val ^ 7) := by
  obtain ⟨S, hS, _, hs⟩ := finiteSin_expansion θ hθ
  obtain ⟨C, hC, _, hc⟩ := one_sub_finiteCos_expansion θ hθ
  obtain ⟨T, hT, ht⟩ := finiteTan_expansion θ hθ
  rw [hs, hc, ht]
  simpa only [add_sub_cancel_left, mul_div_cancel_left₀ _ (pow_ne_zero _ hne)] using ⟨hS, hC, hT⟩

end Surreal.Surcomplex
