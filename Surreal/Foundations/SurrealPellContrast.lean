import Surreal.Algebra.SplitNormParametrization
import Surreal.Foundations.TwoTermTruncation

/-!
# Full-surreal Pell solutions and the failure of truncation

The full-surreal contrast following `odg:ex:pell2`. A nonzero parameter
gives a solution of x²-Dy²=c. At every positive monomial parameter, both
coordinates have a nonzero negative coefficient when c is nonzero. Their
canonical positive-growth truncations have norm zero instead of c.
-/

universe u
namespace Surreal.Foundations.SignSequence

open SmallNormalForm

noncomputable section

/-- The split-norm parametrization gives actual surreal solutions for every positive real D. -/
theorem surreal_pell_parametrization (D c : ℝ) (hD : 0 < D)
    (s : SignSequence.{u}) (hs : s ≠ 0) :
    SplitNorm.x s (ofReal c) ^ 2 - ofReal D *
      SplitNorm.y (ofReal (Real.sqrt D)) s (ofReal c) ^ 2 = ofReal c := by
  have hr : (ofReal (Real.sqrt D) : SignSequence.{u}) ≠ 0 := by
    simpa only [← map_zero ofReal] using ofReal_injective.ne (Real.sqrt_pos.mpr hD).ne'
  have he := SplitNorm.equation (ofReal (Real.sqrt D)) s (ofReal c) hr hs
  rw [← map_pow, Real.sq_sqrt hD.le] at he
  exact he

/-- The first monomial-parameter coordinate has its literal two-term expansion. -/
theorem pell_x_monomial_expansion (a : SignSequence.{u}) (c : ℝ) :
    SplitNorm.x (omegaPower a) (ofReal c) =
      ofReal (1 / 2 : ℝ) * omegaPower a + ofReal (c / 2) * omegaPower (-a) := by
  simp only [SplitNorm.x, ofReal_div, map_one, map_ofNat, omegaPower_neg]
  ring

/-- The second monomial-parameter coordinate has its literal two-term expansion. -/
theorem pell_y_monomial_expansion (a : SignSequence.{u}) (r c : ℝ) :
    SplitNorm.y (ofReal r) (omegaPower a) (ofReal c) =
      ofReal (1 / (2 * r)) * omegaPower a + ofReal (-c / (2 * r)) * omegaPower (-a) := by
  simp only [SplitNorm.y, ofReal_div, map_one, map_mul, map_ofNat, map_neg,
    omegaPower_neg]
  ring

/-- Both monomial-parameter coordinates have forbidden negative terms at every nonzero level. -/
theorem pell_monomial_not_nonnegativeSupport (a : SignSequence.{u}) (ha : 0 < a)
    (r c : ℝ) (hr : r ≠ 0) (hc : c ≠ 0) :
    SplitNorm.x (omegaPower a) (ofReal c) ∉ nonnegativeSupportSubring ∧
      SplitNorm.y (ofReal r) (omegaPower a) (ofReal c) ∉ nonnegativeSupportSubring := by
  rw [pell_x_monomial_expansion, pell_y_monomial_expansion]
  exact ⟨twoTerm_not_mem_nonnegativeSupport a ha _ _ (div_ne_zero hc (by norm_num)),
    twoTerm_not_mem_nonnegativeSupport a ha _ _
      (div_ne_zero (neg_ne_zero.mpr hc) (mul_ne_zero (by norm_num) hr))⟩

/-- Consequently neither coordinate can be the value of any actual omnific integer. -/
theorem pell_monomial_not_omnific (a : SignSequence.{u}) (ha : 0 < a)
    (r c : ℝ) (hr : r ≠ 0) (hc : c ≠ 0) :
    (¬ ∃ z : OmnificInteger.{u}, omnificToSurreal z = SplitNorm.x (omegaPower a) (ofReal c)) ∧
      (¬ ∃ z : OmnificInteger.{u}, omnificToSurreal z =
        SplitNorm.y (ofReal r) (omegaPower a) (ofReal c)) := by
  obtain ⟨hx, hy⟩ := pell_monomial_not_nonnegativeSupport a ha r c hr hc
  constructor
  · rintro ⟨z, hz⟩
    exact hx (hz ▸ z.val.property)
  · rintro ⟨z, hz⟩
    exact hy (hz ▸ z.val.property)

/-- The canonical truncations, not just a chosen approximation, discard the inverse terms. -/
theorem pell_monomial_positiveGrowthParts (a : SignSequence.{u}) (ha : 0 < a) (r c : ℝ) :
    omnificToSurreal (positiveGrowthPart (SplitNorm.x (omegaPower a) (ofReal c))) =
      omegaPower a / 2 ∧
    omnificToSurreal (positiveGrowthPart (SplitNorm.y (ofReal r) (omegaPower a) (ofReal c))) =
      omegaPower a / (2 * ofReal r) := by
  rw [pell_x_monomial_expansion, pell_y_monomial_expansion,
    twoTerm_positiveGrowthPart a ha, twoTerm_positiveGrowthPart a ha]
  simp only [ofReal_div, map_one, map_mul, map_ofNat]
  constructor <;> ring

/-- Taking positive-growth parts changes the prescribed nonzero Pell norm to zero. -/
theorem pell_monomial_truncation_norm (a : SignSequence.{u}) (ha : 0 < a)
    (D c : ℝ) (hD : 0 < D) :
    let x := positiveGrowthPart (SplitNorm.x (omegaPower a) (ofReal c))
    let y := positiveGrowthPart (SplitNorm.y (ofReal (Real.sqrt D)) (omegaPower a) (ofReal c))
    omnificToSurreal x ^ 2 - ofReal D * omnificToSurreal y ^ 2 = 0 := by
  dsimp only
  obtain ⟨hx, hy⟩ := pell_monomial_positiveGrowthParts a ha (Real.sqrt D) c
  rw [hx, hy]
  have hr : (ofReal (Real.sqrt D) : SignSequence.{u}) ≠ 0 := by
    simpa only [← map_zero ofReal] using ofReal_injective.ne (Real.sqrt_pos.mpr hD).ne'
  have he := SplitNorm.truncated_equation (ofReal (Real.sqrt D)) (omegaPower a) hr
  rw [← map_pow, Real.sq_sqrt hD.le] at he
  exact he

/-- At a nonzero level the canonical truncations fail the original Pell equation. -/
theorem pell_monomial_truncation_not_solution (a : SignSequence.{u}) (ha : 0 < a)
    (D c : ℝ) (hD : 0 < D) (hc : c ≠ 0) :
    let x := positiveGrowthPart (SplitNorm.x (omegaPower a) (ofReal c))
    let y := positiveGrowthPart (SplitNorm.y (ofReal (Real.sqrt D)) (omegaPower a) (ofReal c))
    omnificToSurreal x ^ 2 - ofReal D * omnificToSurreal y ^ 2 ≠ ofReal c := by
  dsimp only
  rw [pell_monomial_truncation_norm a ha D c hD]
  simpa only [map_zero] using (ofReal_injective.ne hc).symm

end
end Surreal.Foundations.SignSequence
