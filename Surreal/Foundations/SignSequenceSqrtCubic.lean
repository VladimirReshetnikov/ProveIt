import Surreal.Foundations.SignSequenceHypotenuseExpansion

/-!
# Cubic square-root expansion with a finite fourth-order remainder

One additional binomial coefficient supplies the seventh-order inradius tail
in `trigonometry:ex:flat` after rationalizing its exact square-root formula.
-/

universe u

namespace Surreal.Foundations.SignSequence

/-- The cubic square-root polynomial has an exact fourth-order tail of residue `-5/128`. -/
theorem sqrt_one_add_cubic_expansion (t : SignSequence.{u}) (ht : IsInfinitesimal t) :
    ∃ R : SignSequence.{u}, IsFinite R ∧ standardPart R = -5 / 128 ∧
      sqrt (1 + t) = 1 + t / 2 - t ^ 2 / 8 + t ^ 3 / 16 + t ^ 4 * R := by
  obtain ⟨R, hR, hr, he⟩ := exists_finite_powerSeries_remainder t ht
    (PowerSeries.binomialSeries ℝ (1 / 2 : ℝ)) 4
  rw [← binomialPower, binomialPower_half_eq_sqrt] at he
  have hs2 : Polynomial.smeval (2 : Polynomial ℤ) (1 / 2 : ℝ) = 2 := by
    simpa using Polynomial.smeval_natCast ℤ (1 / 2 : ℝ) 2
  have hs3 : Polynomial.smeval (3 : Polynomial ℤ) (1 / 2 : ℝ) = 3 := by
    simpa using Polynomial.smeval_natCast ℤ (1 / 2 : ℝ) 3
  norm_num [PowerSeries.binomialSeries_coeff, Ring.choose_eq_smul,
    descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_sub,
    Polynomial.smeval_X, Polynomial.smeval_one, Polynomial.smeval_natCast,
    Finset.sum_range_succ, map_div₀, map_ofNat, hs2, hs3] at hr he
  exact ⟨R, hR, by simpa only [neg_div] using hr, by linear_combination he⟩

end Surreal.Foundations.SignSequence
