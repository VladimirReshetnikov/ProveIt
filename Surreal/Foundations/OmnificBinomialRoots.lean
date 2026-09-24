import Surreal.Foundations.MonomialPowerSeries
import Surreal.Foundations.OmnificIntegralClosure

/-!
# Explicit non-omnific binomial roots in the actual normalization

The real root construction and its negative coefficient in
`osq:nm:thm:invisible`, `osq:nm:eq:rootexpansion` and
`osq:nm:rem:rootinN`. The binomial series constructs a positive integral
root of T^m - omega^g - 1. Its coefficient at g/m-g is 1/m, which
excludes membership in the omnific ring when m ≥ 2.
The separate universal small-target assertion is not used here.
-/

universe u
namespace Surreal.Foundations.SignSequence
open SmallNormalForm
noncomputable section

/-- The manuscript's positive root, constructed by monomial substitution in the binomial series. -/
def omnificBinomialRoot (g : SignSequence.{u}) (hg : 0 < g) (m : ℕ) : SignSequence.{u} :=
  omegaPower (g / (m : SignSequence)) *
    monomialEvaluation g hg (PowerSeries.binomialSeries ℝ (1 / (m : ℝ)))

/-- The constructed binomial root is positive. -/
theorem omnificBinomialRoot_pos (g : SignSequence.{u}) (hg : 0 < g) (m : ℕ) :
    0 < omnificBinomialRoot g hg m :=
  mul_pos (omegaPower_pos _) (binomialPower_pos _ (infinitesimal_omegaPower_neg g hg) _)

/-- It satisfies exactly the ordinary integer-power equation in the manuscript. -/
theorem omnificBinomialRoot_pow (g : SignSequence.{u}) (hg : 0 < g) (m : ℕ) (hm : m ≠ 0) :
    omnificBinomialRoot g hg m ^ m = omegaPower g + 1 := by
  have hm' : (m : SignSequence.{u}) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have he : (m : SignSequence) * (g / (m : SignSequence)) = g := by field_simp
  rw [omnificBinomialRoot, mul_pow, ← omegaPower_nat_mul,
    monomialEvaluation_binomial_root g hg m hm, he, mul_add, mul_one,
    ← omegaPower_add, _root_.add_neg_cancel, omegaPower_zero]

/-- Every coefficient in the displayed shifted binomial expansion is exact. -/
theorem omnificBinomialRoot_coeff (g : SignSequence.{u}) (hg : 0 < g) (m n : ℕ) :
    coeff (normalForm (omnificBinomialRoot g hg m))
      (g / (m : SignSequence) + (n : SignSequence) * (-g)) =
        ((Ring.choose (1 / (m : ℚ)) n : ℚ) : ℝ) := by
  rw [omnificBinomialRoot, coeff_normalForm_omegaPower_mul,
    coeff_monomialEvaluation_binomial_rat]

/-- The first term has coefficient one. -/
theorem omnificBinomialRoot_first_term (g : SignSequence.{u}) (hg : 0 < g) (m : ℕ) :
    coeff (normalForm (omnificBinomialRoot g hg m)) (g / (m : SignSequence)) = 1 := by
  simpa using omnificBinomialRoot_coeff g hg m 0

/-- The second term has the nonzero coefficient 1/m. -/
theorem omnificBinomialRoot_second_term (g : SignSequence.{u}) (hg : 0 < g) (m : ℕ) :
    coeff (normalForm (omnificBinomialRoot g hg m)) (g / (m : SignSequence) - g) = 1 / (m : ℝ) := by
  simpa only [Nat.cast_one, _root_.one_mul, ← sub_eq_add_neg, Ring.choose_one_right,
    Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using omnificBinomialRoot_coeff g hg m 1

/-- For m ≥ 2 the second term lies strictly below growth exponent zero. -/
theorem omnificBinomialRoot_second_exponent_neg (g : SignSequence.{u}) (hg : 0 < g)
    (m : ℕ) (hm : 2 ≤ m) : g / (m : SignSequence) - g < 0 := by
  apply sub_neg.mpr
  apply div_lt_self hg
  exact_mod_cast (show 1 < m by omega)

/-- The negative second term excludes the constructed root from the actual omnific ring. -/
theorem omnificBinomialRoot_not_mem (g : SignSequence.{u}) (hg : 0 < g) (m : ℕ) (hm : 2 ≤ m) :
    ¬ ∃ a : OmnificInteger.{u}, omnificToSurreal a = omnificBinomialRoot g hg m := by
  intro h
  have hz := ((exists_omnific_iff _).mp h).1 _ (omnificBinomialRoot_second_exponent_neg g hg m hm)
  rw [omnificBinomialRoot_second_term] at hz
  exact (one_div_ne_zero (Nat.cast_ne_zero.mpr (by omega : m ≠ 0))) hz

/-- The constructed non-omnific root is integral over the omnific ring. -/
theorem omnificBinomialRoot_isIntegral (g : SignSequence.{u}) (hg : 0 < g)
    (m : ℕ) (hm : m ≠ 0) : IsIntegral OmnificInteger (omnificBinomialRoot g hg m) := by
  apply IsIntegral.of_pow (Nat.pos_of_ne_zero hm)
  rw [omnificBinomialRoot_pow g hg m hm]
  have h : IsIntegral OmnificInteger (omnificToSurreal (omnificMonomial g hg)) :=
    isIntegral_algebraMap
  exact h.add isIntegral_one

/-- Explicit positive integral roots outside Oz, at every positive surreal scale and every m ≥ 2. -/
theorem omnificBinomialRoot_normalization_witness (g : SignSequence.{u}) (hg : 0 < g)
    (m : ℕ) (hm : 2 ≤ m) :
    0 < omnificBinomialRoot g hg m ∧
      omnificBinomialRoot g hg m ^ m = omegaPower g + 1 ∧
      IsIntegral OmnificInteger (omnificBinomialRoot g hg m) ∧
      ¬ ∃ a : OmnificInteger.{u}, omnificToSurreal a = omnificBinomialRoot g hg m :=
  ⟨omnificBinomialRoot_pos g hg m, omnificBinomialRoot_pow g hg m (by omega),
    omnificBinomialRoot_isIntegral g hg m (by omega), omnificBinomialRoot_not_mem g hg m hm⟩

/-- No actual real omnific integer solves the manuscript's power equation. -/
theorem omnific_no_root_omegaPower_add_one (g : SignSequence.{u}) (hg : 0 < g)
    (m : ℕ) (hm : 2 ≤ m) :
    ¬ ∃ a : OmnificInteger.{u}, omnificToSurreal a ^ m = omegaPower g + 1 := by
  rintro ⟨a, ha⟩
  have hp : 0 < omegaPower g + 1 := add_pos (omegaPower_pos g) zero_lt_one
  have he : |omnificToSurreal a| ^ m = omnificBinomialRoot g hg m ^ m := by
    rw [← abs_pow, ha, abs_of_pos hp, omnificBinomialRoot_pow g hg m (by omega)]
  have habs := (pow_left_inj₀ (abs_nonneg (omnificToSurreal a))
    (omnificBinomialRoot_pos g hg m).le (by omega : m ≠ 0)).mp he
  apply omnificBinomialRoot_not_mem g hg m hm
  rcases abs_choice (omnificToSurreal a) with h | h
  · exact ⟨a, h.symm.trans habs⟩
  · exact ⟨-a, (map_neg omnificToSurreal a).trans (h.symm.trans habs)⟩

/-- At exponent two the explicit binomial construction is the native nonnegative square root. -/
theorem omnificBinomialRoot_two_eq_sqrt (g : SignSequence.{u}) (hg : 0 < g) :
    omnificBinomialRoot g hg 2 = sqrt (omegaPower g + 1) :=
  (sqrt_eq_of_nonneg_sq (omnificBinomialRoot_pos g hg 2).le
    (omnificBinomialRoot_pow g hg 2 (by decide))).symm

/-- The square-root witness specified in `osq:nm:cor:notintclosed` is integral and outside Oz. -/
theorem omnific_sqrt_omega_add_one_witness :
    IsIntegral OmnificInteger.{u} (sqrt (omegaPower 1 + 1) : SignSequence.{u}) ∧
      ¬ ∃ a : OmnificInteger.{u}, omnificToSurreal a = sqrt (omegaPower 1 + 1) := by
  rw [← omnificBinomialRoot_two_eq_sqrt 1 zero_lt_one]
  exact ⟨omnificBinomialRoot_isIntegral 1 zero_lt_one 2 (by decide),
    omnificBinomialRoot_not_mem 1 zero_lt_one 2 le_rfl⟩

end
end Surreal.Foundations.SignSequence
