import Surreal.Foundations.SignSequenceBinomial
import Surreal.Algebra.FormalBinomialRoots

/-!
# Injective monomial substitution in actual surreal normal forms

The actual-surreal clause of `osq:nm:lem:binomial`. At omega^(-g),
g > 0, arbitrary real formal power series have strongly summable
terms, retain every coefficient, and introduce no other exponents.
The native power-series evaluation homomorphism is therefore injective.
This is Hahn substitution, not convergence of partial sums in the fine topology.
-/

universe u
namespace Surreal.Foundations.SignSequence
open SmallNormalForm
noncomputable section

/-- A Conway monomial with negative growth exponent is infinitesimal. -/
theorem infinitesimal_omegaPower_neg (g : SignSequence.{u}) (hg : 0 < g) :
    IsInfinitesimal (omegaPower (-g)) := by
  rw [infinitesimal_iff_leadingExponent_neg (omegaPower_ne_zero _), leadingExponent_omegaPower]
  exact neg_lt_zero.mpr hg

/-- Actual monomial substitution uses the existing native formal-series evaluation homomorphism. -/
def monomialEvaluation (g : SignSequence.{u}) (hg : 0 < g) :
    PowerSeries ℝ →+* SignSequence.{u} :=
  powerSeriesEvaluation (omegaPower (-g)) (infinitesimal_omegaPower_neg g hg)

/-- The growth exponents in a positive monomial substitution are pairwise distinct. -/
theorem monomialEvaluation_exponents_injective (g : SignSequence.{u}) (hg : 0 < g) :
    Function.Injective (fun n : ℕ => (n : SignSequence.{u}) * (-g)) := by
  intro n k h
  exact Nat.cast_injective (mul_right_cancel₀ (neg_ne_zero.mpr hg.ne') h)

/-- Coefficients at the ordinary monomial multiples are exactly the formal coefficients. -/
theorem coeff_monomialEvaluation (g : SignSequence.{u}) (hg : 0 < g)
    (f : PowerSeries ℝ) (n : ℕ) :
    coeff (normalForm (monomialEvaluation g hg f)) ((n : SignSequence) * (-g)) = f.coeff n := by
  rw [monomialEvaluation, powerSeriesEvaluation_eq_strongSum, coeff_normalForm_strongSum,
    finsum_eq_single _ n]
  · rw [← omegaPower_nat_mul, normalForm_real_mul_omegaPower, coeff_single, if_pos rfl]
  · intro k hk
    rw [← omegaPower_nat_mul, normalForm_real_mul_omegaPower, coeff_single]
    exact if_neg (fun he => hk ((monomialEvaluation_exponents_injective g hg) he).symm)

/-- The substituted normal form has no exponents outside the displayed ordinary monomial powers. -/
theorem coeff_monomialEvaluation_eq_zero (g : SignSequence.{u}) (hg : 0 < g)
    (f : PowerSeries ℝ) (a : SignSequence.{u}) (ha : ∀ n : ℕ, a ≠ (n : SignSequence) * (-g)) :
    coeff (normalForm (monomialEvaluation g hg f)) a = 0 := by
  rw [monomialEvaluation, powerSeriesEvaluation_eq_strongSum, coeff_normalForm_strongSum]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  rw [← omegaPower_nat_mul, normalForm_real_mul_omegaPower, coeff_single, if_neg (ha n)]

/-- Distinct formal series give distinct actual surreal numbers under monomial substitution. -/
theorem monomialEvaluation_injective (g : SignSequence.{u}) (hg : 0 < g) :
    Function.Injective (monomialEvaluation g hg) := by
  intro f q h
  ext n
  simpa only [coeff_monomialEvaluation] using
    congrArg (fun x : SignSequence.{u} => coeff (normalForm x) ((n : SignSequence) * (-g))) h

@[simp] theorem monomialEvaluation_X (g : SignSequence.{u}) (hg : 0 < g) :
    monomialEvaluation g hg PowerSeries.X = omegaPower (-g) := powerSeriesEvaluation_X _ _

/-- The formal binomial root identity survives injective substitution into actual surreals. -/
theorem monomialEvaluation_binomial_root (g : SignSequence.{u}) (hg : 0 < g)
    (m : ℕ) (hm : m ≠ 0) :
    monomialEvaluation g hg (PowerSeries.binomialSeries ℝ (1 / (m : ℝ))) ^ m =
      1 + omegaPower (-g) := by
  rw [← map_pow, FormalBinomialRoots.binomialSeries_root m hm, map_add, map_one,
    monomialEvaluation_X]

/-- Every coefficient of the actual binomial root is the corresponding ordinary binomial coefficient. -/
theorem coeff_monomialEvaluation_binomial (g : SignSequence.{u}) (hg : 0 < g) (m n : ℕ) :
    coeff (normalForm (monomialEvaluation g hg (PowerSeries.binomialSeries ℝ (1 / (m : ℝ)))))
      ((n : SignSequence) * (-g)) = Ring.choose (1 / (m : ℝ)) n := by
  rw [coeff_monomialEvaluation, PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]

/-- The coefficients agree literally with the rational binomial series in the manuscript. -/
theorem coeff_monomialEvaluation_binomial_rat (g : SignSequence.{u}) (hg : 0 < g) (m n : ℕ) :
    coeff (normalForm (monomialEvaluation g hg (PowerSeries.binomialSeries ℝ (1 / (m : ℝ)))))
      ((n : SignSequence) * (-g)) = ((Ring.choose (1 / (m : ℚ)) n : ℚ) : ℝ) := by
  rw [coeff_monomialEvaluation_binomial]
  simpa using (Ring.map_choose (Rat.castHom ℝ) (1 / (m : ℚ)) n).symm

/-- Multiplication by a Conway monomial shifts every actual normal-form coefficient. -/
theorem coeff_normalForm_omegaPower_mul (a b x : SignSequence.{u}) :
    coeff (normalForm (omegaPower a * x)) (a + b) = coeff (normalForm x) b := by
  rw [normalForm_mul, normalForm_omegaPower]
  have hs : ofLex (single a 1).val =
      _root_.HahnSeries.single (OrderDual.toDual (toSurreal a)) (1 : ℝ) := by
    ext c
    change (Pi.single (toSurreal a) (1 : ℝ) : _root_.Surreal.{u} → ℝ) (OrderDual.ofDual c) = _
    simp only [Pi.single_apply, _root_.HahnSeries.coeff_single]
    by_cases hc : c = OrderDual.toDual (toSurreal a) <;> simp [hc]
    exact fun h => hc (congrArg OrderDual.toDual h)
  change (ofLex (single a 1).val *
    ofLex (normalForm x).val).coeff (OrderDual.toDual (toSurreal (a + b))) = _
  have he : OrderDual.toDual (toSurreal (a + b)) =
      OrderDual.toDual (toSurreal b) + OrderDual.toDual (toSurreal a) := by
    change toSurreal (a + b) = toSurreal b + toSurreal a
    rw [toSurreal_add, _root_.add_comm]
  rw [hs, he, _root_.HahnSeries.coeff_single_mul_add, _root_.one_mul]
  rfl

end
end Surreal.Foundations.SignSequence
