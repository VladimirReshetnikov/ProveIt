import Surreal.Foundations.SignSequenceBinomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Positive natural roots of actual surreals at every scale

Normalize by the leading monomial and its positive ordinary coefficient,
then apply the proved binomial root to the remaining principal unit.
This supplies the positive radii required by `trigonometry:cor:representatives`
without assuming algebraic closedness or restricting to finite inputs.
-/

universe u

namespace Surreal.Foundations.SignSequence

/-- Every positive actual surreal is a positive real monomial times a principal unit. -/
theorem exists_positive_monomial_factor (x : SignSequence.{u}) (hx : 0 < x) :
    ∃ (r : ℝ) (a ε : SignSequence.{u}), 0 < r ∧ IsInfinitesimal ε ∧
      x = ofReal r * omegaPower a * (1 + ε) := by
  let r := leadingCoeff x
  let a := leadingExponent x
  let y := x / omegaPower a
  have hr : 0 < r := (leadingCoeff_pos_iff x).mpr hx
  have hy : IsFinite y := finite_normalized x
  have hs : standardPart y = r := (leadingCoeff_eq_standardPart x).symm
  let ε := ofReal r⁻¹ * y - 1
  have hε : IsInfinitesimal ε := by
    apply (standardPart_eq_zero_iff (finite_sub (finite_mul (finite_ofReal _) hy) finite_one)).mp
    rw [standardPart_sub (finite_mul (finite_ofReal _) hy) finite_one,
      standardPart_mul (finite_ofReal _) hy, standardPart_ofReal, hs, standardPart_one,
      inv_mul_cancel₀ hr.ne', sub_self]
  refine ⟨r, a, ε, hr, hε, ?_⟩
  have hn : ofReal r ≠ (0 : SignSequence.{u}) := (map_ne_zero ofReal).mpr hr.ne'
  dsimp [ε, y]
  rw [map_inv₀]
  field_simp [omegaPower_ne_zero a]
  ring

/-- Every positive actual surreal has a unique positive natural root of nonzero degree. -/
theorem existsUnique_positive_nthRoot (x : SignSequence.{u}) (hx : 0 < x)
    (n : ℕ) (hn : 0 < n) : ∃! y : SignSequence.{u}, 0 < y ∧ y ^ n = x := by
  obtain ⟨r, a, ε, hr, hε, he⟩ := exists_positive_monomial_factor x hx
  let b : ℝ := r ^ ((n : ℝ)⁻¹)
  have hb : 0 < b := Real.rpow_pos_of_pos hr _
  have hbn : b ^ n = r := Real.rpow_inv_natCast_pow hr.le hn.ne'
  let y := ofReal b * omegaPower (a / n) * binomialPower ε hε (1 / (n : ℝ))
  have hy : 0 < y := mul_pos
    (mul_pos (by simpa only [map_zero] using ofReal_strictMono hb) (omegaPower_pos _))
    (binomialPower_pos _ _ _)
  have hn' : (n : SignSequence.{u}) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have heq : (n : SignSequence.{u}) * (a / n) = a := by field_simp
  have hyp : y ^ n = x := by
    dsimp only [y]
    rw [mul_pow, mul_pow, ← map_pow, hbn, ← omegaPower_nat_mul, heq,
      binomialPower_rat_root ε hε n hn.ne']
    exact he.symm
  refine ⟨y, ⟨hy, hyp⟩, ?_⟩
  intro z hz
  exact (pow_left_inj₀ hz.1.le hy.le hn.ne').mp (hz.2.trans hyp.symm)

/-- The unique positive natural root, available for every positive actual surreal. -/
noncomputable def positiveNthRoot (x : SignSequence.{u}) (hx : 0 < x) (n : ℕ) (hn : 0 < n) :
    SignSequence.{u} :=
  (existsUnique_positive_nthRoot x hx n hn).choose

/-- The chosen root is strictly positive. -/
theorem positiveNthRoot_pos (x : SignSequence.{u}) (hx : 0 < x) (n : ℕ) (hn : 0 < n) :
    0 < positiveNthRoot x hx n hn :=
  (existsUnique_positive_nthRoot x hx n hn).choose_spec.1.1

/-- The chosen root has exactly the prescribed natural power. -/
@[simp] theorem positiveNthRoot_pow (x : SignSequence.{u}) (hx : 0 < x) (n : ℕ) (hn : 0 < n) :
    positiveNthRoot x hx n hn ^ n = x :=
  (existsUnique_positive_nthRoot x hx n hn).choose_spec.1.2

end Surreal.Foundations.SignSequence
