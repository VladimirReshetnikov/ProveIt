import Surreal.Foundations.OmnificDegree
import Mathlib.Algebra.Group.Int.Units

/-!
# Units and finite elements of the actual omnific ring

The real and omnific clauses of `odg:prop:units`: units of the real support
ring are the nonzero real constants, finite omnific integers are precisely
ordinary integers, omnific units are `1` and `-1`, and the inherited order
has least positive element `1`.
-/

universe u
namespace Surreal.Foundations.SignSequence

noncomputable section

/-- A unit of the real support ring is finite: both factors have nonnegative leading degree. -/
theorem nonnegativeSupport_finite_of_isUnit (x : nonnegativeSupportSubring.{u})
    (hx : IsUnit x) : IsFinite x.val := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have he : x.val * y.val = 1 := congrArg Subtype.val hy
  have hxn : x.val ≠ 0 := left_ne_zero_of_mul_eq_one he
  have hyn : y.val ≠ 0 := right_ne_zero_of_mul_eq_one he
  have hs : leadingExponent x.val + leadingExponent y.val = 0 := by
    rw [← leadingExponent_mul hxn hyn, he, leadingExponent_one]
  apply (finite_iff_leadingExponent_nonpos hxn).mpr
  linarith [nonnegativeSupport_leadingExponent_nonneg y hyn]

/-- The units of the real support ring are exactly the nonzero ordinary real constants. -/
theorem nonnegativeSupport_isUnit_iff (x : nonnegativeSupportSubring.{u}) :
    IsUnit x ↔ ∃ r : ℝ, r ≠ 0 ∧ x = realConstants r := by
  constructor
  · intro hx
    have he := nonnegativeSupport_eq_realConstant_of_finite x (nonnegativeSupport_finite_of_isUnit x hx)
    refine ⟨constantCoeff x, ?_, he⟩
    exact (hx.map constantCoeff).ne_zero
  · rintro ⟨r, hr, rfl⟩
    exact (isUnit_iff_ne_zero.mpr hr).map realConstants

/-- Every finite omnific integer equals its integer constant term. -/
theorem omnific_eq_intConstant_of_finite (x : OmnificInteger.{u})
    (hx : IsFinite (omnificToSurreal x)) : x = omnificIntCast (omnificConstantCoeff x) := by
  apply omnificToSurreal_injective
  rw [omnificToSurreal_intCast]
  have he := congrArg Subtype.val
    (nonnegativeSupport_eq_realConstant_of_finite x.val hx)
  change omnificToSurreal x = ofReal (constantCoeff x.val) at he
  have hc : (omnificConstantCoeff x : ℝ) = constantCoeff x.val :=
    CoefficientPullback.embedding_retraction constantCoeff (Int.castRingHom ℝ) Int.cast_injective x
  rw [← hc, map_intCast] at he
  exact he

/-- The finite omnific integers are exactly the ordinary integers. -/
theorem omnific_isFinite_iff (x : OmnificInteger.{u}) :
    IsFinite (omnificToSurreal x) ↔ ∃ n : ℤ, x = omnificIntCast n := by
  constructor
  · intro hx
    exact ⟨omnificConstantCoeff x, omnific_eq_intConstant_of_finite x hx⟩
  · rintro ⟨n, rfl⟩
    rw [omnificToSurreal_intCast, ← ofReal_intCast]
    exact finite_ofReal n

/-- A real bound on an omnific integer is equivalent to being an ordinary integer. -/
theorem omnific_bounded_iff (x : OmnificInteger.{u}) :
    (∃ r : ℝ, |omnificToSurreal x| ≤ ofReal r) ↔ ∃ n : ℤ, x = omnificIntCast n := by
  rw [← omnific_isFinite_iff]
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨n, hn⟩ := (isFinite_iff_exists_nat_abs_le (ofReal r : SignSequence.{u})).mp (finite_ofReal r)
    exact (isFinite_iff_exists_nat_abs_le _).mpr ⟨n, hr.trans ((le_abs_self _).trans hn)⟩
  · intro hx
    obtain ⟨n, hn⟩ := (isFinite_iff_exists_nat_abs_le _).mp hx
    exact ⟨n, by simpa only [map_natCast] using hn⟩

/-- The only omnific units are `1` and `-1`. -/
theorem omnific_isUnit_iff (x : OmnificInteger.{u}) : IsUnit x ↔ x = 1 ∨ x = -1 := by
  constructor
  · intro hx
    have hf := nonnegativeSupport_finite_of_isUnit x.val (hx.map omnificSubring.subtype)
    have he := omnific_eq_intConstant_of_finite x hf
    have hn := Int.isUnit_iff.mp (hx.map omnificConstantCoeff)
    rcases hn with hn | hn
    · left
      simpa only [hn, map_one] using he
    · right
      simpa only [hn, map_neg, map_one] using he
  · rintro (rfl | rfl) <;> simp

/-- Every positive omnific integer is at least one. -/
theorem one_le_omnific_of_pos (x : OmnificInteger.{u}) (hx : 0 < x) : 1 ≤ x := by
  by_contra! hsmall
  have hpos : 0 < omnificToSurreal x := hx
  have hlt : omnificToSurreal x < 1 := hsmall
  have hf : IsFinite (omnificToSurreal x) := (isFinite_iff_exists_nat_abs_le _).mpr
    ⟨1, by simpa only [Nat.cast_one, abs_of_pos hpos] using hlt.le⟩
  obtain ⟨n, hn⟩ := (omnific_isFinite_iff x).mp hf
  rw [hn, omnificToSurreal_intCast] at hpos hlt
  have hnpos : (0 : ℤ) < n := by exact_mod_cast hpos
  have hnlt : n < (1 : ℤ) := by exact_mod_cast hlt
  omega

/-- One is positive and is the least positive element of the actual omnific order. -/
theorem omnific_least_positive :
    (0 : OmnificInteger.{u}) < 1 ∧ ∀ x : OmnificInteger.{u}, 0 < x → 1 ≤ x :=
  ⟨zero_lt_one, one_le_omnific_of_pos⟩

end
end Surreal.Foundations.SignSequence
