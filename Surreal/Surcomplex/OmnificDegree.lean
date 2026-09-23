import Surreal.Foundations.OmnificDegree
import Surreal.Surcomplex.NonnegativeSupportRing
import Surreal.Surcomplex.Leading

/-!
# Degree and constants in the actual complex support ring

The degree convention of `odg:lem:degree`, with degree minus infinity at
zero, and the support-ring consequences needed for `odg:prop:units`.
-/

universe u
namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Conway growth degree, with minus infinity assigned to zero. -/
def growthDegree (z : Surcomplex.{u}) : WithBot SignSequence.{u} :=
  if z = 0 then ⊥ else ↑(leadingExponent z)

@[simp] theorem growthDegree_zero : growthDegree (0 : Surcomplex.{u}) = ⊥ := by
  simp [growthDegree]

/-- On a nonzero normal form, degree is its actual leading growth exponent. -/
theorem growthDegree_of_ne_zero {z : Surcomplex.{u}} (hz : z ≠ 0) :
    growthDegree z = ↑(leadingExponent z) := if_neg hz

@[simp] theorem growthDegree_eq_bot_iff (z : Surcomplex.{u}) : growthDegree z = ⊥ ↔ z = 0 := by
  by_cases hz : z = 0 <;> simp [growthDegree, hz]

/-- Degree adds under multiplication, including the zero cases. -/
theorem growthDegree_mul (z w : Surcomplex.{u}) :
    growthDegree (z * w) = growthDegree z + growthDegree w := by
  by_cases hz : z = 0
  · simp [hz]
  by_cases hw : w = 0
  · simp [hw]
  simp only [growthDegree_of_ne_zero (mul_ne_zero hz hw), growthDegree_of_ne_zero hz,
    growthDegree_of_ne_zero hw, leadingExponent_mul hz hw, WithBot.coe_add]

/-- The degree of a sum is bounded by the larger input degree. -/
theorem growthDegree_add_le (z w : Surcomplex.{u}) :
    growthDegree (z + w) ≤ max (growthDegree z) (growthDegree w) := by
  by_cases hz : z = 0
  · simp [hz]
  by_cases hw : w = 0
  · simp [hw]
  by_cases hs : z + w = 0
  · simp [hs]
  rw [growthDegree_of_ne_zero hs, growthDegree_of_ne_zero hz, growthDegree_of_ne_zero hw,
    ← WithBot.coe_max, WithBot.coe_le_coe]
  have hv := min_valuation_le_add z w
  rw [valuation_of_ne_zero hz, valuation_of_ne_zero hw, valuation_of_ne_zero hs,
    ← WithTop.coe_min, WithTop.coe_le_coe] at hv
  change min (-leadingExponent z) (-leadingExponent w) ≤ -leadingExponent (z + w) at hv
  rw [min_neg_neg, neg_le_neg_iff] at hv
  exact hv

/-- Unequal input degrees cannot cancel in a sum. -/
theorem growthDegree_add_of_ne {z w : Surcomplex.{u}} (hne : growthDegree z ≠ growthDegree w) :
    growthDegree (z + w) = max (growthDegree z) (growthDegree w) := by
  by_cases hz : z = 0
  · simp [hz]
  by_cases hw : w = 0
  · simp [hw]
  have hvne : valuation z ≠ valuation w := by
    intro he
    rw [valuation_of_ne_zero hz, valuation_of_ne_zero hw, WithTop.coe_inj, neg_inj] at he
    apply hne
    rw [growthDegree_of_ne_zero hz, growthDegree_of_ne_zero hw]
    change leadingExponent z = leadingExponent w at he
    rw [he]
  have hv := valuation_add_of_ne hvne
  have hs : z + w ≠ 0 := by
    intro hs
    rw [hs, valuation_zero, valuation_of_ne_zero hz, valuation_of_ne_zero hw,
      ← WithTop.coe_min] at hv
    exact WithTop.top_ne_coe hv
  rw [growthDegree_of_ne_zero hs, growthDegree_of_ne_zero hz, growthDegree_of_ne_zero hw,
    ← WithBot.coe_max, WithBot.coe_inj]
  rw [valuation_of_ne_zero hz, valuation_of_ne_zero hw, valuation_of_ne_zero hs,
    ← WithTop.coe_min, WithTop.coe_inj] at hv
  change -leadingExponent (z + w) = min (-leadingExponent z) (-leadingExponent w) at hv
  rw [min_neg_neg, neg_inj] at hv
  exact hv

/-- A nonzero element of the complex support ring has nonpositive valuation. -/
theorem nonnegativeSupport_valuation_nonpos (z : nonnegativeSupportSubring.{u})
    (hz : z.val ≠ 0) : valuation z.val ≤ 0 := by
  rw [valuation_eq_min_coordinates]
  by_cases hre : z.val.re = 0
  · have him : z.val.im ≠ 0 := by intro h; apply hz; exact Surcomplex.ext hre h
    exact (min_le_right _ _).trans (SignSequence.nonnegativeSupport_valuation_nonpos
      (nonnegativeIm z) him)
  · exact (min_le_left _ _).trans (SignSequence.nonnegativeSupport_valuation_nonpos
      (nonnegativeRe z) hre)

/-- Nonzero elements of the complex support ring have nonnegative growth degree. -/
theorem nonnegativeSupport_leadingExponent_nonneg (z : nonnegativeSupportSubring.{u})
    (hz : z.val ≠ 0) : 0 ≤ leadingExponent z.val := by
  have hv := nonnegativeSupport_valuation_nonpos z hz
  rw [valuation_of_ne_zero hz] at hv
  exact neg_nonpos.mp (WithTop.coe_le_coe.mp hv)

/-- Finiteness in the complex support ring forces an ordinary complex constant. -/
theorem nonnegativeSupport_eq_complexConstant_of_finite (z : nonnegativeSupportSubring.{u})
    (hz : IsFinite z.val) : z = complexConstants (constantCoeff z) := by
  apply Subtype.ext
  apply Surcomplex.ext
  · exact congrArg Subtype.val (SignSequence.nonnegativeSupport_eq_realConstant_of_finite
      (nonnegativeRe z) hz.1)
  · exact congrArg Subtype.val (SignSequence.nonnegativeSupport_eq_realConstant_of_finite
      (nonnegativeIm z) hz.2)

/-- Degree zero in the complex support ring characterizes the nonzero complex constants. -/
theorem nonnegativeSupport_growthDegree_eq_zero_iff (z : nonnegativeSupportSubring.{u}) :
    growthDegree z.val = 0 ↔ ∃ c : ℂ, c ≠ 0 ∧ z = complexConstants c := by
  constructor
  · intro hz
    have hzn : z.val ≠ 0 := by intro h; simp [h] at hz
    have hlead : leadingExponent z.val = 0 := by
      rw [growthDegree_of_ne_zero hzn] at hz
      exact WithBot.coe_inj.mp hz
    have hf : IsFinite z.val := (isFinite_iff_valuation_nonneg _).mpr (by
      rw [valuation_of_ne_zero hzn]
      change (0 : WithTop SignSequence.{u}) ≤ ↑(-leadingExponent z.val)
      simp [hlead])
    have he := nonnegativeSupport_eq_complexConstant_of_finite z hf
    refine ⟨constantCoeff z, ?_, he⟩
    intro hc
    apply hzn
    rw [he, hc, map_zero]
    rfl
  · rintro ⟨c, hc, rfl⟩
    rw [growthDegree_of_ne_zero (show (complexConstants c).val ≠ 0 from
      (map_ne_zero ofComplex).mpr hc)]
    change (leadingExponent (ofComplex c) : WithBot SignSequence.{u}) = 0
    rw [leadingExponent_ofComplex]
    rfl

end
end Surreal.Surcomplex
