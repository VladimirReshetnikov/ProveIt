import Surreal.Surcomplex.OmnificDegree
import Surreal.Foundations.OmnificUnits

/-!
# Units of the actual complex support ring

Completes the complex clause of `odg:prop:units`. Together with the real
and omnific classifications, this gives all three unit groups stated in
the source, retaining their actual-field embeddings.
-/

universe u
namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- A unit of the complex support ring is finite, since both factor degrees are nonnegative. -/
theorem nonnegativeSupport_finite_of_isUnit (z : nonnegativeSupportSubring.{u})
    (hz : IsUnit z) : IsFinite z.val := by
  obtain ⟨w, hw⟩ := hz.exists_right_inv
  have he : z.val * w.val = 1 := congrArg Subtype.val hw
  have hzn : z.val ≠ 0 := left_ne_zero_of_mul_eq_one he
  have hwn : w.val ≠ 0 := right_ne_zero_of_mul_eq_one he
  have hs : leadingExponent z.val + leadingExponent w.val = 0 := by
    rw [← leadingExponent_mul hzn hwn, he]
    simpa only [map_one] using leadingExponent_ofComplex.{u} (1 : ℂ)
  have hlead : leadingExponent z.val ≤ 0 := by
    linarith [nonnegativeSupport_leadingExponent_nonneg w hwn]
  apply (isFinite_iff_valuation_nonneg _).mpr
  rw [valuation_of_ne_zero hzn]
  exact WithTop.coe_le_coe.mpr (neg_nonneg.mpr hlead)

/-- The units of the complex support ring are exactly the nonzero ordinary complex constants. -/
theorem nonnegativeSupport_isUnit_iff (z : nonnegativeSupportSubring.{u}) :
    IsUnit z ↔ ∃ c : ℂ, c ≠ 0 ∧ z = complexConstants c := by
  constructor
  · intro hz
    exact ⟨constantCoeff z, (hz.map constantCoeff).ne_zero,
      nonnegativeSupport_eq_complexConstant_of_finite z (nonnegativeSupport_finite_of_isUnit z hz)⟩
  · rintro ⟨c, hc, rfl⟩
    exact (isUnit_iff_ne_zero.mpr hc).map complexConstants

/-- In the complex support ring, being a unit is equivalent to having degree zero. -/
theorem nonnegativeSupport_isUnit_iff_growthDegree_eq_zero (z : nonnegativeSupportSubring.{u}) :
    IsUnit z ↔ growthDegree z.val = 0 :=
  (nonnegativeSupport_isUnit_iff z).trans (nonnegativeSupport_growthDegree_eq_zero_iff z).symm

end
end Surreal.Surcomplex
