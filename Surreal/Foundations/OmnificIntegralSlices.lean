import Surreal.Algebra.CoefficientPullbackIntegrality
import Surreal.Foundations.OmnificIntegralClosure
import Surreal.Foundations.OmnificAlgebraAbsorption

/-!
# Constant and support slices of the actual omnific normalization

The actual-surreal clauses of `osq:nm:thm:realslice` and
`osq:nm:eq:realslice`. On nonnegative growth support, integrality is
exactly algebraic integrality of the real constant coefficient.
The intersections with ordinary reals and rationals follow.
-/

universe u
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- On the nonnegative-support ring, integrality is exactly integrality of the constant coefficient. -/
theorem omnific_nonnegative_isIntegral_iff (x : nonnegativeSupportSubring.{u}) :
    IsIntegral OmnificInteger (x : SignSequence) ↔ IsIntegral ℤ (constantCoeff x) :=
  CoefficientPullback.integralElem_ambient_iff constantCoeff (Int.castRingHom ℝ)
    Int.cast_injective realConstants constantCoeff_realConstants
    nonnegativeSupportSubring.subtype Subtype.val_injective x

/-- The native support-slice equality for the actual omnific integral closure. -/
theorem omnific_integralClosure_support_slice :
    (integralClosure OmnificInteger SignSequence.{u}).toSubring.comap
        nonnegativeSupportSubring.subtype =
      (integralClosure ℤ ℝ).toSubring.comap constantCoeff := by
  ext x
  exact omnific_nonnegative_isIntegral_iff x

/-- An ordinary real is integral over the omnific integers exactly when it is an algebraic integer. -/
theorem omnific_ofReal_isIntegral_iff (r : ℝ) :
    IsIntegral OmnificInteger.{u} (ofReal r : SignSequence.{u}) ↔ IsIntegral ℤ r := by
  have h := omnific_nonnegative_isIntegral_iff (realConstants.{u} r)
  rwa [constantCoeff_realConstants] at h

/-- The real slice is precisely the native ring of real algebraic integers. -/
theorem omnific_integralClosure_real_slice :
    (integralClosure OmnificInteger SignSequence.{u}).toSubring.comap ofReal.toRingHom =
      (integralClosure ℤ ℝ).toSubring := by
  ext r
  exact omnific_ofReal_isIntegral_iff r

/-- A rational surreal is integral over the omnific integers exactly when it is an ordinary integer. -/
theorem omnific_ratCast_isIntegral_iff (q : ℚ) :
    IsIntegral OmnificInteger.{u} (q : SignSequence.{u}) ↔ ∃ n : ℤ, (n : ℚ) = q := by
  rw [← map_ratCast ofReal q, omnific_ofReal_isIntegral_iff]
  have hc : IsIntegral ℤ (q : ℝ) ↔ IsIntegral ℤ q := by
    exact isIntegral_algHom_iff (Rat.castHom ℝ |>.toIntAlgHom) Rat.cast_injective
  rw [hc]
  exact IsIntegrallyClosed.isIntegral_iff

/-- The rational slice is exactly the image of the ordinary integers. -/
theorem omnific_integralClosure_rat_slice :
    (integralClosure OmnificInteger SignSequence.{u}).toSubring.comap (Rat.castHom SignSequence) =
      (Int.castRingHom ℚ).range := by
  ext q
  exact omnific_ratCast_isIntegral_iff q

/-- Adding an omnific element does not change the integrality test for a real constant. -/
theorem omnific_real_add_isIntegral_iff (r : ℝ) (p : OmnificInteger.{u}) :
    IsIntegral OmnificInteger (ofReal r + omnificToSurreal p) ↔ IsIntegral ℤ r := by
  constructor
  · intro h
    apply (omnific_ofReal_isIntegral_iff r).mp
    have hp : IsIntegral OmnificInteger (omnificToSurreal p) :=
      isIntegral_algebraMap (x := p) (A := SignSequence.{u})
    simpa only [add_sub_cancel_right] using h.sub hp
  · intro h
    exact ((omnific_ofReal_isIntegral_iff r).mpr h).add isIntegral_algebraMap

/-- The support-slice equality as an algebraic integer plus a purely infinite omnific element. -/
theorem omnific_integral_support_decomposition (x : nonnegativeSupportSubring.{u}) :
    IsIntegral OmnificInteger (x : SignSequence) ↔
      ∃ r : ℝ, IsIntegral ℤ r ∧ ∃ p : OmnificInteger,
        p ∈ omnificPurelyInfiniteIdeal ∧ (x : SignSequence) = ofReal r + omnificToSurreal p := by
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := real_constant_decomposition x
    let p : OmnificInteger := ⟨y, purelyInfinite_mem_omnificSubring y hy⟩
    refine ⟨constantCoeff x, (omnific_nonnegative_isIntegral_iff x).mp hx, p, ?_, ?_⟩
    · exact (mem_omnificPurelyInfiniteIdeal_iff p).mpr ((mem_purelyInfiniteIdeal_iff y).mp hy)
    · exact congrArg Subtype.val he
  · rintro ⟨r, hr, p, _, he⟩
    rw [he]
    exact (omnific_real_add_isIntegral_iff r p).mpr hr

/-- Every real multiple of omega plus sqrt(2) is integral, including the manuscript's pi example. -/
theorem omnific_scaled_omega_add_sqrt_two_isIntegral (c : ℝ) :
    IsIntegral OmnificInteger.{u}
      (ofReal c * omegaPower 1 + ofReal (Real.sqrt 2) : SignSequence.{u}) := by
  let p := omnificRealScale c (omnificMonomial (1 : SignSequence.{u}) zero_lt_one)
    (omnificMonomial_mem_purelyInfinite 1 zero_lt_one)
  have hp : IsIntegral OmnificInteger (omnificToSurreal p) := isIntegral_algebraMap
  exact hp.add omnific_sqrt_two_isIntegral

/-- Omega plus one half is almost integral, but its nonintegral constant term excludes integrality. -/
theorem omnific_omega_add_half_almost_not_integral :
    IsAlmostIntegral OmnificInteger.{u} (omegaPower 1 + 2⁻¹ : SignSequence.{u}) ∧
      ¬ IsIntegral OmnificInteger.{u} (omegaPower 1 + 2⁻¹ : SignSequence.{u}) := by
  refine ⟨omnific_isAlmostIntegral _, ?_⟩
  intro h
  apply omnific_half_almost_not_integral.2
  have hp : IsIntegral OmnificInteger.{u} (omegaPower 1 : SignSequence.{u}) := by
    exact isIntegral_algebraMap (x := omnificMonomial 1 zero_lt_one)
  simpa only [add_sub_cancel_left] using h.sub hp

end
end Surreal.Foundations.SignSequence
