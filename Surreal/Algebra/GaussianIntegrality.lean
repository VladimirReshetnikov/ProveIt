import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Analysis.Complex.IsIntegral
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Gaussian and ordinary algebraic integrality

The coefficient-ring step of `osq:nm:thm:complexnormal` and
`osq:nm:eq:complexslice`: integrality over the Gaussian integers is the
same as integrality over the ordinary integers. We reuse Mathlib's
integrality of i, injective descent and transitivity.
-/

namespace Surreal.GaussianIntegrality
noncomputable section

/-- Every native Gaussian integer is integral over the ordinary integers. -/
theorem gaussianInteger_isIntegral (z : GaussianInt) : IsIntegral ℤ z := by
  apply (isIntegral_algHom_iff GaussianInt.toComplex.toIntAlgHom
    GaussianInt.toComplex_injective).mp
  change IsIntegral ℤ ((z.re : ℂ) + (z.im : ℂ) * Complex.I)
  exact (isIntegral_intCast z.re).add ((isIntegral_intCast z.im).mul Complex.isIntegral_int_I)

/-- The complex coefficients integral over Z[i] are exactly the algebraic integers over Z. -/
theorem coefficient_integral_iff (z : ℂ) :
    GaussianInt.toComplex.IsIntegralElem z ↔ IsIntegral ℤ z := by
  letI : Algebra GaussianInt ℂ := GaussianInt.toComplex.toAlgebra
  letI : Algebra.IsIntegral ℤ GaussianInt := ⟨gaussianInteger_isIntegral⟩
  change IsIntegral GaussianInt z ↔ IsIntegral ℤ z
  exact ⟨fun h => isIntegral_trans z h, fun h => h.tower_top⟩

end
end Surreal.GaussianIntegrality
