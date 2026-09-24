import Surreal.Algebra.SeparableNormFactors
import Surreal.Algebra.DecomposableFibers

/-!
# Constant coordinates in separable norm fibers

The norm-rigidity mechanism of `odg:thm:norm`. The native determinant norm
polynomial factors after coefficient extension. The embedding matrix is
proved injective, and the constant-unit property then gives rigidity.
-/

namespace Surreal.NormForm

open Module

noncomputable section

/-- A nonzero constant norm level has constant coordinates in a constant-field algebra
whose units are constants. No embedding of L in B is needed. -/
theorem coordinates_constant {K L E B ι : Type*} [Field K] [Infinite K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [Module.Finite K L] [Algebra.IsSeparable K L] [IsAlgClosed E]
    [CommRing B] [Algebra E B] [Fintype ι] [DecidableEq ι]
    (ct : B →ₐ[E] E) (hunit : ∀ z : B, IsUnit z → z = algebraMap E B (ct z))
    (b : Basis ι K L) (c : E) (hc : c ≠ 0) (x : ι → B)
    (hx : (polynomial b).eval₂ ((algebraMap E B).comp (algebraMap K E)) x = algebraMap E B c) :
    ∀ j, x j = algebraMap E B (ct (x j)) := by
  classical
  rw [eval₂_polynomial_eq_prod] at hx
  apply DecomposableFibers.coordinates_constant_of_injective ct hunit
    (fun _ => 0) (embeddingMatrix b) (fun _ => 1) (fun _ => one_ne_zero) c hc x
  · simpa only [DecomposableFibers.value, DecomposableFibers.affineValue,
      map_zero, zero_add, pow_one, Algebra.smul_def, embeddingMatrix] using hx
  · exact embeddingMatrix_injective b

end
end Surreal.NormForm
