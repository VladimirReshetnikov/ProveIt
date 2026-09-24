import Surreal.Algebra.BinaryFormRigidity
import Surreal.Surcomplex.OmnificDecomposableFibers
import Surreal.Foundations.OmnificEquationalTransfer

/-!
# Binary-form rigidity in the actual support and omnific rings

The full `odg:thm:binary`. Two distinct projective linear factors are
represented by native polynomial divisors with nonzero coefficient
determinant. The conclusion holds without an additional homogeneity
hypothesis, and integer polynomial fibers agree exactly with ordinary ones.
-/

universe u
namespace Surreal.Surcomplex

open Foundations BinaryFormRigidity

noncomputable section

attribute [local instance] nonnegativeSupportComplexAlgebra

/-- Nonzero constant levels with two projectively distinct linear factors have constant coordinates. -/
theorem nonnegativeSupport_binary_rigidity (p : MvPolynomial (Fin 2) ℂ)
    (hp : HasTwoProjectiveFactors p) (c : ℂ) (hc : c ≠ 0)
    (x : Fin 2 → nonnegativeSupportSubring.{u})
    (hx : p.eval₂ complexConstants x = complexConstants c) :
    ∀ k, x k = complexConstants (constantCoeff (x k)) :=
  BinaryFormRigidity.coordinates_constant constantCoeffAlgHom nonnegativeSupport_unit_eq_constant
    p hp x c hc hx

/-- The inclusion of actual omnific integers in the complex support ring is faithful. -/
theorem omnificSupportInclusion_injective : Function.Injective (omnificSupportInclusion.{u}) := by
  intro x y h
  apply SignSequence.omnificToSurreal_injective
  apply ofReal_injective
  exact congrArg Subtype.val h

/-- On real omnific coordinates, binary-form rigidity forces ordinary integers. -/
theorem omnific_binary_rigidity (p : MvPolynomial (Fin 2) ℂ)
    (hp : HasTwoProjectiveFactors p) (c : ℂ) (hc : c ≠ 0)
    (x : Fin 2 → SignSequence.OmnificInteger.{u})
    (hx : p.eval₂ complexConstants (fun k => omnificSupportInclusion (x k)) = complexConstants c) :
    ∀ k, x k = SignSequence.omnificIntCast (SignSequence.omnificConstantCoeff (x k)) := by
  have h := nonnegativeSupport_binary_rigidity p hp c hc
    (fun k => omnificSupportInclusion (x k)) hx
  intro k
  apply omnificSupportInclusion_injective
  rw [omnificSupportInclusion_intCast]
  simpa only [constantCoeff_omnificSupportInclusion] using h k

/-- Complexifying integer coefficients and then evaluating agrees with the actual ring inclusion. -/
theorem omnific_eval_complexification (p : MvPolynomial (Fin 2) ℤ)
    (x : Fin 2 → SignSequence.OmnificInteger.{u}) :
    (p.map (Int.castRingHom ℂ)).eval₂ complexConstants (fun k => omnificSupportInclusion (x k)) =
      omnificSupportInclusion (p.eval₂ SignSequence.omnificIntCast x) := by
  have hi : complexConstants.comp (Int.castRingHom ℂ) =
      omnificSupportInclusion.comp (SignSequence.omnificIntCast.{u}) :=
    RingHom.ext fun a => (omnificSupportInclusion_intCast a).symm
  rw [MvPolynomial.eval₂_map, hi, MvPolynomial.hom_eval₂]

/-- An integer binary polynomial with two distinct complex projective factors has precisely its
ordinary integer solutions at each nonzero ordinary integer level. -/
theorem omnific_integer_binary_solutions_iff (p : MvPolynomial (Fin 2) ℤ)
    (hp : HasTwoProjectiveFactors (p.map (Int.castRingHom ℂ))) (c : ℤ) (hc : c ≠ 0)
    (x : Fin 2 → SignSequence.OmnificInteger.{u}) :
    p.eval₂ SignSequence.omnificIntCast x = SignSequence.omnificIntCast c ↔
      ∃ a : Fin 2 → ℤ, p.eval a = c ∧ ∀ k, x k = SignSequence.omnificIntCast (a k) := by
  constructor
  · intro hx
    have hxc : (p.map (Int.castRingHom ℂ)).eval₂ complexConstants
        (fun k => omnificSupportInclusion (x k)) = complexConstants (c : ℂ) := by
      rw [omnific_eval_complexification, hx, omnificSupportInclusion_intCast]
    have hconst := omnific_binary_rigidity _ hp (c : ℂ) (Int.cast_ne_zero.mpr hc) x hxc
    refine ⟨fun k => SignSequence.omnificConstantCoeff (x k), ?_, hconst⟩
    rw [← SignSequence.omnificConstantCoeff_eval, hx, SignSequence.omnificConstantCoeff_intCast]
  · rintro ⟨a, ha, hx⟩
    have hxe : x = SignSequence.omnificIntCast ∘ a := funext hx
    rw [hxe, ← MvPolynomial.eval₂_comp, ha]

end
end Surreal.Surcomplex
