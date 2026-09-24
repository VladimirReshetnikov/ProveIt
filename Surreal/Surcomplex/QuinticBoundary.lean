import Surreal.Algebra.QuinticBoundary
import Surreal.Foundations.OmnificQuintic
import Surreal.Surcomplex.DiophantineConstantsBoundary

/-!
# The actual real and Gaussian boundary examples for the quintic

Completes the counterexamples in `odg:def:rem:quintic`. No ordinary shift
of a nonzero purely infinite omnific integer satisfies the real quintic.
In the Gaussian omnific ring, the positive Conway monomial omega does
satisfy it, using a square root of -i times the half-exponent monomial.
-/

universe u
namespace Surreal

open Foundations QuinticConstants

noncomputable section

namespace Foundations.SignSequence

/-- A nonzero purely infinite part cannot be repaired by an ordinary integer shift. -/
theorem omnific_not_quintic_purelyInfinite_add_int (x : OmnificInteger.{u})
    (hx : omnificConstantCoeff x = 0) (hx0 : x ≠ 0) (n : ℤ) :
    ¬Defines (x + omnificIntCast n) := by
  intro h
  obtain ⟨m, hm⟩ := (omnific_quintic_iff _).mp h
  have hc := congrArg omnificConstantCoeff hm
  simp only [map_add, hx, omnificConstantCoeff_intCast, _root_.zero_add] at hc
  rw [← hc] at hm
  exact hx0 (_root_.add_right_cancel (hm.trans (_root_.zero_add _).symm))

/-- In particular neither omega nor omega+1, nor any other integer shift, has witnesses. -/
theorem omnific_omega_add_int_not_quintic (n : ℤ) :
    ¬Defines (omnificMonomial (1 : SignSequence.{u}) zero_lt_one + omnificIntCast n) :=
  omnific_not_quintic_purelyInfinite_add_int _
    (omnificMonomial_mem_purelyInfinite _ _) (omnificMonomial_ne_zero _ _) n

end Foundations.SignSequence

namespace Surcomplex

/-- Any complex multiple of a positive monomial still has Gaussian constant term zero. -/
def gaussianScaledMonomial (c : ℂ) (a : SignSequence.{u}) (ha : 0 < a) :
    GaussianOmnificInteger.{u} :=
  ⟨complexConstants c * omnificSupportInclusion (SignSequence.omnificMonomial a ha), 0, by
    have hz := SignSequence.omnificMonomial_mem_purelyInfinite a ha
    change SignSequence.omnificConstantCoeff (SignSequence.omnificMonomial a ha) = 0 at hz
    rw [map_mul, constantCoeff_complexConstants, constantCoeff_omnificSupportInclusion,
      hz, Int.cast_zero, mul_zero, map_zero]⟩

/-- Its value is the claimed scalar multiple in the actual surcomplex field. -/
theorem gaussianScaledMonomial_val (c : ℂ) (a : SignSequence.{u}) (ha : 0 < a) :
    gaussianOmnificToSurcomplex (gaussianScaledMonomial c a ha) =
      ofComplex c * ofReal (SignSequence.omegaPower a) := rfl

/-- The chosen half-exponent monomial has the required square in the Gaussian omnific ring. -/
theorem gaussianScaledHalfMonomial_sq (c : ℂ) (hc : c ^ 2 = -Complex.I) :
    gaussianScaledMonomial c (1 / 2 : SignSequence.{u}) (by norm_num) ^ 2 =
      -gaussianOmnificConstants (⟨0, 1⟩ : GaussianInt) * gaussianOmnificOmega := by
  have hω : SignSequence.omegaPower (1 / 2 : SignSequence.{u}) ^ 2 =
      SignSequence.omegaPower 1 := by
    rw [pow_two, ← SignSequence.omegaPower_add]
    congr 1
    ring
  apply Subtype.ext
  apply Subtype.ext
  change (ofComplex c * ofReal (SignSequence.omegaPower (1 / 2))) ^ 2 =
    -ofComplex (GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt)) * ofReal (SignSequence.omegaPower 1)
  have hi : GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt) = Complex.I := by
    simp [GaussianInt.toComplex_def]
  rw [hi, mul_pow, ← map_pow, ← map_pow, hc, hω, map_neg]

/-- The real Conway monomial omega satisfies the quintic in the Gaussian omnific ring. -/
theorem gaussianOmnific_omega_quintic : Defines (gaussianOmnificOmega.{u}) := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (-Complex.I) zero_lt_two
  let i := gaussianOmnificConstants.{u} (⟨0, 1⟩ : GaussianInt)
  let s := gaussianScaledMonomial c (1 / 2 : SignSequence.{u}) (by norm_num)
  have hi : i ^ 2 = -1 := by
    change gaussianOmnificConstants.{u} (⟨0, 1⟩ : GaussianInt) ^ 2 = -1
    rw [← map_pow, show (⟨0, 1⟩ : GaussianInt) ^ 2 = -1 by decide, map_neg, map_one]
  exact ⟨1, 0, 1, ![i, s, 0, 0], complex_collapse _ i s hi (gaussianScaledHalfMonomial_sq c hc)⟩

/-- This accepted Gaussian omnific element is not an ordinary Gaussian constant. -/
theorem gaussianOmnific_omega_quintic_nonconstant :
    Defines (gaussianOmnificOmega.{u}) ∧
      ¬∃ a : GaussianInt, gaussianOmnificOmega.{u} = gaussianOmnificConstants a := by
  refine ⟨gaussianOmnific_omega_quintic, ?_⟩
  rintro ⟨a, ha⟩
  have hc := congrArg gaussianOmnificConstantCoeff ha
  rw [gaussianOmnificOmega_constantCoeff, gaussianOmnificConstantCoeff_constants] at hc
  rw [← hc, map_zero] at ha
  exact gaussianOmnificOmega_ne_zero ha

end Surcomplex
end
end Surreal
