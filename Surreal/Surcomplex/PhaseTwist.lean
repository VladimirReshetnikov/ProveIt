import Surreal.Surcomplex.CharacterAutomorphisms
import Surreal.Surcomplex.DiophantineConstantsBoundary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# A phase twist moving the actual real axis

The literal phase character and automorphism of `odg:def:lem:twist`,
with the algebraic witnesses used by `odg:def:thm:norealaxis`.
The latter's formal first-order definability assertions are separate.
-/

universe u
namespace Surreal.Surcomplex
open Foundations
noncomputable section

/-- The coefficient of omega to the zeroth power is additive on the whole actual surreal field. -/
def exponentConstantCoefficient : SignSequence.{u} →+ ℝ where
  toFun a := (SignSequence.rawNormalForm a).coeff 0
  map_zero' := by rw [SignSequence.rawNormalForm_zero, _root_.HahnSeries.coeff_zero]
  map_add' a b := by rw [SignSequence.rawNormalForm_add, _root_.HahnSeries.coeff_add]

@[simp] theorem exponentConstantCoefficient_one : exponentConstantCoefficient (1 : SignSequence.{u}) = 1 := by
  change (SignSequence.rawNormalForm 1).coeff 0 = 1
  rw [SignSequence.rawNormalForm_one, _root_.HahnSeries.coeff_one, if_pos rfl]

@[simp] theorem exponentConstantCoefficient_omega :
    exponentConstantCoefficient (SignSequence.omegaPower (1 : SignSequence.{u})) = 0 := by
  change (SignSequence.rawNormalForm (SignSequence.omegaPower (1 : SignSequence.{u}))).coeff 0 = 0
  rw [SignSequence.rawNormalForm_omegaPower, _root_.HahnSeries.coeff_single]
  norm_num

@[simp] theorem exponentConstantCoefficient_inv_omega :
    exponentConstantCoefficient (SignSequence.omegaPower (1 : SignSequence.{u}))⁻¹ = 0 := by
  rw [← SignSequence.omegaPower_neg]
  change (SignSequence.rawNormalForm (SignSequence.omegaPower (-(1 : SignSequence.{u})))).coeff 0 = 0
  rw [SignSequence.rawNormalForm_omegaPower, _root_.HahnSeries.coeff_single]
  norm_num

/-- The zero-coefficient map on the whole exponent field is not multiplicative. -/
theorem exponentConstantCoefficient_not_multiplicative :
    ¬ ∀ a b : SignSequence.{u}, exponentConstantCoefficient (a * b) =
      exponentConstantCoefficient a * exponentConstantCoefficient b := by
  intro h
  have he := h (SignSequence.omegaPower 1) (SignSequence.omegaPower 1)⁻¹
  rw [mul_inv_cancel₀ (SignSequence.omegaPower_ne_zero 1), exponentConstantCoefficient_one,
    exponentConstantCoefficient_omega, exponentConstantCoefficient_inv_omega, zero_mul] at he
  exact one_ne_zero he

/-- The source's phase character, using only the ordinary complex exponential. -/
def phaseCharacter : AddChar SignSequence.{u} ℂ where
  toFun a := Complex.exp ((exponentConstantCoefficient a : ℂ) * (Real.pi / 2) * Complex.I)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    rw [map_add, Complex.ofReal_add, add_mul, add_mul, Complex.exp_add]

@[simp] theorem phaseCharacter_one : phaseCharacter (1 : SignSequence.{u}) = Complex.I := by
  change Complex.exp ((exponentConstantCoefficient (1 : SignSequence.{u}) : ℂ) * (Real.pi / 2) * Complex.I) = _
  rw [exponentConstantCoefficient_one, Complex.ofReal_one, one_mul]
  exact Complex.exp_pi_div_two_mul_I

/-- Express the phase character in the native dual growth indices used by canonical Hahn forms. -/
def nativePhaseCharacter : AddChar (_root_.Surreal.{u}ᵒᵈ) ℂ :=
  phaseCharacter.compAddMonoidHom SignSequence.growthExponentEquiv.symm.toAddMonoidHom

@[simp] theorem nativePhaseCharacter_toSurreal (a : SignSequence.{u}) :
    nativePhaseCharacter (OrderDual.toDual (SignSequence.toSurreal a)) = phaseCharacter a := by
  change phaseCharacter (SignSequence.growthExponentEquiv.symm (SignSequence.growthExponentEquiv a)) = _
  rw [AddEquiv.symm_apply_apply]

/-- The actual field automorphism obtained from the printed phase character. -/
def phaseTwist : Surcomplex.{u} ≃+* Surcomplex.{u} := characterAutomorphism nativePhaseCharacter

/-- The phase twist fixes the full ordinary complex coefficient field pointwise. -/
theorem phaseTwist_ofComplex (c : ℂ) : phaseTwist (ofComplex c : Surcomplex.{u}) = ofComplex c :=
  characterAutomorphism_ofComplex nativePhaseCharacter c

theorem phaseTwist_support (z : Surcomplex.{u}) :
    (rawNormalForm (phaseTwist z)).support = (rawNormalForm z).support :=
  support_characterAutomorphism nativePhaseCharacter z

/-- The decisive monomial is sent outside the real axis. -/
theorem phaseTwist_omega : phaseTwist (ofReal (SignSequence.omegaPower (1 : SignSequence.{u}))) =
    I * ofReal (SignSequence.omegaPower 1) := by
  change characterAutomorphism nativePhaseCharacter _ = _
  rw [characterAutomorphism_real_omegaPower, nativePhaseCharacter_toSurreal, phaseCharacter_one, ofComplex_I]

/-- The same phase twist is an automorphism of the actual Gaussian omnific ring. -/
def gaussianPhaseTwist : GaussianOmnificInteger.{u} ≃+* GaussianOmnificInteger.{u} :=
  gaussianCharacterAutomorphism nativePhaseCharacter

@[simp] theorem gaussianPhaseTwist_value (z : GaussianOmnificInteger.{u}) :
    gaussianOmnificToSurcomplex (gaussianPhaseTwist z) = phaseTwist (gaussianOmnificToSurcomplex z) := rfl

theorem gaussianPhaseTwist_constants (a : GaussianInt) :
    gaussianPhaseTwist (gaussianOmnificConstants.{u} a) = gaussianOmnificConstants a :=
  gaussianCharacterAutomorphism_constants nativePhaseCharacter a

/-- The image of omega under the coefficient-fixing twist is not any actual real number. -/
theorem phaseTwist_omega_not_real :
    ¬ ∃ a : SignSequence.{u}, phaseTwist (ofReal (SignSequence.omegaPower 1)) = ofReal a := by
  rintro ⟨a, ha⟩
  rw [phaseTwist_omega] at ha
  have hi := congrArg QuadraticAlgebra.im ha
  simp only [mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul, zero_add] at hi
  exact SignSequence.omegaPower_ne_zero 1 hi

/-- Actual conjugation fails to commute with the phase twist already at omega. -/
theorem phaseTwist_conjugation_omega :
    phaseTwist (conj (ofReal (SignSequence.omegaPower (1 : SignSequence.{u})))) ≠
      conj (phaseTwist (ofReal (SignSequence.omegaPower 1))) := by
  rw [conj_ofReal, phaseTwist_omega, conj_mul, conj_I, conj_ofReal]
  intro h
  have hz : I * ofReal (SignSequence.omegaPower (1 : SignSequence.{u})) = 0 :=
    neg_eq_self.mp (by simpa only [neg_mul] using h.symm)
  have hi := congrArg QuadraticAlgebra.im hz
  simp only [mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul, zero_add,
    QuadraticAlgebra.im_zero] at hi
  exact SignSequence.omegaPower_ne_zero 1 hi

/-- Even in the pure Gaussian omnific ring, the twist moves an omnific element outside the real ring. -/
theorem gaussianPhaseTwist_omega_not_omnific :
    ¬ ∃ a : SignSequence.OmnificInteger.{u}, gaussianOmnificToSurcomplex
      (gaussianPhaseTwist gaussianOmnificOmega) = ofReal (SignSequence.omnificToSurreal a) := by
  rintro ⟨a, ha⟩
  apply phaseTwist_omega_not_real
  refine ⟨SignSequence.omnificToSurreal a, ?_⟩
  simpa only [gaussianPhaseTwist_value, gaussianOmnificOmega_val] using ha

end
end Surreal.Surcomplex
