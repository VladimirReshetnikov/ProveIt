import Surreal.Algebra.DiophantineConstantsBoundary
import Surreal.Surcomplex.DiophantineConstants
import Surreal.Foundations.OmnificConstantRigidity

/-!
# Actual-ring examples and full-field failure of Xi

The concrete examples and ambient-field warning following
`odg:def:thm:constants`. The full actual surreal and surcomplex fields
satisfy Xi everywhere, whereas a nonzero purely infinite Gaussian part
prevents Xi in the Gaussian omnific ring.
-/

universe u
namespace Surreal

open DiophantineConstants Foundations

noncomputable section

/-- The predicate is true everywhere in the actual full surreal field. -/
theorem Foundations.SignSequence.xi_all_surreal (x : SignSequence.{u}) : Xi x :=
  xi_of_real_hom SignSequence.ofReal.toRingHom x

/-- It is also true everywhere in the actual full surcomplex field. -/
theorem Surcomplex.xi_all_surcomplex (x : Surcomplex.{u}) : Xi x :=
  xi_of_real_hom (Surcomplex.ofReal.comp SignSequence.ofReal.toRingHom) x

namespace Surcomplex

/-- Adding any Gaussian constant to a nonzero purely infinite part cannot satisfy Xi. -/
theorem gaussianOmnific_not_xi_purelyInfinite_add_constant
    (x : GaussianOmnificInteger.{u}) (hx : gaussianOmnificConstantCoeff x = 0) (hx0 : x ≠ 0)
    (a : GaussianInt) : ¬Xi (x + gaussianOmnificConstants a) := by
  intro h
  obtain ⟨b, hb⟩ := (gaussianOmnific_xi_iff _).mp h
  have hc := congrArg gaussianOmnificConstantCoeff hb
  simp only [map_add, hx, gaussianOmnificConstantCoeff_constants, zero_add] at hc
  rw [← hc] at hb
  exact hx0 (add_right_cancel (hb.trans (zero_add _).symm))

/-- The positive Conway monomial of exponent one, as an actual Gaussian omnific integer. -/
def gaussianOmnificOmega : GaussianOmnificInteger.{u} :=
  ⟨omnificSupportInclusion (SignSequence.omnificMonomial 1 zero_lt_one), 0, by
    have hz := SignSequence.omnificMonomial_mem_purelyInfinite (1 : SignSequence.{u}) zero_lt_one
    change SignSequence.omnificConstantCoeff (SignSequence.omnificMonomial 1 zero_lt_one) = 0 at hz
    rw [constantCoeff_omnificSupportInclusion, hz, Int.cast_zero, map_zero]⟩

/-- Its actual surcomplex value is the real Conway monomial omega. -/
theorem gaussianOmnificOmega_val :
    gaussianOmnificToSurcomplex gaussianOmnificOmega.{u} = ofReal (SignSequence.omegaPower 1) := rfl

/-- The monomial is nonzero. -/
theorem gaussianOmnificOmega_ne_zero : gaussianOmnificOmega.{u} ≠ 0 := by
  intro h
  apply SignSequence.omnificMonomial_ne_zero (1 : SignSequence.{u}) zero_lt_one
  apply omnificSupportInclusion_injective
  have he := congrArg Subtype.val h
  change omnificSupportInclusion (SignSequence.omnificMonomial 1 zero_lt_one) = 0 at he
  simpa only [map_zero] using he

/-- The monomial has zero Gaussian constant coefficient. -/
theorem gaussianOmnificOmega_constantCoeff :
    gaussianOmnificConstantCoeff gaussianOmnificOmega.{u} = 0 := by
  apply GaussianInt.toComplex_injective
  rw [gaussianOmnificConstantCoeff_toComplex, map_zero]
  change constantCoeff (omnificSupportInclusion (SignSequence.omnificMonomial 1 zero_lt_one)) = 0
  rw [constantCoeff_omnificSupportInclusion]
  have hz := SignSequence.omnificMonomial_mem_purelyInfinite (1 : SignSequence.{u}) zero_lt_one
  change SignSequence.omnificConstantCoeff (SignSequence.omnificMonomial 1 zero_lt_one) = 0 at hz
  rw [hz, Int.cast_zero]

/-- The printed omega+i example has no five-witness solution in the actual Gaussian omnific ring. -/
theorem gaussianOmnific_omega_add_I_not_xi :
    ¬Xi (gaussianOmnificOmega.{u} + gaussianOmnificConstants (⟨0, 1⟩ : GaussianInt)) :=
  gaussianOmnific_not_xi_purelyInfinite_add_constant gaussianOmnificOmega
    gaussianOmnificOmega_constantCoeff gaussianOmnificOmega_ne_zero _

end Surcomplex
end
end Surreal
