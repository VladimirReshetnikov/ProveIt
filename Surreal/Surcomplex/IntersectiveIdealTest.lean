import Surreal.Algebra.IntersectiveIdealTest
import Surreal.Surcomplex.IntersectiveDetector

/-!
# The largest root-free ideals of the actual omnific rings

The actual-carrier instances of `odg:def:thm:idealtest`,
`odg:def:eq:idealtest`, and `odg:def:cor:universal`.
-/

universe u
namespace Surreal

open IntersectivePolynomial

noncomputable section

namespace Foundations.SignSequence

/-- An actual omnific ideal contains a Lambda value exactly when it escapes the purely infinite ideal. -/
theorem omnific_ideal_contains_value_iff (J : Ideal OmnificInteger.{u}) :
    (∃ t : OmnificInteger.{u}, value t ∈ J) ↔ ¬J ≤ omnificPurelyInfiniteIdeal :=
  exists_value_mem_iff omnificPurelyInfiniteIdeal omnific_detector_iff J

/-- Exactly the ideals contained in the purely infinite ideal have root-free quotients. -/
theorem omnific_quotient_no_root_iff (J : Ideal OmnificInteger.{u}) :
    (∀ t : OmnificInteger.{u} ⧸ J, value t ≠ 0) ↔ J ≤ omnificPurelyInfiniteIdeal :=
  quotient_no_root_iff omnificPurelyInfiniteIdeal omnific_detector_iff J

/-- The actual purely infinite ideal is the greatest ideal with a root-free quotient. -/
theorem omnific_greatest_root_free_ideal :
    IsGreatest {J : Ideal OmnificInteger.{u} | ∀ t : OmnificInteger.{u} ⧸ J, value t ≠ 0}
      omnificPurelyInfiniteIdeal :=
  greatest_root_free_ideal omnificPurelyInfiniteIdeal omnific_detector_iff

/-- The universal ring formula defines the actual purely infinite ideal. -/
theorem omnific_purelyInfinite_iff_universal (a : OmnificInteger.{u}) :
    a ∈ omnificPurelyInfiniteIdeal ↔ ∀ s t : OmnificInteger.{u}, a * s ≠ value t :=
  mem_iff_universal omnificPurelyInfiniteIdeal omnific_detector_iff a

/-- The same formula on the difference detects equality of actual integer constant terms. -/
theorem omnific_constant_eq_iff_universal (a b : OmnificInteger.{u}) :
    omnificConstantCoeff a = omnificConstantCoeff b ↔
      ∀ s t : OmnificInteger.{u}, (a - b) * s ≠ value t :=
  constant_eq_iff_universal omnificConstantCoeff omnific_detector_iff a b

end Foundations.SignSequence
namespace Surcomplex

/-- Every actual Gaussian omnific ideal is tested by the same polynomial. -/
theorem gaussianOmnific_ideal_contains_value_iff (J : Ideal GaussianOmnificInteger.{u}) :
    (∃ t : GaussianOmnificInteger.{u}, value t ∈ J) ↔
      ¬J ≤ RingHom.ker gaussianOmnificConstantCoeff.{u} :=
  exists_value_mem_iff (RingHom.ker gaussianOmnificConstantCoeff.{u}) gaussianOmnific_detector_iff J

/-- The root-free Gaussian quotients are precisely those below the constant-term kernel. -/
theorem gaussianOmnific_quotient_no_root_iff (J : Ideal GaussianOmnificInteger.{u}) :
    (∀ t : GaussianOmnificInteger.{u} ⧸ J, value t ≠ 0) ↔
      J ≤ RingHom.ker gaussianOmnificConstantCoeff.{u} :=
  quotient_no_root_iff (RingHom.ker gaussianOmnificConstantCoeff.{u}) gaussianOmnific_detector_iff J

/-- The Gaussian constant-term kernel is the greatest root-free ideal. -/
theorem gaussianOmnific_greatest_root_free_ideal :
    IsGreatest {J : Ideal GaussianOmnificInteger.{u} |
      ∀ t : GaussianOmnificInteger.{u} ⧸ J, value t ≠ 0}
        (RingHom.ker gaussianOmnificConstantCoeff.{u}) :=
  greatest_root_free_ideal (RingHom.ker gaussianOmnificConstantCoeff.{u}) gaussianOmnific_detector_iff

/-- The universal ring formula also defines the Gaussian purely infinite ideal. -/
theorem gaussianOmnific_purelyInfinite_iff_universal (a : GaussianOmnificInteger.{u}) :
    a ∈ RingHom.ker gaussianOmnificConstantCoeff.{u} ↔
      ∀ s t : GaussianOmnificInteger.{u}, a * s ≠ value t :=
  mem_iff_universal (RingHom.ker gaussianOmnificConstantCoeff.{u}) gaussianOmnific_detector_iff a

/-- Universal nonexistence of a certificate for a difference detects equal Gaussian constants. -/
theorem gaussianOmnific_constant_eq_iff_universal (a b : GaussianOmnificInteger.{u}) :
    gaussianOmnificConstantCoeff.{u} a = gaussianOmnificConstantCoeff.{u} b ↔
      ∀ s t : GaussianOmnificInteger.{u}, (a - b) * s ≠ value t :=
  constant_eq_iff_universal gaussianOmnificConstantCoeff.{u} gaussianOmnific_detector_iff a b

end Surcomplex
end
end Surreal
