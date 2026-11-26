import IPRADerivations.Analysis.Logarithm.RightHalfPlane.GaussianRightHalfPlaneLogarithmIncrementBound
import IPRADerivations.Analysis.Names.Differences.GaussianNamedStrictOrderDifference
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotientProperness

/-!
# Actual canonical logarithm increments and their linear term

Compare the two original exponentials and use the bound on their
logarithms to select the same branch. The difference of the canonical
logarithms is then the actual relative Mercator name.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmIncrement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaFiniteApproximantName (exponential_input)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianLocalLogarithmName (pointF)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans cross_at)
open GaussianNameRingLaws (add_commutative)
open GaussianNamedDifferenceQuotientProperness (difference_proper)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRightHalfPlaneLogarithmIncrementBound (input shift_input)
open GaussianRightHalfPlaneLogarithmRelativeExponential (correctedF correctedData correctionData)
open GaussianRightHalfPlaneLogarithmRelativeStep (numerator denominator radius relative)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => GaussianRightHalfPlaneLogarithm.nameF
local notation "P" => GaussianRightHalfPlaneLogarithm.data
local notation "F" => GaussianNamedDifference.nameF
local notation "X" => GaussianNamedDifference.data

private theorem smallness (A B neg a b sign D H J M : PTm n)
    (h : Γ ⊢[PRAAx] input A B neg a b sign D H J M) : Γ ⊢[PRAAx] le (num 4*H) A :=
  le_trans (le_trans (le_of_eq_add (d := num 124*H) (by ipra_ring)) h.andE₂.andE₂.andE₂.andE₂.andE₁)
    h.andE₂.andE₂.andE₁

theorem increment_relative (A B neg a b sign D H J M : PTm n)
    (h : Γ ⊢[PRAAx] input A B neg a b sign D H J M) :
    Γ ⊢[PRAAx] crossEquivalent (F G G) pointF (X (P a b D sign) (P A B D neg))
      (correctionData A B neg a b sign H) := by
  let u := native A B neg
  let v := native a b sign
  let x := P A B D neg
  let y := P a b D sign
  let z := correctionData A B neg a b sign H
  let c := correctedData A B neg a b sign D H
  have hA := h.andE₁.andE₁
  have ha := h.andE₁.andE₂.andE₁
  have step := h.andE₁.andE₂.andE₂.andE₁
  have small := smallness A B neg a b sign D H J M h
  have localSrc := GaussianRightHalfPlaneLogarithmRelativeStep.mercator_source A B neg v H hA.andE₁ step small
  have hx := GaussianRightHalfPlaneLogarithm.regular A B D neg hA
  have hy := GaussianRightHalfPlaneLogarithm.regular a b D sign ha
  have hz := GaussianLocalLogarithmName.name_regular (numerator u v) (radius A B H) (denominator u) localSrc
  have hc := add_fast G pointF x z hx hz
  have equal := GaussianNamedExponentialLocalUniqueness.local_injective correctedF G
    (GaussianNameBounds.U correctedF c) (GaussianNameBounds.U G y) c y (num 288)
    (exponential_input correctedF c hc) (exponential_input G y hy)
    (GaussianRightHalfPlaneLogarithmIncrementBound.late_difference A B neg a b sign D H J M h)
    (GaussianRightHalfPlaneLogarithmRelativeExponential.same_exponential A B neg a b sign D H hA ha step small)
  have moved := cross_trans G correctedF (addF pointF G) y c (addData z x)
    (cross_symm _ _ _ _ equal) (add_commutative G pointF x z hx hz)
  exact cross_trans (F G G) (F (addF pointF G) G) pointF (X y x) (X (addData z x) x) z
    (difference_proper G (addF pointF G) G G y (addData z x) x x hy (add_fast _ _ _ _ hz hx) hx hx moved
      (cross_refl _ _ hx)) (GaussianNamedStrictOrderDifference.sum_sub_right pointF G z x hz hx)

theorem sample_error (p A B neg a b sign D H J M : PTm n)
    (h : Γ ⊢[PRAAx] input A B neg a b sign D H J M) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (F G G) p (X (P a b D sign) (P A B D neg)))
      (relative (native A B neg) (native a b sign)) (num 4*H*H*unit p+num 3*(A*A)) (A*A*unit p) := by
  let u := unit p
  let d := A*A*u
  let x := X (P a b D sign) (P A B D neg)
  let y := correctionData A B neg a b sign H
  let z := relative (native A B neg) (native a b sign)
  have hu := unit_positive (Γ := Γ) p
  have hU := positive_product u u hu hu
  have hA := h.andE₁.andE₁.andE₁.andE₁
  have hD := positive_product _ _ (positive_product _ _ hA hA) hu
  have eq := cross_at (F G G) pointF x y p p (increment_relative A B neg a b sign D H J M h)
  have q := GaussianRightHalfPlaneLogarithmRelativeStep.quadratic_error p A B neg (native a b sign) H
    h.andE₁.andE₁.andE₁ h.andE₁.andE₂.andE₂.andE₁ (smallness A B neg a b sign D H J M h)
  have both := GaussianRationalPanelTailDistance.triangle (ap2 (F G G) p x) (ap2 pointF p y) z
    (u+u) (u*u) (num 4*H*H*u+A*A) d hU hD eq q
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU hD) hD
    (le_of_eq_add (d := zero) (by dsimp only [d]; ipra_ring)) both

theorem shifted_sample_error (p i A B neg a b sign D H J M : PTm n)
    (h : Γ ⊢[PRAAx] input A B neg a b sign D H J M) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (F G G) p (X (P (a+i*D) b D sign) (P (A+i*D) B D neg)))
      (relative (native (A+i*D) B neg) (native (a+i*D) b sign))
      (num 4*H*H*unit p+num 3*((A+i*D)*(A+i*D))) ((A+i*D)*(A+i*D)*unit p) :=
  sample_error p _ B neg _ b sign D H J _ (shift_input i A B neg a b sign D H J M h)

theorem actual_right_half_plane_logarithm_relative_increment_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
        crossEquivalent (F G G) pointF
          (X (P (var 3) (var 4) (var 6) (var 5)) (P (var 0) (var 1) (var 6) (var 2)))
          (correctionData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7))) :=
  closeUniv 10 (.impI (increment_relative _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmIncrement
