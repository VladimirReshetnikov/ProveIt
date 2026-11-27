import IPRADerivations.Analysis.Logarithm.RightHalfPlane.GaussianRightHalfPlaneLogarithmRelativeStep
import IPRADerivations.Analysis.Exponential.RightHalfPlane.GaussianRightHalfPlaneLogarithmExponential
import IPRADerivations.Analysis.Logarithm.Local.GaussianLocalLogarithmExponentialIdentity
import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.Folded.GaussianGammaFoldedApproximantBalance

/-!
# Recover the shifted argument from the relative logarithm program

The actual canonical base logarithm plus the relative Mercator name
exponentiates to the exact later rational argument.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmRelativeExponential

open_ipra
open GaussianFiniteLogarithmCompositionTail (linearValue)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianLocalLogarithmName (pointF)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianRationalHorner (ofGaussian qmul)
open GaussianRightHalfPlaneLogarithm (source)
open GaussianRightHalfPlaneLogarithmRelativeStep (numerator denominator radius relative)
open GaussianRootAlgebra (sub)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => GaussianRightHalfPlaneLogarithm.nameF
local notation "P" => GaussianRightHalfPlaneLogarithm.data
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ED" => GaussianRadiusExponentialName.data
local notation "EU" => GaussianUnitDiskExponentialName.nameF
local notation "MC" => GaussianFiniteLogarithmCompositionName.constantF

def correctionData (A B neg a b sign H : PTm n) : PTm n :=
  GaussianLocalLogarithmName.data (numerator (native A B neg) (native a b sign))
    (radius A B H) (denominator (native A B neg))

def correctedF : PR 2 := addF G pointF
def correctedData (A B neg a b sign D H : PTm n) : PTm n :=
  addData (P A B D neg) (correctionData A B neg a b sign H)

ipra_subst correctionData
ipra_subst correctedData

private theorem composition_cross (w : PTm n) : Γ ⊢[PRAAx] crossEquivalent MC constantF w (linearValue w) := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (GaussianFiniteLogarithmCompositionName.constant_regular w) (constant_regular _)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,GaussianFiniteLogarithmCompositionName.constant,GaussianFiniteLogarithmCompositionTail.subst_linearValue] using
    (GaussianFiniteLogarithmCompositionName.constant_at (Γ := Γ.map Fm.shift) (var 0) (Syn.shift w)).eqTrans
      (constant_at (var 0) (linearValue (Syn.shift w))).eqSymm

theorem recovery (A B neg a b sign D H : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg)
    (hw : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (sub (native a b sign) (native A B neg)) H)
    (hh : Γ ⊢[PRAAx] le (num 4*H) A) :
    Γ ⊢[PRAAx] crossEquivalent (E correctedF) constantF
      (exponentialInputData correctedF (correctedData A B neg a b sign D H))
      (GaussianLogGammaEulerHead.argument a b D sign) := by
  let u := native A B neg
  let v := native a b sign
  let z := numerator u v
  let N := denominator u
  let R := radius A B H
  let x := P A B D neg
  let y := correctionData A B neg a b sign H
  let xy := correctedData A B neg a b sign D H
  let left := GaussianLogGammaEulerHead.argument A B D neg
  let right := linearValue (relative u v)
  let e := exponentialInputData G x
  let f := ED one y
  have ml := GaussianRightHalfPlaneLogarithmRelativeStep.mercator_source A B neg v H h.andE₁ hw hh
  have hi := GaussianLocalLogarithmName.original_exponential_input z R N ml
  have hx := exponential_input G x (GaussianRightHalfPlaneLogarithm.regular A B D neg h)
  have hy := GaussianExponentialRadiusIndependence.radius_one_input pointF y hi
  have hr := add_fast G pointF x y hx.andE₁ hy.andE₁
  have hz := exponential_input correctedF xy hr
  have identify := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent G pointF correctedF
    (GaussianNameBounds.U G x) one (GaussianNameBounds.U correctedF xy) x y xy hx hy hz (cross_refl _ _ hr)
  have unitRecovery := cross_trans (EU pointF) MC constantF y (relative u v) right
    (GaussianLocalLogarithmExponentialIdentity.source_cross z R N ml) (composition_cross (relative u v))
  have original := GaussianExponentialRadiusIndependence.original_unit_cross pointF y hi
  have rightRecovery := cross_trans (E pointF) (EU pointF) constantF f y right
    (cross_symm (EU pointF) (E pointF) y f original) unitRecovery
  have replace := multiply_cross (E G) constantF (E pointF) constantF e left f right
    (GaussianRadiusExponentialName.name_regular _ _ _ hx) (constant_regular left)
    (GaussianRadiusExponentialName.name_regular _ _ _ hy) (constant_regular right)
    (GaussianRightHalfPlaneLogarithmExponential.recovery A B D neg h) rightRecovery
  let w := GaussianLogGammaEulerHead.argument a b D sign
  have wEq : Γ ⊢[PRAAx] qmul left right ≐ w :=
    GaussianRightHalfPlaneLogarithmRelativeStep.factor_binding u v D h.andE₂
      (GaussianRightHalfPlaneLogarithmRelativeStep.denominator_positive A B neg h.andE₁)
  have combine := cross_trans (multiplyF constantF constantF) constantF constantF
    (multiplyData constantF constantF left right) (qmul left right) w
    (GaussianGammaWeierstrassApproximant.constant_product_cross left right)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ wEq)
  exact cross_trans (E correctedF) (multiplyF (E G) (E pointF)) constantF
    (exponentialInputData correctedF xy) (multiplyData (E G) (E pointF) e f) w
    (cross_symm _ _ _ _ identify) (cross_trans _ _ _ _ _ _ replace combine)

theorem same_exponential (A B neg a b sign D H : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (ht : Γ ⊢[PRAAx] source a D sign)
    (hw : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (sub (native a b sign) (native A B neg)) H)
    (hh : Γ ⊢[PRAAx] le (num 4*H) A) :
    Γ ⊢[PRAAx] crossEquivalent (E correctedF) (E G)
      (exponentialInputData correctedF (correctedData A B neg a b sign D H))
      (exponentialInputData G (P a b D sign)) :=
  cross_trans _ constantF _ _ (GaussianLogGammaEulerHead.argument a b D sign) _
    (recovery A B neg a b sign D H h hw hh)
    (cross_symm _ _ _ _ (GaussianRightHalfPlaneLogarithmExponential.recovery a b D sign ht))

theorem actual_relative_logarithm_exponential_recovers_shift_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      ((source (var 0) (var 6) (var 2) ⋏
        (ComplexLogarithmRemainder.bounded (sub (native (var 3) (var 4) (var 5)) (native (var 0) (var 1) (var 2))) (var 7) ⋏
          le (num 4*var 7) (var 0))) ⟶
        crossEquivalent (E correctedF) constantF
          (exponentialInputData correctedF (correctedData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))
          (GaussianLogGammaEulerHead.argument (var 3) (var 4) (var 6) (var 5))) :=
  closeUniv 8 (.impI (recovery _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmRelativeExponential
