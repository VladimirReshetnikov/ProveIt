import IPRADerivations.Analysis.Logarithm.RightHalfPlane.NearOne.GaussianRightHalfPlaneLogarithmOffset
import IPRADerivations.Analysis.Logarithm.RightHalfPlane.NearOne.GaussianRightHalfPlaneLogarithmLocalBound
import IPRADerivations.Analysis.Exponential.RightHalfPlane.GaussianRightHalfPlaneLogarithmExponential
import IPRADerivations.Analysis.Exponential.Names.LocalEstimates.GaussianNamedExponentialLocalUniqueness
import IPRADerivations.Analysis.Logarithm.Local.GaussianLocalLogarithmQuarterBound
import IPRADerivations.Analysis.Logarithm.Local.GaussianLocalLogarithmExponentialIdentity

/-!
# Identify the canonical logarithm with Mercator near one

Both programs exponentiate to the same signed input. Their late
difference samples lie inside the local uniqueness radius.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmMercator

open_ipra
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianFastValueCut (exponent)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFiniteApproximantName (exponential_input)
open GaussianLocalLogarithmName (pointF)
open GaussianNameArithmetic (add_at add_canonical recode_congr)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNameRingLaws (negativeF negativeData)
open GaussianNamedExponentialLocalUniqueness (lateSmall)
open GaussianRationalHorner (ofGaussian qadd_canonical canonical positive_product)
open GaussianRationalMetric (bounded qnegative)
open GaussianRationalReciprocal (bounded_sum bound_congr)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRightHalfPlaneLogarithmOffset (offset source)
open GaussianFiniteLogarithmCompositionTail (linearValue)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianRightHalfPlaneLogarithm.nameF
local notation "dL" => GaussianRightHalfPlaneLogarithm.data
local notation "dM" => GaussianLocalLogarithmName.data
local notation "F" => GaussianNamedDifference.nameF
local notation "X" => GaussianNamedDifference.data
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ED" => GaussianRadiusExponentialName.data
local notation "EU" => GaussianUnitDiskExponentialName.nameF
local notation "MC" => GaussianFiniteLogarithmCompositionName.constantF

private theorem late_difference_at (A B D neg R p : PTm n)
    (hs : Γ ⊢[PRAAx] source A B D neg R) (hp : Γ ⊢[PRAAx] le (num 8) p) :
    Γ ⊢[PRAAx]
      canonical (ap2 (F L pointF) p (X (dL A B D neg) (dM (offset A B D neg) R D))) ⋏
      bounded (ap2 (F L pointF) p (X (dL A B D neg) (dM (offset A B D neg) R D))) (num 3) (num 4) := by
  let z := offset A B D neg
  let x := dL A B D neg
  let y := dM z R D
  let t := exponent two p
  let u := exponent (one+one) t
  let a := ap2 L t x
  let b := ap2 pointF u y
  let v := qnegative b
  have ht : Γ ⊢[PRAAx] le p t := le_add_right _ _
  have hu : Γ ⊢[PRAAx] le t u := le_add_right _ _
  have h₁ : Γ ⊢[PRAAx] bounded a one two :=
    GaussianRightHalfPlaneLogarithmLocalBound.sample_bound t A B D neg
      (GaussianRightHalfPlaneLogarithmOffset.box A B D neg R hs) hs.andE₁.andE₁.andE₂ (le_trans hp ht)
  have atLeastFour : Γ ⊢[PRAAx] le (num 4) u :=
    le_trans (by ipra_le 4) (le_trans hp (le_trans ht hu))
  have h₂ : Γ ⊢[PRAAx] bounded b one (num 4) :=
    GaussianLocalLogarithmQuarterBound.quarter_at u z R D
      (GaussianRightHalfPlaneLogarithmOffset.local_source A B D neg R hs) hs.andE₂.andE₂ atLeastFour
  have h4 : Γ ⊢[PRAAx] le one (num 4) := by ipra_le 3
  have h2 : Γ ⊢[PRAAx] le one two := by ipra_le 1
  have nBound := GaussianRationalReciprocal.bounded_negative b one (num 4) h4 h₂
  have plus := bounded_sum a v one two one (num 4) h2 h4 h₁ nBound
  have exactSample := (add_at (Γ := Γ) L (negativeF pointF) x (negativeData y) p).eqTrans
    ((recode_congr (qadd_congr (.eqRefl a)
      (GaussianRealNameExponentialUnitReflection.negative_sample_at pointF t y))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (qadd_canonical _ _)))
  have small := bounded_radius_mono (GaussianRationalHorner.qadd a v)
    (one * num 4 + one * two) (two * num 4) (num 3) (num 4)
    (positive_product _ _ h2 h4) h4 (by ipra_le 0) plus
  have bound := bound_congr exactSample.eqSymm (.eqRefl (num 3)) (.eqRefl (num 4)) small
  exact .andI (add_canonical L (negativeF pointF) x (negativeData y) p) bound

theorem late_difference (A B D neg R : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R) :
    Γ ⊢[PRAAx] lateSmall (F L pointF) (X (dL A B D neg) (dM (offset A B D neg) R D)) (num 8) := by
  refine .allI (.impI ?_)
  let sh (a : PTm n) := Syn.shift a
  let Δ := le (num 8) (var 0) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh A) (sh B) (sh D) (sh neg) (sh R) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.wk
  simpa only [lateSmall,Syn.shift,GaussianNamedDifference.subst_data,GaussianRightHalfPlaneLogarithm.subst_data,
    GaussianLocalLogarithmName.subst_data,GaussianRightHalfPlaneLogarithmOffset.subst_offset,
    LeanProofs.IPRA.PTm.subst_num,sh,Δ] using
    late_difference_at (sh A) (sh B) (sh D) (sh neg) (sh R) (var 0) hs (Prf.hyp0 : Δ ⊢[PRAAx] le (num 8) (var 0))

private theorem composition_constant_cross (w v : PTm n) (h : Γ ⊢[PRAAx] linearValue w ≐ v) :
    Γ ⊢[PRAAx] crossEquivalent GaussianFiniteLogarithmCompositionName.constantF constantF w v := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (GaussianFiniteLogarithmCompositionName.constant_regular w) (constant_regular v)
  refine .allI ?_
  have h' : Γ.map Fm.shift ⊢[PRAAx] linearValue (Syn.shift w) ≐ Syn.shift v := by
    simpa [Fm.shift,Syn.shift,linearValue] using h.shift
  exact (GaussianFiniteLogarithmCompositionName.constant_at (var 0) (Syn.shift w)).eqTrans
    (h'.eqTrans (constant_at (var 0) (Syn.shift v)).eqSymm)

theorem coincidence (A B D neg R : PTm n) (hs : Γ ⊢[PRAAx] source A B D neg R) :
    Γ ⊢[PRAAx] crossEquivalent L pointF (dL A B D neg) (dM (offset A B D neg) R D) := by
  let z := offset A B D neg
  let x := dL A B D neg
  let y := dM z R D
  let T := GaussianNameBounds.U L x
  have l := GaussianRightHalfPlaneLogarithm.regular A B D neg hs.andE₁
  have h := GaussianRightHalfPlaneLogarithmOffset.local_source A B D neg R hs
  have m := GaussianLocalLogarithmName.original_exponential_input z R D h
  have lm := GaussianRightHalfPlaneLogarithmExponential.recovery A B D neg hs.andE₁
  have shift := GaussianLocalLogarithmExponentialIdentity.source_cross z R D h
  have target := composition_constant_cross (ofGaussian z D) (GaussianLogGammaEulerHead.argument A B D neg)
    (GaussianRightHalfPlaneLogarithmOffset.linear_value A B D neg hs.andE₁.andE₂)
  let a := GaussianLogGammaEulerHead.argument A B D neg
  have unitRecovery := cross_trans (EU pointF) MC constantF y (ofGaussian z D) a shift target
  have recovered := cross_trans (E pointF) (EU pointF) constantF (ED one y) y a
    (cross_symm (EU pointF) (E pointF) y (ED one y)
      (GaussianExponentialRadiusIndependence.original_unit_cross pointF y m)) unitRecovery
  have same := cross_trans (E L) constantF (E pointF) (ED T x) a (ED one y) lm
    (cross_symm (E pointF) constantF (ED one y) a recovered)
  exact GaussianNamedExponentialLocalUniqueness.local_injective L pointF T one x y (num 8)
    (exponential_input L x l) (GaussianExponentialRadiusIndependence.radius_one_input pointF y m)
    (late_difference A B D neg R hs) same

theorem actual_right_half_plane_logarithm_equals_Mercator_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
        crossEquivalent L pointF (dL (var 0) (var 1) (var 2) (var 3))
          (dM (offset (var 0) (var 1) (var 2) (var 3)) (var 4) (var 2))) :=
  closeUniv 5 (.impI (coincidence _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmMercator
