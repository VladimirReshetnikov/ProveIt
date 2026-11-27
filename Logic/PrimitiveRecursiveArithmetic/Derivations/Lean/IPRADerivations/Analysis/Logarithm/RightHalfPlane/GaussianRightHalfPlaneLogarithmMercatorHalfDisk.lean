import IPRADerivations.Analysis.Exponential.Names.LocalEstimates.GaussianNamedExponentialQuarterUniqueness
import IPRADerivations.Analysis.Logarithm.RightHalfPlane.GaussianRightHalfPlaneLogarithmMercator

/-!
# Canonical and Mercator logarithms on the half disk

Both actual exponentials recover the original signed Gaussian fraction.
The Mercator samples stay in the unit disk. A radius-two late bound for
the canonical samples thus suffices for the radius-three uniqueness law.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmMercatorHalfDisk

open_ipra
open GaussianFastValueCut (exponent)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFiniteApproximantName (exponential_input)
open GaussianLocalLogarithmName (pointF)
open GaussianNameArithmetic (add_at recode_congr)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNameRingLaws (negativeF negativeData)
open GaussianNamedExponentialQuarterUniqueness (lateRadius)
open GaussianRationalHorner (ofGaussian qadd_canonical)
open GaussianRationalMetric (bounded qnegative)
open GaussianRationalReciprocal (bounded_sum bounded_negative bound_congr)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRightHalfPlaneLogarithmOffset (offset)
open GaussianFiniteLogarithmCompositionTail (linearValue)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianRightHalfPlaneLogarithm.nameF
local notation "ld" => GaussianRightHalfPlaneLogarithm.data
local notation "md" => GaussianLocalLogarithmName.data
local notation "F" => GaussianNamedDifference.nameF
local notation "X" => GaussianNamedDifference.data
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => GaussianRadiusExponentialName.data

def source (A B D neg R : PTm n) : Fm PTm n :=
  GaussianRightHalfPlaneLogarithm.source A D neg ⋏
    (ComplexLogarithmRemainder.bounded (offset A B D neg) R ⋏ le (two*R) D)

def lateLogBound (A B D neg C : PTm n) : Fm PTm n := .all
  (le (Syn.shift C) (var 0) ⟶
    bounded (ap2 L (var 0) (ld (Syn.shift A) (Syn.shift B) (Syn.shift D) (Syn.shift neg))) two one)

ipra_subst source [GaussianRightHalfPlaneLogarithm.source, GaussianRightHalfPlaneArgument.source, ComplexLogarithmRemainder.bounded, two, one]

ipra_subst lateLogBound [Syn.subst_shift, Syn.shift_subst, two, one]

theorem local_source (A B D neg R : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R) :
    Γ ⊢[PRAAx] GaussianLocalLogarithmName.source (offset A B D neg) R D :=
  .andI h.andE₁.andE₂ h.andE₂

private theorem late_at (A B D neg C p : PTm n) (h : Γ ⊢[PRAAx] lateLogBound A B D neg C)
    (hp : Γ ⊢[PRAAx] le C p) : Γ ⊢[PRAAx] bounded (ap2 L p (ld A B D neg)) two one :=
  .impE (by simpa [lateLogBound,two,one] using h.allE p) hp

private theorem late_difference_at (A B D neg R C p : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R) (hl : Γ ⊢[PRAAx] lateLogBound A B D neg C)
    (hp : Γ ⊢[PRAAx] le C p) :
    Γ ⊢[PRAAx] bounded (ap2 (F L pointF) p (X (ld A B D neg) (md (offset A B D neg) R D)))
      (LeanProofs.IPRA.PTm.num 3) one := by
  let z := offset A B D neg
  let x := ld A B D neg
  let y := md z R D
  let t := exponent two p
  let u := exponent (one+one) t
  let a := ap2 L t x
  let b := ap2 pointF u y
  let v := qnegative b
  have ht : Γ ⊢[PRAAx] le p t := le_add_right _ _
  have left := late_at A B D neg C t hl (le_trans hp ht)
  have right := GaussianRadiusExponentialName.bounded_samples_at pointF one y u
    (GaussianExponentialRadiusIndependence.radius_one_input pointF y
      (GaussianLocalLogarithmName.original_exponential_input z R D (local_source A B D neg R h))).andE₂
  have both := bounded_sum a v two one one one (le_refl one) (le_refl one) left
    (bounded_negative b one one (le_refl one) right)
  have exactSample := (add_at (Γ := Γ) L (negativeF pointF) x (negativeData y) p).eqTrans
    ((recode_congr (qadd_congr (.eqRefl a)
      (GaussianRealNameExponentialUnitReflection.negative_sample_at pointF t y))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (qadd_canonical _ _)))
  exact bound_congr exactSample.eqSymm (by ipra_ring) (one_mul _) both

theorem late_difference (A B D neg R C : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R)
    (hl : Γ ⊢[PRAAx] lateLogBound A B D neg C) :
    Γ ⊢[PRAAx] lateRadius (F L pointF) (X (ld A B D neg) (md (offset A B D neg) R D)) C := by
  refine .allI (.impI ?_)
  let sh (a : PTm n) := Syn.shift a
  let Δ := le (sh C) (var 0) :: Γ.map Fm.shift
  have h' : Δ ⊢[PRAAx] source (sh A) (sh B) (sh D) (sh neg) (sh R) := by
    simpa only [Fm.shift,Syn.shift,subst_source,sh,Δ] using h.shift.wk
  have l' : Δ ⊢[PRAAx] lateLogBound (sh A) (sh B) (sh D) (sh neg) (sh C) := by
    simpa only [Fm.shift,Syn.shift,subst_lateLogBound,sh,Δ] using hl.shift.wk
  simpa only [lateRadius,Syn.shift,GaussianNamedDifference.subst_data,GaussianRightHalfPlaneLogarithm.subst_data,
    GaussianLocalLogarithmName.subst_data,GaussianRightHalfPlaneLogarithmOffset.subst_offset,sh,Δ] using
    late_difference_at (sh A) (sh B) (sh D) (sh neg) (sh R) (sh C) (var 0) h' l' Prf.hyp0

private theorem composition_constant_cross (w v : PTm n) (h : Γ ⊢[PRAAx] linearValue w ≐ v) :
    Γ ⊢[PRAAx] crossEquivalent GaussianFiniteLogarithmCompositionName.constantF constantF w v := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (GaussianFiniteLogarithmCompositionName.constant_regular w) (constant_regular v)
  refine .allI ?_
  have h' : Γ.map Fm.shift ⊢[PRAAx] linearValue (Syn.shift w) ≐ Syn.shift v := by
    simpa [Fm.shift,Syn.shift,linearValue] using h.shift
  exact (GaussianFiniteLogarithmCompositionName.constant_at (var 0) (Syn.shift w)).eqTrans
    (h'.eqTrans (constant_at (var 0) (Syn.shift v)).eqSymm)

theorem coincidence (A B D neg R C : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R)
    (hl : Γ ⊢[PRAAx] lateLogBound A B D neg C) :
    Γ ⊢[PRAAx] crossEquivalent L pointF (ld A B D neg) (md (offset A B D neg) R D) := by
  let z := offset A B D neg
  let x := ld A B D neg
  let y := md z R D
  let a := GaussianLogGammaEulerHead.argument A B D neg
  let T := GaussianNameBounds.U L x
  have l := GaussianRightHalfPlaneLogarithm.regular A B D neg h.andE₁
  have mercatorSource := local_source A B D neg R h
  have m := GaussianLocalLogarithmName.original_exponential_input z R D mercatorSource
  have shift := GaussianLocalLogarithmExponentialIdentity.source_cross z R D mercatorSource
  have target := composition_constant_cross (ofGaussian z D) a
    (GaussianRightHalfPlaneLogarithmOffset.linear_value A B D neg h.andE₁.andE₂)
  have recovered := cross_trans _ _ _ _ _ _
    (cross_symm _ _ _ _ (GaussianExponentialRadiusIndependence.original_unit_cross pointF y m))
      (cross_trans _ _ _ _ _ _ shift target)
  have same := cross_trans (E L) constantF (E pointF) (ed T x) a (ed one y)
    (GaussianRightHalfPlaneLogarithmExponential.recovery A B D neg h.andE₁)
    (cross_symm _ _ _ _ recovered)
  exact GaussianNamedExponentialQuarterUniqueness.injective L pointF T one x y C
    (exponential_input L x l) (GaussianExponentialRadiusIndependence.radius_one_input pointF y m)
    (late_difference A B D neg R C h hl) same

theorem actual_canonical_Mercator_half_disk_when_bounded_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ lateLogBound (var 0) (var 1) (var 2) (var 3) (var 5) ⟶
        crossEquivalent L pointF (ld (var 0) (var 1) (var 2) (var 3))
          (md (offset (var 0) (var 1) (var 2) (var 3)) (var 4) (var 2))) :=
  closeUniv 6 (.impI (.impI (coincidence _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmMercatorHalfDisk
