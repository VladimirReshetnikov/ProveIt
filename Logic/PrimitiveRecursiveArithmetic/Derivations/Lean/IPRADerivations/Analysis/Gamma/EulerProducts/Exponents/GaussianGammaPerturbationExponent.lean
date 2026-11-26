import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.GaussianGammaEulerCorrectionDisk
import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.GaussianGammaExactTailDisk

/-!
# The actual perturbing exponent for the Euler convergence rate

Subtract the original C6 tail from the original C2 correction. Their
actual observation envelopes and two original name operations give
radius `(R²+R)/N` plus explicit dyadic slack. Adding the tail back
gives the original correction at independent observation precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPerturbationExponent

open_ipra
open GaussianNameArithmetic (addF addData)
open GaussianNameRingLaws (negativeF negativeData negative_fast negative_sample_error add_sample_error
  three sum_right_error equivalent_of_envelope)
open GaussianRationalHorner (qadd qzero positive_product)
open GaussianRationalMetric (qsub qnegative qnegative_canonical bounded distanceBounded)
open GaussianRationalReciprocal (bounded_negative bound_congr)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianRationalSyntheticDivision (qadd_congr qzero_add)
open GaussianGammaFoldedExponentBalance (correctionF correctionData correction_fast)
open GaussianGammaCanonicalTailName (pointF point source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (rawEnvelope)
open GaussianNameEquivalence (crossEquivalent)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def tailData (z R B N : PTm n) : PTm n := GaussianGammaCanonicalTailName.data z R B N
def deltaF : PR 2 := addF correctionF (negativeF pointF)
def deltaData (z R B N : PTm n) : PTm n :=
  addData (correctionData z B N) (negativeData (tailData z R B N))
def sumF : PR 2 := addF pointF deltaF
def sumData (z R B N : PTm n) : PTm n := addData (tailData z R B N) (deltaData z R B N)
def numerator (R : PTm n) : PTm n := R*R+R
def slack (z R B N : PTm n) : PTm n := GaussianGammaEulerCorrectionDisk.slack z R B N+num 7

ipra_subst tailData
ipra_subst deltaData
ipra_subst sumData
ipra_subst numerator
ipra_subst slack

theorem correction_source (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] GaussianGammaEulerCorrectionDisk.source z R B N :=
  .andI h.andE₂.andE₁ (.andI h.andE₁ h.andE₂.andE₂.andE₁)

theorem delta_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] pointCN deltaF (deltaData z R B N) :=
  GaussianNameArithmetic.add_fast _ _ _ _ (correction_fast z B N h.andE₂.andE₁)
    (negative_fast _ _ (GaussianGammaCanonicalTailName.name_regular z R B N h))

def core (p z R B N : PTm n) : PTm n :=
  qsub (ap2 correctionF p (correctionData z B N)) (point p z R B N)

theorem core_distance (p z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 deltaF p (deltaData z R B N)) (core p z R B N) (num 6) (unit p) := by
  let X := correctionData z B N
  let Y := tailData z R B N
  let C := ap2 correctionF p X
  let T := point p z R B N
  have ht := GaussianGammaCanonicalTailName.name_regular z R B N h
  have e := negative_sample_error pointF Y p ht
  have e' : Γ ⊢[PRAAx] distanceBounded (ap2 (negativeF pointF) p (negativeData Y)) (qnegative T) three (unit p) :=
    distance_congr (.eqRefl _) (qzero_add _ (qnegative_canonical T)) (.eqRefl _) (.eqRefl _) e
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p)
      (add_sample_error correctionF (negativeF pointF) X (negativeData Y) p
        (correction_fast z B N h.andE₂.andE₁) (negative_fast _ _ ht))
      (sum_right_error C _ _ _ _ (unit_positive p) e'))

theorem core_bound (p z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] bounded (core p z R B N)
      (numerator R*unit p+(GaussianGammaEulerCorrectionDisk.slack z R B N+one)*N) (N*unit p) := by
  let W := N*unit p
  have pos := positive_product _ _ h.andE₂.andE₁ (unit_positive p)
  have c := GaussianGammaEulerCorrectionDisk.correction_bound p z R B N (correction_source z R B N h)
  have t := GaussianGammaExactTailDisk.original_point_envelope p z R B N h
  exact bound_congr (.eqRefl _) (by unfold numerator; ipra_ring) (.eqRefl _)
    (GaussianRationalPowerDifference.bounded_sum_same _ _ _ _ W pos c (bounded_negative _ _ _ pos t))

theorem delta_bound (p z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] bounded (ap2 deltaF p (deltaData z R B N))
      (numerator R*unit p+slack z R B N*N) (N*unit p) := by
  let x := ap2 deltaF p (deltaData z R B N)
  let c := core p z R B N
  let D := N*unit p
  have pos := positive_product _ _ h.andE₂.andE₁ (unit_positive p)
  have b := core_bound p z R B N h
  have e : Γ ⊢[PRAAx] bounded (qsub x c) (num 6*N) D :=
    GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (unit_positive p) pos
      (le_of_eq_add (d := zero) (by unfold D; ipra_ring)) (core_distance p z R B N h)
  have hc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical x :=
    GaussianNameArithmetic.add_canonical _ _ _ _ p
  exact bound_congr (GaussianRationalLinearProduct.add_sub_right c x hc) (by unfold slack; ipra_ring)
    (.eqRefl _) (GaussianRationalPowerDifference.bounded_sum_same _ _ _ _ _ pos b e)

theorem delta_envelope (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] rawEnvelope deltaF (deltaData z R B N) (numerator R) N (slack z R B N) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) := by
    simpa only [Fm.shift, Syn.shift, GaussianGammaCanonicalTailName.subst_source] using h.shift
  simpa only [rawEnvelope, unit, Syn.shift, subst_deltaData, subst_numerator, subst_slack] using
    delta_bound (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) hs

theorem cancel_at (p z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 sumF p (sumData z R B N))
      (ap2 correctionF p (correctionData z B N)) (num 9) (unit p) := by
  let T := point p z R B N
  let C := ap2 correctionF p (correctionData z B N)
  have c : Γ ⊢[PRAAx] GaussianRationalHorner.canonical C := GaussianNameArithmetic.multiply_canonical _ _ _ _ p
  have e : Γ ⊢[PRAAx] qadd T (core p z R B N) ≐ C := GaussianRationalLinearProduct.add_sub_right T C c
  exact distance_congr (.eqRefl _) e (by unfold three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p)
      (add_sample_error pointF deltaF (tailData z R B N) (deltaData z R B N) p
        (GaussianGammaCanonicalTailName.name_regular z R B N h) (delta_regular z R B N h))
      (sum_right_error T _ _ _ _ (unit_positive p) (core_distance p z R B N h)))

theorem tail_plus_delta (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] crossEquivalent sumF correctionF (sumData z R B N) (correctionData z B N) := by
  apply equivalent_of_envelope sumF correctionF (sumData z R B N) (correctionData z B N) (num 9)
    (GaussianNameArithmetic.add_fast _ _ _ _ (GaussianGammaCanonicalTailName.name_regular z R B N h)
      (delta_regular z R B N h)) (correction_fast z B N h.andE₂.andE₁)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) := by
    simpa only [Fm.shift, Syn.shift, GaussianGammaCanonicalTailName.subst_source] using h.shift
  change Γ.map Fm.shift ⊢[PRAAx] distanceBounded (ap2 sumF (var 0) (Syn.shift (sumData z R B N)))
    (ap2 correctionF (var 0) (Syn.shift (correctionData z B N))) (Syn.shift (num 9)) (unit (var 0))
  have s₀ : Syn.shift (sumData z R B N) = sumData (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) :=
    subst_sumData _ _ _ _ _
  have s₁ : Syn.shift (correctionData z B N) = correctionData (Syn.shift z) (Syn.shift B) (Syn.shift N) :=
    GaussianGammaFoldedExponentBalance.subst_correctionData _ _ _ _
  have s₉ : Syn.shift (num 9 : PTm n) = num 9 := by simp [Syn.shift]
  rw [s₀, s₁, s₉]
  exact cancel_at (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) hs

theorem original_C10_perturbation_exponent_envelope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶
      rawEnvelope deltaF (deltaData (var 0) (var 1) (var 2) (var 3)) (numerator (var 1)) (var 3)
        (slack (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (delta_envelope _ _ _ _ Prf.hyp0))

theorem original_C10_perturbation_exponent_reconstruction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶
      crossEquivalent sumF correctionF (sumData (var 0) (var 1) (var 2) (var 3))
        (correctionData (var 0) (var 2) (var 3))) :=
  closeUniv 4 (.impI (tail_plus_delta _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaPerturbationExponent
