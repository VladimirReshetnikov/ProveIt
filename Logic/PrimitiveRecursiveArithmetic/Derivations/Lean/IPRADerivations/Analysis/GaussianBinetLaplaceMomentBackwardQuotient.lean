import IPRADerivations.Analysis.GaussianBinetLaplaceMomentBackwardWindow
import IPRADerivations.Analysis.GaussianBinetLaplaceMomentForwardQuotient

/-!
# Backward derivatives of the original improper Binet moments

Use the next order's Taylor estimate to move the linear coefficient
from the lower endpoint to the actual base point. The actual quotient
of the original samples at x and x-h then converges linearly to the
negative successor moment at x, at independent observation clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentBackwardQuotient

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetLaplaceMomentImproper (nameF data regular sample_canonical)
open GaussianBinetLaplaceMomentBackwardWindow (source lowerData secondCap lower_source window_geometry
  backward_window_taylor lower_observation_bound)
open GaussianBinetLaplaceMomentForwardQuotient (quotientF targetF targetData positive_parameter)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDominantPairAlgebra (radiusPoint radiusNumerator radius_bounded)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalNumerator diagonalDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qmul qzero positive_product)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianReconstructionRoots (distance_zero_iff)
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (LeanProofs.IPRA.Q.mk _ t)

def backwardCap (j D : PTm n) : PTm n := (secondCap j D+num 3)+(secondCap (succ j) D+num 3)+secondCap j D

def quotientData (j X D R H Q : PTm n) : PTm n :=
  GaussianNamedDifferenceQuotient.data nameF nameF (data j X D R) (lowerData j X D H Q) (radiusNumerator H) Q

def linearBudget (j D H : PTm n) : PTm n := num 3*H*backwardCap j D

def samplerBudget (j X D R H Q : PTm n) : PTm n :=
  GaussianNamedDifferenceQuotient.cost nameF nameF (data j X D R) (lowerData j X D H Q) (radiusNumerator H) Q
    + num 24*Q+num 3

@[simp] theorem subst_backwardCap {m : ℕ} (σ : Fin n → PTm m) (j D : PTm n) :
    Syn.subst σ (backwardCap j D) = backwardCap (Syn.subst σ j) (Syn.subst σ D) := by simp [backwardCap]

@[simp] theorem subst_quotientData {m : ℕ} (σ : Fin n → PTm m) (j X D R H Q : PTm n) :
    Syn.subst σ (quotientData j X D R H Q) =
      quotientData (Syn.subst σ j) (Syn.subst σ X) (Syn.subst σ D) (Syn.subst σ R) (Syn.subst σ H) (Syn.subst σ Q) := by
  simp [quotientData]

@[simp] theorem subst_linearBudget {m : ℕ} (σ : Fin n → PTm m) (j D H : PTm n) :
    Syn.subst σ (linearBudget j D H) = linearBudget (Syn.subst σ j) (Syn.subst σ D) (Syn.subst σ H) := by
  simp [linearBudget]

@[simp] theorem subst_samplerBudget {m : ℕ} (σ : Fin n → PTm m) (j X D R H Q : PTm n) :
    Syn.subst σ (samplerBudget j X D R H Q) =
      samplerBudget (Syn.subst σ j) (Syn.subst σ X) (Syn.subst σ D) (Syn.subst σ R) (Syn.subst σ H) (Syn.subst σ Q) := by
  simp [samplerBudget]

theorem successor_distance (p j X D R H Q : PTm n) (h : Γ ⊢[PRAAx] source X D R H Q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data (succ j) X D R))
      (ap2 nameF p (lowerData (succ j) X D H Q))
      (H*(secondCap j D+num 3*(secondCap (succ j) D+num 3))*unit p+num 12*Q) (Q*unit p) := by
  let r := ap2 nameF p (data (succ j) X D R)
  let y := ap2 nameF p (lowerData (succ j) X D H Q)
  let z := ap2 nameF p (lowerData (succ (succ j)) X D H Q)
  let s := radiusPoint H Q
  let M := secondCap j D
  let N := secondCap (succ j) D+num 3
  let U := unit p
  have hQ := h.andE₂.andE₂.andE₁
  have hh := (window_geometry X D R H Q h).andE₂.andE₂.andE₂
  have hp := unit_positive (Γ := Γ) p
  have den := positive_product _ _ hQ hp
  have den₂ := positive_product _ _ (positive_product _ _ hQ hQ) hp
  have raw : Γ ⊢[PRAAx] distanceBounded r (qsub y (qmul s z)) (num 3*(H*H)*N*U+num 12*(Q*Q)) ((Q*Q)*U) :=
    backward_window_taylor p (succ j) X D R H Q h
  have first : Γ ⊢[PRAAx] distanceBounded r (qsub y (qmul s z)) (num 3*H*N*U+num 12*Q) (Q*U) :=
    distance_radius_mono _ _ _ _ _ _ den₂ den (by ipra_le 3*𝔞(H)*𝔞(N)*𝔞(Q)*𝔞(U)*𝔞(U)*sl hh) raw
  have product := bounded_product s z H Q M one hQ (le_refl one)
    (radius_bounded H Q hQ) (lower_observation_bound p (succ (succ j)) X D R H Q h)
  have shift := (distance_zero_iff _ _ _ hQ).iffMpr
    (bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) product)
  have near : Γ ⊢[PRAAx] distanceBounded (qsub y (qmul s z)) y (H*M) Q :=
    distance_congr (.eqRefl _) (GaussianRationalReconstruction.qsub_zero_right y (sample_canonical _ _ _ _ _))
      (zero_add _) (.eqRefl _)
      (GaussianNamedDifference.difference_distance y y _ qzero zero _ Q hQ
        (GaussianRationalPowerDifference.distance_refl_zero y Q hQ) shift)
  have mapped := distance_radius_mono _ _ _ _ (H*M*U) (Q*U) hQ den
    (le_of_eq_add (d := zero) (by ipra_ring)) near
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [M,N,U]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ den first mapped)

theorem backward_observation_taylor (p j X D R H Q : PTm n) (h : Γ ⊢[PRAAx] source X D R H Q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data j X D R))
      (qsub (ap2 nameF p (lowerData j X D H Q)) (qmul (radiusPoint H Q) (ap2 nameF p (data (succ j) X D R))))
      (num 3*(H*H)*backwardCap j D*unit p+num 24*(Q*Q)) ((Q*Q)*unit p) := by
  let x := ap2 nameF p (data j X D R)
  let y := ap2 nameF p (lowerData j X D H Q)
  let z := ap2 nameF p (data (succ j) X D R)
  let v := ap2 nameF p (lowerData (succ j) X D H Q)
  let s := radiusPoint H Q
  let M := secondCap j D
  let N := secondCap (succ j) D+num 3
  let U := unit p
  let B := (Q*Q)*U
  have hQ := h.andE₂.andE₂.andE₁
  have hh := (window_geometry X D R H Q h).andE₂.andE₂.andE₂
  have hp := unit_positive (Γ := Γ) p
  have den := positive_product _ _ hQ hp
  have den₂ : Γ ⊢[PRAAx] le one B := positive_product _ _ (positive_product _ _ hQ hQ) hp
  have earlier : Γ ⊢[PRAAx] distanceBounded x (qsub y (qmul s v)) (num 3*(H*H)*(M+num 3)*U+num 12*(Q*Q)) B :=
    backward_window_taylor p j X D R H Q h
  have gap : Γ ⊢[PRAAx] distanceBounded z v (H*(M+num 3*N)*U+num 12*Q) (Q*U) :=
    successor_distance p j X D R H Q h
  have weighted : Γ ⊢[PRAAx] distanceBounded (qmul s v) (qmul s z)
      (H*(H*(M+num 3*N)*U+num 12*Q)) B :=
    bound_congr (GaussianRationalRoundedPower.multiplication_difference s v z).eqSymm
      (.eqRefl _) (by dsimp only [B]; ipra_ring)
      (bounded_product s (qsub v z) H Q _ _ hQ den (radius_bounded H Q hQ)
        (distance_symmetric _ _ _ _ den gap))
  have correction : Γ ⊢[PRAAx] distanceBounded (qsub y (qmul s v)) (qsub y (qmul s z))
      (H*(H*(M+num 3*N)*U+num 12*Q)) B :=
    distance_congr (.eqRefl _) (.eqRefl _) (zero_add _) (.eqRefl _)
      (GaussianNamedDifference.difference_distance y y _ _ zero _ B den₂
        (GaussianRationalPowerDifference.distance_refl_zero y B den₂) weighted)
  have joined := distance_triangle_same _ _ _ _ _ _ den₂ earlier correction
  apply distance_radius_mono _ _ _ _ _ _ den₂ den₂ ?_ joined
  dsimp only [backwardCap,M,N,U,B]
  ipra_le 2*𝔞(H)*𝔞(H)*𝔞(secondCap j D)*𝔞(unit p)*𝔞(Q)*𝔞(Q)*𝔞(unit p)+
    12*𝔞(Q)*𝔞(Q)*𝔞(Q)*𝔞(unit p)*sl hh

private theorem quotient_input (j X D R H Q : PTm n) (h : Γ ⊢[PRAAx] source X D R H Q) :
    Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.input nameF nameF (data j X D R) (lowerData j X D H Q) (radiusNumerator H) Q :=
  .andI (regular _ _ _ _ h.andE₁) (.andI (regular _ _ _ _ (lower_source X D R H Q h))
    (positive_parameter H Q h.andE₂.andE₁ h.andE₂.andE₂.andE₁))

theorem quotient_regular (j X D R H Q : PTm n) (h : Γ ⊢[PRAAx] source X D R H Q) :
    Γ ⊢[PRAAx] pointCN quotientF (quotientData j X D R H Q) :=
  GaussianNamedDifferenceQuotient.name_regular _ _ _ _ _ _ (quotient_input j X D R H Q h)

theorem quotient_sample (p j X D R H Q : PTm n) (h : Γ ⊢[PRAAx] source X D R H Q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 quotientF p (quotientData j X D R H Q)) (ap2 targetF p (targetData j X D R))
      (diagonalNumerator (linearBudget j D H) Q (samplerBudget j X D R H Q) p) (diagonalDenominator Q p) :=
  GaussianBinetLaplaceMomentForwardQuotient.sample_of_taylor p _ _ _ H Q (backwardCap j D) (num 24)
    (quotient_input j X D R H Q h) (regular _ _ _ _ h.andE₁) (sample_canonical _ _ _ _ _) h.andE₂.andE₁ h.andE₂.andE₂.andE₁
    (backward_observation_taylor p j X D R H Q h)

theorem backward_rate (j X D R H Q : PTm n) (h : Γ ⊢[PRAAx] source X D R H Q) :
    Γ ⊢[PRAAx] independentRate quotientF targetF (quotientData j X D R H Q) (targetData j X D R)
      (linearBudget j D H) Q := by
  apply GaussianNamedLipschitzRate.independent_rate quotientF targetF (quotientData j X D R H Q) (targetData j X D R)
    (linearBudget j D H) Q (samplerBudget j X D R H Q) h.andE₂.andE₂.andE₁
    (quotient_regular j X D R H Q h) (GaussianNameRingLaws.negative_fast _ _ (regular (succ j) X D R h.andE₁))
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s X) (s D) (s R) (s H) (s Q) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,GaussianBinetLaplaceMomentBackwardWindow.subst_source] using h.shift
  change Δ ⊢[PRAAx] distanceBounded (ap2 quotientF (var 0) (Syn.shift (quotientData j X D R H Q)))
    (ap2 targetF (var 0) (Syn.shift (targetData j X D R)))
    (diagonalNumerator (Syn.shift (linearBudget j D H)) (s Q) (Syn.shift (samplerBudget j X D R H Q)) (var 0))
    (diagonalDenominator (s Q) (var 0))
  rw [show Syn.shift (quotientData j X D R H Q) = quotientData (s j) (s X) (s D) (s R) (s H) (s Q)
        from subst_quotientData _ _ _ _ _ _ _,
    show Syn.shift (targetData j X D R) = targetData (s j) (s X) (s D) (s R)
        from GaussianBinetLaplaceMomentForwardQuotient.subst_targetData _ _ _ _ _,
    show Syn.shift (linearBudget j D H) = linearBudget (s j) (s D) (s H) from subst_linearBudget _ _ _ _,
    show Syn.shift (samplerBudget j X D R H Q) = samplerBudget (s j) (s X) (s D) (s R) (s H) (s Q)
        from subst_samplerBudget _ _ _ _ _ _ _]
  exact quotient_sample (var 0) (s j) (s X) (s D) (s R) (s H) (s Q) hs

theorem actual_improper_Binet_moment_backward_quotient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let j := var 0
     let X := var 1
     let D := var 2
     let R := var 3
     let H := var 4
     let Q := var 5
     source X D R H Q ⟶ independentRate quotientF targetF (quotientData j X D R H Q) (targetData j X D R)
      (linearBudget j D H) Q) :=
  closeUniv 6 (.impI (backward_rate _ _ _ _ _ _ Prf.hyp0))

def forwardData (j X D R H Q : PTm n) : PTm n :=
  GaussianBinetLaplaceMomentForwardQuotient.quotientData j X D R
    (GaussianLogGammaEulerResidualRadius.radius (X*Q+H*D) zero) H Q

theorem two_sided_rate (j X D R H Q : PTm n) (h : Γ ⊢[PRAAx] source X D R H Q) : Γ ⊢[PRAAx]
    independentRate quotientF targetF (forwardData j X D R H Q) (targetData j X D R)
        (GaussianBinetLaplaceMomentForwardQuotient.linearBudget j D H) Q ⋏
      independentRate quotientF targetF (quotientData j X D R H Q) (targetData j X D R) (linearBudget j D H) Q := by
  have hD := h.andE₁.andE₁.andE₂
  have hQ := h.andE₂.andE₂.andE₁
  have hX := h.andE₁.andE₁.andE₁.andE₁
  have moved := GaussianLogGammaEulerResidualRadius.source_of_right_half_plane (X*Q+H*D) zero (D*Q) zero
    (.andI (.andI (le_trans (positive_product _ _ hX hQ) (le_add_right _ _)) (.orI₁ (.eqRefl zero)))
      (positive_product _ _ hD hQ))
  exact .andI (GaussianBinetLaplaceMomentForwardQuotient.forward_rate j X D R _ H Q h.andE₁ moved h.andE₂.andE₁ hQ
    (window_geometry X D R H Q h).andE₂.andE₂.andE₂) (backward_rate j X D R H Q h)

theorem actual_improper_Binet_moment_two_sided_quotient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let j := var 0
     let X := var 1
     let D := var 2
     let R := var 3
     let H := var 4
     let Q := var 5
     source X D R H Q ⟶
       (independentRate quotientF targetF (forwardData j X D R H Q) (targetData j X D R)
           (GaussianBinetLaplaceMomentForwardQuotient.linearBudget j D H) Q ⋏
         independentRate quotientF targetF (quotientData j X D R H Q) (targetData j X D R) (linearBudget j D H) Q)) :=
  closeUniv 6 (.impI (two_sided_rate _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentBackwardQuotient
