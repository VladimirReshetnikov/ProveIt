import IPRADerivations.Analysis.Stirling.AllOrders.Truncation.GaussianStirlingAllOrderTruncationAlgebra
import IPRADerivations.Analysis.Stirling.AllOrders.ImproperBounds.GaussianStirlingAllOrderImproperName

/-!
# The original Stirling remainder equals the signed centered kernel

The literal correction terms are accumulated in increasing order.
The calculation keeps the original remainder name and the actual
cofinal Bernoulli kernel, with independent observation clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderLogTruncation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianStirlingNames (source)
open GaussianStirlingGlobalBounds (remainderF remainderData remainder_regular)
open GaussianStirlingAllOrderTruncationAlgebra (signedScale correction truncation signed_initial_cancel signed_recurrence_exact)
open GaussianStirlingAllOrderPanelPartsNames (constantCap initial derivativeRatio weightedPrimitive fixed_product_distance
  normalized_product_error difference_error)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianRationalHorner (qmul qadd qzero positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalSyntheticDivision (qsub_congr qmul_congr)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianValueNormalizerExtensionality (rawDiagonal)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "J" => GaussianStirlingAllOrderPanelPartsNames.nameF
local notation "JData" => GaussianStirlingAllOrderPanelPartsNames.nameData
local notation "I" => GaussianStirlingAllOrderImproperName.nameF
local notation "IData" => GaussianStirlingAllOrderImproperName.data
local notation "subF" => GaussianNamedDifference.nameF
local notation "subData" => GaussianNamedDifference.data
local notation "scaleF" => GaussianBoundedConstantProductName.nameF
local notation "scaleData" => GaussianBoundedConstantProductName.data

def errorF : PR 2 := subF remainderF constantF
def errorData (m : ℕ) (A B x : PTm n) : PTm n := subData (remainderData A B x) (truncation m A B)
def signedF (m : ℕ) : PR 2 := scaleF (I m)
def signedData (m : ℕ) (A B : PTm n) : PTm n :=
  scaleData (constantCap (signedScale m)) (signedScale m) (IData m A B)

def stepCost (m : ℕ) : PTm n := (constantCap (derivativeRatio m)+one)+constantCap (derivativeRatio m)*num 6

def projectionCost : ℕ → PTm n
  | 0 => constantCap (signedScale 0)*(constantCap initial+one)
  | m+1 => constantCap (signedScale (m+1))*stepCost m+(projectionCost m+zero)

def cost (m : ℕ) : PTm n :=
  (constantCap (signedScale m)+one)+constantCap (signedScale m)*two+projectionCost m+num 6

@[simp] theorem subst_errorData {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (A B x : PTm n) :
    Syn.subst σ (errorData m A B x) = errorData m (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ x) :=
  by simp [errorData]
@[simp] theorem subst_signedData {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (A B : PTm n) :
    Syn.subst σ (signedData m A B) = signedData m (Syn.subst σ A) (Syn.subst σ B) := by simp [signedData]
@[simp] theorem subst_stepCost {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) :
    Syn.subst σ (stepCost m : PTm n) = (stepCost m : PTm l) := by simp [stepCost]
@[simp] theorem subst_projectionCost {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) :
    Syn.subst σ (projectionCost m : PTm n) = (projectionCost m : PTm l) := by
  induction m with
  | zero => simp [projectionCost]
  | succ m ih => simp [projectionCost,ih]
@[simp] theorem subst_cost {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) :
    Syn.subst σ (cost m : PTm n) = (cost m : PTm l) := by simp [cost]

theorem error_regular (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) : Γ ⊢[PRAAx]
    pointCN errorF (errorData m A B x) :=
  GaussianNamedDifference.name_regular _ _ _ _ (remainder_regular A B x hs) (constant_regular _)

theorem signed_regular (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) : Γ ⊢[PRAAx]
    pointCN (signedF m) (signedData m A B) :=
  GaussianBoundedConstantProductName.name_regular _ _ _ _
    (.andI (GaussianStirlingAllOrderImproperName.name_regular m A B x hs)
      (GaussianStirlingAllOrderPanelPartsNames.constant_bound _))

private theorem initial_readback (R : PTm n) (hR : Γ ⊢[PRAAx] GaussianRationalHorner.canonical R) :
    Γ ⊢[PRAAx] qmul (signedScale 0) (qmul initial R) ≐ qsub R (truncation 0 R R) :=
  (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
    ((qmul_congr signed_initial_cancel (.eqRefl _)).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
        ((GaussianReciprocalHorner.qmul_one_right R hR).eqTrans
          (GaussianRationalReconstruction.qsub_zero_right R hR).eqSymm)))

private theorem step_error (m : ℕ) (A B p x : PTm n) (hs : Γ ⊢[PRAAx] source A B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (J (m+1)) p (JData (m+1) A B x))
      (qmul (derivativeRatio m) (qsub (weightedPrimitive m A B) (ap2 (J m) p (JData m A B x))))
      (stepCost m) (unit p) := by
  let f := subF constantF (J m)
  let d := subData (weightedPrimitive m A B) (JData m A B x)
  let c := derivativeRatio (n := n) m
  have h := GaussianNamedDifference.name_regular constantF (J m) (weightedPrimitive m A B) (JData m A B x)
    (constant_regular _) (GaussianStirlingAllOrderPanelPartsNames.name_regular m A B x hs)
  have first := normalized_product_error f c d p h
  have second := fixed_product_distance c _ _ _ _ (unit_positive p) (difference_error m A B x p hs)
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p) first second

theorem signed_projection_error (m : ℕ) (A B p x : PTm n) (hs : Γ ⊢[PRAAx] source A B) : Γ ⊢[PRAAx]
    distanceBounded (qmul (signedScale m) (ap2 (J m) p (JData m A B x)))
      (qsub (ap2 remainderF p (remainderData A B x)) (truncation m A B)) (projectionCost m) (unit p) := by
  let R := ap2 remainderF p (remainderData A B x)
  have hp := unit_positive (Γ := Γ) p
  induction m with
  | zero =>
    have hR : Γ ⊢[PRAAx] GaussianRationalHorner.canonical R := GaussianNameArithmetic.add_canonical _ _ _ _ _
    have h := normalized_product_error remainderF initial (remainderData A B x) p (remainder_regular A B x hs)
    exact distance_congr (.eqRefl _) (initial_readback R hR) (.eqRefl _) (.eqRefl _)
      (fixed_product_distance (signedScale 0) _ _ _ _ hp h)
  | succ m ih =>
    let u := ap2 (J m) p (JData m A B x)
    let c := correction m A B
    let s := signedScale (n := n) (m+1)
    have first := distance_congr (.eqRefl _) (signed_recurrence_exact m A B u hs.andE₁) (.eqRefl _) (.eqRefl _)
      (fixed_product_distance s _ _ _ _ hp (step_error m A B p x hs))
    have second := GaussianNamedDifference.difference_distance _ _ c c _ zero _ hp ih (distance_refl_zero _ _ hp)
    have reordered := GaussianRationalInverseQuadraticAlgebra.subtract_sum (Γ := Γ) R (truncation m A B) c
    exact distance_triangle_same _ _ _ _ _ _ hp first
      (distance_congr (.eqRefl _) reordered (.eqRefl _) (.eqRefl _) second)

theorem diagonal_error (m : ℕ) (A B p x : PTm n) (hs : Γ ⊢[PRAAx] source A B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (signedF m) p (signedData m A B)) (ap2 errorF p (errorData m A B x)) (cost m) (unit p) := by
  let u := unit p
  let r := remainderData A B x
  let c := truncation m A B
  let s := signedScale (n := n) m
  have hu := unit_positive (Γ := Γ) p
  have first := normalized_product_error (I m) s (IData m A B) p
    (GaussianStirlingAllOrderImproperName.name_regular m A B x hs)
  have prior := cross_at (I m) (J m) (IData m A B) (JData m A B x) p p
    (GaussianStirlingAllOrderImproperName.original_improper_cross m A B x hs)
  have second := fixed_product_distance s _ _ _ _ hu
    (distance_radius_mono _ _ _ _ two u (positive_product _ _ hu hu) hu (by unfold u; ipra_le 0) prior)
  have third := signed_projection_error m A B p x hs
  have fourth := distance_congr (.eqRefl _) (qsub_congr (.eqRefl _) (constant_at p c))
    (.eqRefl _) (.eqRefl _) (GaussianNamedDifference.sample_error remainderF constantF r c p
      (remainder_regular A B x hs) (constant_regular _))
  exact distance_triangle_same _ _ _ _ _ _ hu
    (distance_triangle_same _ _ _ _ _ _ hu (distance_triangle_same _ _ _ _ _ _ hu first second) third)
    (distance_symmetric _ _ _ _ hu fourth)

theorem original_logarithmic_truncation (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) : Γ ⊢[PRAAx]
    crossEquivalent (signedF m) errorF (signedData m A B) (errorData m A B x) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (cost m)
    (signed_regular m A B x hs) (error_regular m A B x hs)
  refine .allI ?_
  let a := Syn.shift A
  let b := Syn.shift B
  let c := Syn.shift x
  let Δ := Γ.map Fm.shift
  have h : Δ ⊢[PRAAx] source a b := by simpa [Δ,a,b,Fm.shift,Syn.shift] using hs.shift
  simpa [rawDiagonal,a,b,c,Δ,Syn.shift,GaussianCoefficientNameBounds.unit,GaussianEuclideanPointDistance.unit] using
    diagonal_error m a b (var 0) c h

theorem actual_all_order_logarithmic_truncation_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source (var 0) (var 1) ⟶
        crossEquivalent (signedF m) errorF (signedData m (var 0) (var 1)) (errorData m (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_logarithmic_truncation m _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderLogTruncation
