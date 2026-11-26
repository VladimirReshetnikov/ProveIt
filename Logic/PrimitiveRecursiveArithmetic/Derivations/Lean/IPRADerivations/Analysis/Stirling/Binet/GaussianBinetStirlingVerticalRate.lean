import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetStirlingVerticalStep

/-!
# The local vertical Stirling rate at independent observation clocks

Bound the original linear term by the digamma minus logarithm estimate
and the half reciprocal. At one common clock all remaining errors are
quadratic in the step or have a fixed dyadic allowance. The independent
rate removes the auxiliary allowance before subdivision of the panel.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetStirlingVerticalRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetStirlingVerticalStep (linearTerm errorDenominator errorNumerator gammaError logError)
open GaussianBinetLogGammaVerticalStep (dyadicCost step_bound)
open GaussianBinetStirlingRemainder (nameF data offset)
open GaussianBinetStirlingUnitDifference (remainderBudget)
open GaussianBinetStirlingSlopeBound (correction correction_bound)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianNamedInverseRate (diagonal_rate independentRate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (positive_product qadd qmul)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalPowerDifference (bounded_sum_same)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianReconstructionRoots (norm_from_distance)
open GaussianRightHalfPlaneLogarithm (source)
open GaussianRightHalfPlaneLogarithmIncrementMargin (smallStep)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "P" => GaussianLogGammaEulerDigammaFractionsCofinal.nameF
local notation "pd" => GaussianLogGammaEulerDigammaFractionsCofinal.data
local notation "L" => GaussianRightHalfPlaneLogarithm.nameF
local notation "ld" => GaussianRightHalfPlaneLogarithm.data

def quadraticCost (K W : PTm n) : PTm n :=
  num 4*(K*K+two)+K+num 4*(W+one)*(K*K)

def observationCost (A B D sign H W : PTm n) : PTm n :=
  remainderBudget A (B+H) D sign+remainderBudget A B D sign+
    dyadicCost A B D sign H+num 9*H+num 9*W

def leadingNumerator (A D H K W : PTm n) : PTm n :=
  num 3*H*(D*D)+quadraticCost K W*(H*H)*(two*A)
def leadingDenominator (A D : PTm n) : PTm n := two*A*(D*D)

private theorem linear_bound (p A B D sign H : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] bounded (linearTerm p A B D sign H) (num 3*H*unit p+two*H*(two*A)) (two*A*unit p) := by
  let U := unit p
  let a := ap2 P p (pd A B D sign)
  let b := ap2 L p (ld A B D sign)
  let c := correction A B D sign
  let Q := two*A*U
  have hA := h.andE₁.andE₁
  have hD := h.andE₂
  have hu := unit_positive (Γ := Γ) p
  have ht : Γ ⊢[PRAAx] le one two := le_succ_self one
  have hQ := positive_product _ _ (positive_product two A ht hA) hu
  have ha : Γ ⊢[PRAAx] bounded (qsub a b) (two*D*U+num 4*A) Q :=
    bounded_radius_mono _ _ _ _ _ (positive_product A U hA hu) hQ (by dsimp only [Q]; ipra_le 0)
      (diagonal_rate P L _ _ D A p hA (GaussianBinetDigammaLogBound.independent_rate A B D sign h))
  have hb : Γ ⊢[PRAAx] bounded c (D*U) Q :=
    bounded_radius_mono _ _ _ _ _ (positive_product two A ht hA) hQ (by dsimp only [Q]; ipra_le 0)
      (correction_bound A B D sign h)
  have sum := bounded_sum_same _ _ _ _ Q hQ ha hb
  have product := bounded_product _ _ H D _ Q hD hQ (step_bound D sign H hD h.andE₁.andE₂) sum
  exact bounded_radius_mono _ _ _ _ _ (positive_product D Q hD hQ) hQ
    (by dsimp only [Q]; ipra_le 8*𝔞(H)*𝔞(A)^2*𝔞(U)*sl hD) product

private theorem error_bound (p A B D sign H K W : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hHD : Γ ⊢[PRAAx] le H D) (hm : Γ ⊢[PRAAx] le D (K*A)) :
    Γ ⊢[PRAAx] le (errorNumerator p A B D sign H K W)
      ((quadraticCost K W*(H*H)*unit p+observationCost A B D sign H W*(D*D))*(A*A)) := by
  have hs := le_mul_mono hm hm
  dsimp only [errorNumerator,quadraticCost,observationCost,gammaError,logError,GaussianLogGammaEulerTaylorRows.coefficient]
  ipra_le 𝔞(H)^2*𝔞(A)*𝔞(unit p)*sl hm+
    4*𝔞(H)^2*𝔞(D)*𝔞(unit p)*sl hHD+
    4*(𝔞(W)+1)*𝔞(H)^2*𝔞(unit p)*sl hs+
    9*𝔞(H)*𝔞(A)^2*𝔞(D)*sl hD

theorem diagonal (p A B D sign H K C W x : PTm n)
    (h : Γ ⊢[PRAAx] source A D sign) (hK : Γ ⊢[PRAAx] le one K) (hm : Γ ⊢[PRAAx] le D (K*A))
    (hsize : Γ ⊢[PRAAx] le (A+B+A+(B+H)) (C*D)) (hs : Γ ⊢[PRAAx] smallStep H K C D)
    (hHD : Γ ⊢[PRAAx] le H D) (hw : Γ ⊢[PRAAx] bounded (offset A B D sign) W one) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A (B+H) D sign x)) (ap2 nameF p (data A B D sign x))
      (diagonalNumerator (leadingNumerator A D H K W) (leadingDenominator A D)
        (observationCost A B D sign H W+two*H) p) (diagonalDenominator (leadingDenominator A D) p) := by
  let U := unit p
  let DD := D*D
  let AA := A*A
  let T := two*A
  let a := ap2 nameF p (data A (B+H) D sign x)
  let b := ap2 nameF p (data A B D sign x)
  let lin := linearTerm p A B D sign H
  let E := quadraticCost K W*(H*H)*U+observationCost A B D sign H W*DD
  let M := num 3*H*U+two*H*T
  have hA := h.andE₁.andE₁
  have hD := h.andE₂
  have hU := unit_positive (Γ := Γ) p
  have hDD := positive_product D D hD hD
  have hAA := positive_product A A hA hA
  have hT := positive_product two A (le_succ_self one) hA
  have hV := positive_product _ _ (positive_product DD AA hDD hAA) hU
  have hG := positive_product DD U hDD hU
  have hP := positive_product T U hT hU
  have raw := GaussianBinetStirlingVerticalStep.sample_error p A B D sign H K C W x h hK hm hsize hs hw
  have ew : Γ ⊢[PRAAx] le (errorNumerator p A B D sign H K W*(DD*U)) (E*errorDenominator p A D) :=
    le_congr (.eqRefl _) (by dsimp only [E,errorDenominator,DD,AA,U]; ipra_ring)
      (le_mul_mono (error_bound p A B D sign H K W hD hHD hm) (le_refl (DD*U)))
  have er := distance_radius_mono (qsub a b) lin _ _ E (DD*U) hV hG ew raw
  have both := norm_from_distance (qsub a b) lin E (DD*U) M (T*U) hG hP er (linear_bound p A B D sign H h)
  have hN := positive_product _ _ (positive_product T DD hT hDD) hU
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hG hP) hN
    (by dsimp only [E,M,diagonalNumerator,diagonalDenominator,leadingNumerator,leadingDenominator,U,T,DD]; ipra_le 0)
    both

theorem independent_rate (A B D sign H K C W x : PTm n)
    (h : Γ ⊢[PRAAx] source A D sign) (hK : Γ ⊢[PRAAx] le one K) (hm : Γ ⊢[PRAAx] le D (K*A))
    (hsize : Γ ⊢[PRAAx] le (A+B+A+(B+H)) (C*D)) (hs : Γ ⊢[PRAAx] smallStep H K C D)
    (hHD : Γ ⊢[PRAAx] le H D) (hw : Γ ⊢[PRAAx] bounded (offset A B D sign) W one) :
    Γ ⊢[PRAAx] independentRate nameF nameF (data A (B+H) D sign x) (data A B D sign x)
      (leadingNumerator A D H K W) (leadingDenominator A D) := by
  have hN := positive_product (two*A) (D*D) (positive_product two A (le_succ_self one) h.andE₁.andE₁)
    (positive_product D D h.andE₂ h.andE₂)
  apply GaussianNamedLipschitzRate.independent_rate nameF nameF _ _ _ _ (observationCost A B D sign H W+two*H)
    hN (GaussianBinetStirlingRemainder.regular A (B+H) D sign x h)
    (GaussianBinetStirlingRemainder.regular A B D sign x h)
  refine .allI ?_
  let s (y : PTm n) := Syn.shift y
  let Δ := Γ.map Fm.shift
  have h' : Δ ⊢[PRAAx] source (s A) (s D) (s sign) := by simpa [s,Δ,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using h.shift
  have hk' : Δ ⊢[PRAAx] le one (s K) := by simpa [s,Δ,Fm.shift,Syn.shift,one] using hK.shift
  have hm' : Δ ⊢[PRAAx] le (s D) (s K*s A) := by simpa [s,Δ,Fm.shift,Syn.shift] using hm.shift
  have hc' : Δ ⊢[PRAAx] le (s A+s B+s A+(s B+s H)) (s C*s D) := by simpa [s,Δ,Fm.shift,Syn.shift] using hsize.shift
  have hs' : Δ ⊢[PRAAx] smallStep (s H) (s K) (s C) (s D) := by simpa [s,Δ,Fm.shift,Syn.shift] using hs.shift
  have hd' : Δ ⊢[PRAAx] le (s H) (s D) := by simpa [s,Δ,Fm.shift,Syn.shift] using hHD.shift
  have hw' : Δ ⊢[PRAAx] bounded (offset (s A) (s B) (s D) (s sign)) (s W) one :=
    by simpa [s,Δ,Fm.shift,Syn.shift,one] using hw.shift
  simpa [s,Δ,diagonalEnvelope,Syn.shift,leadingNumerator,leadingDenominator,observationCost,quadraticCost,
    dyadicCost,remainderBudget,GaussianLogGammaEulerReciprocalSlopeCofinal.canonicalData,one,two] using
    diagonal (var 0) (s A) (s B) (s D) (s sign) (s H) (s K) (s C) (s W) (s x) h' hk' hm' hc' hs' hd' hw'

end LeanProofs.IPRA.Analysis.GaussianBinetStirlingVerticalRate
