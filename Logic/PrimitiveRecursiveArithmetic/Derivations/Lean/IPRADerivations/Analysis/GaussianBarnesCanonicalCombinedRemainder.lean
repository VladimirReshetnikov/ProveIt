import IPRADerivations.Analysis.GaussianBarnesCanonicalHarmonicRemainder
import IPRADerivations.Analysis.GaussianBarnesCanonicalTerminalRemainder
import IPRADerivations.Analysis.GaussianBinetStirlingRealBound
import IPRADerivations.Analysis.GaussianNamedSmallPerturbationTransport

/-!
# Quantitative bound on the combined Barnes shift remainder

The three original logarithmic errors use the same integer cutoff.
Multiplication by the fixed rational coefficient retains the actual
named multiplication clock and introduces no cutoff-dependent loss.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCombinedRemainder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast sum_distance)
open GaussianNamedInverseRate (diagonal_rate)
open GaussianNamedSmallPerturbationTransport (productClock product_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (qzero qadd qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr qmul_zero_left qzero_add qzero_canonical)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "C" => constantF
local notation "H" => GaussianBarnesCanonicalHarmonicRemainder.nameF
local notation "hdata" => GaussianBarnesCanonicalHarmonicRemainder.data
local notation "T" => GaussianBarnesCanonicalTerminalRemainder.nameF
local notation "tdata" => GaussianBarnesCanonicalTerminalRemainder.data
local notation "S" => GaussianStirlingGlobalBounds.remainderF
local notation "sdata" => GaussianStirlingGlobalBounds.remainderData

abbrev weightedF : PR 2 := multiplyF H C
def weightedData (c K : PTm n) : PTm n := multiplyData H C (hdata K) c
abbrev sumF : PR 2 := addF weightedF T
def sumData (c w R B K : PTm n) : PTm n := addData (weightedData c K) (tdata w R B K)
abbrev nameF : PR 2 := GaussianNamedDifference.nameF sumF S
def data (c w R B K : PTm n) : PTm n := GaussianNamedDifference.data (sumData c w R B K) (sdata K one zero)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (c w R B K : PTm n) :
    Syn.subst σ (data c w R B K) = data (Syn.subst σ c) (Syn.subst σ w) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ K) := by
  simp [data,sumData,weightedData,one]

private theorem stirling_source (K : PTm n) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx] GaussianStirlingNames.source K one :=
  .andI hK (le_refl one)

theorem regular (c w R B K : PTm n) (h : Γ ⊢[PRAAx] GaussianBarnesCanonicalTerminalRemainder.source w R B K) :
    Γ ⊢[PRAAx] pointCN nameF (data c w R B K) :=
  GaussianNamedDifference.name_regular _ _ _ _
    (add_fast _ _ _ _ (multiply_fast H C _ _ (GaussianBarnesCanonicalHarmonicRemainder.regular K h.andE₂.andE₁)
      (constant_regular c)) (GaussianBarnesCanonicalTerminalRemainder.regular w R B K h))
    (GaussianStirlingGlobalBounds.remainder_regular K one zero (stirling_source K h.andE₂.andE₁))

theorem stirling_error (p K : PTm n) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    distanceBounded (ap2 S p (sdata K one zero)) qzero (unit p+two*K) (K*unit p) := by
  let R := num 12*K
  have hR := positive_product (Γ := Γ) (num 12) K
    (Foundations.NumeralPrimes.num_le (a := 1) (b := 12) (by decide)) hK
  have rate := diagonal_rate S C (sdata K one zero) qzero one R p hR
    (GaussianBinetStirlingRealBound.original_real_rate K one zero (stirling_source K hK))
  exact distance_congr (.eqRefl _) (constant_at p qzero) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hR (unit_positive p))
      (positive_product _ _ hK (unit_positive p)) (le_of_eq_add (d := num 11*K*unit p*unit p) (by dsimp [R]; ipra_ring)) rate)

theorem weighted_error (p c M K : PTm n) (hK : Γ ⊢[PRAAx] le one K) (hc : Γ ⊢[PRAAx] bounded c M one) : Γ ⊢[PRAAx]
    distanceBounded (ap2 weightedF p (weightedData c K)) qzero (M*unit p+num 17*M*K) (K*unit p) := by
  let s := productClock H C (hdata K) c p
  let Vs := unit s
  let U := unit p
  have hs : Γ ⊢[PRAAx] le U Vs := GaussianExponentialReference.unit_monotone (le_add_right p _)
  have hv := positive_product K Vs hK (unit_positive s)
  have he := positive_product K U hK (unit_positive p)
  have raw := GaussianBarnesCanonicalHarmonicRemainder.sample_error s K hK
  have b0 : Γ ⊢[PRAAx] bounded (qzero : PTm n) zero one :=
    (GaussianReconstructionRoots.distance_zero_iff _ _ _ (le_refl one)).iffMp
      (GaussianRationalPowerDifference.distance_refl_zero _ _ (le_refl one))
  have scaled := GaussianNameRingLaws.product_left_error _ qzero c _ _ M zero hv raw hc b0
  have eq := (product_at (Γ := Γ) H C (hdata K) c p).eqTrans (qmul_congr (.eqRefl _) (constant_at s c))
  have clearing : Γ ⊢[PRAAx] le ((Vs+num 17*K)*M*(K*U)) ((M*U+num 17*M*K)*(K*Vs)) := by
    ipra_le 17*𝔞 M*𝔞 K^2*sl hs
  exact distance_congr eq.eqSymm (qmul_zero_left c) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hv he clearing scaled)

theorem sample_error (p c M w R B K : PTm n) (h : Γ ⊢[PRAAx] GaussianBarnesCanonicalTerminalRemainder.source w R B K)
    (hc : Γ ⊢[PRAAx] bounded c M one) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data c w R B K)) qzero
      ((R*R+M+one)*unit p+(num 17*M+num 18)*K) (K*unit p) := by
  let A := weightedData c K
  let B' := tdata w R B K
  let D := sdata K one zero
  let X := sumData c w R B K
  let a := ap2 weightedF p A
  let b := ap2 T p B'
  let d := ap2 S p D
  let x := ap2 sumF p X
  let y := ap2 nameF p (data c w R B K)
  let U := unit p
  let E := K*U
  let hK := h.andE₂.andE₁
  have hu := unit_positive (Γ := Γ) p
  have he := positive_product K U hK hu
  have hw := multiply_fast H C (hdata K) c (GaussianBarnesCanonicalHarmonicRemainder.regular K hK) (constant_regular c)
  have ht := GaussianBarnesCanonicalTerminalRemainder.regular w R B K h
  have hs := GaussianStirlingGlobalBounds.remainder_regular K one zero (stirling_source K hK)
  have hx := add_fast weightedF T A B' hw ht
  have lift (q r L : PTm n) (v : Γ ⊢[PRAAx] distanceBounded q r L U) : Γ ⊢[PRAAx] distanceBounded q r (L*K) E :=
    distance_radius_mono q r L U _ _ hu he (le_of_eq_add (d := zero) (by dsimp only [E]; ipra_ring)) v
  have obs := lift x (qadd a b) (num 3) (distance_congr (.eqRefl _) (.eqRefl _)
    (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
    (GaussianNameRingLaws.add_sample_error weightedF T A B' p hw ht))
  have errs := sum_distance _ _ _ _ _ _ E he (weighted_error p c M K hK hc)
    (GaussianBarnesCanonicalTerminalRemainder.sample_error p w R B K h)
  have sum := distance_triangle_same x (qadd a b) qzero _ _ E he obs
    (distance_congr (.eqRefl _) (qzero_add qzero qzero_canonical) (.eqRefl _) (.eqRefl _) errs)
  have rem := GaussianNamedDifference.difference_distance x qzero d qzero _ _ E he sum (stirling_error p K hK)
  have obs' := lift y (qsub x d) (num 6) (GaussianNamedDifference.sample_error sumF S X D p hx hs)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same y (qsub x d) qzero _ _ E he obs'
      (distance_congr (.eqRefl _) (GaussianCoefficientNormOrder.qsub_self qzero) (.eqRefl _) (.eqRefl _) rem))

theorem actual_Barnes_combined_logarithm_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let p := var 0
     let c := var 1
     let M := var 2
     let w := var 3
     let R := var 4
     let B := var 5
     let K := var 6
     GaussianBarnesCanonicalTerminalRemainder.source w R B K ⟶ bounded c M one ⟶
       distanceBounded (ap2 nameF p (data c w R B K)) qzero ((R*R+M+one)*unit p+(num 17*M+num 18)*K) (K*unit p)) :=
  closeUniv 7 (.impI (.impI (sample_error _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCombinedRemainder
