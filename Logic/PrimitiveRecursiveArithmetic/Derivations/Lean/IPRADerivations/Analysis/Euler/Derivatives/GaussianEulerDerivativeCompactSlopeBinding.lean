import IPRADerivations.Analysis.Euler.Derivatives.GaussianEulerDerivativeCommonInterval
import IPRADerivations.Analysis.Euler.Derivatives.GaussianEulerDerivativeSlopeVariation

/-!
# Bind actual compact path slopes to the original improper base slope

The common compact interval keeps an arbitrary deep order-j cutoff r
and an independent order-(j+1) cutoff s. The path continuity precision u
is independent of both. Reversing the original compact truncation rate
and composing with the original path rate gives the exact two rational
errors. Original regularity and one finite-gap argument remove only the
auxiliary same-query observation allowance.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDerivativeCompactSlopeBinding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerDerivativeCommonInterval (compactData improperData)
open GaussianEulerLogarithmicImproperName (data)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianNamedLipschitzRate (diagonalNumerator diagonalDenominator diagonalEnvelope)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => GaussianEulerLogarithmicIntervalName.nameF
local notation "I" => GaussianEulerLogarithmicImproperName.nameF

def source (u j z R B A h D N i : PTm n) : Fm PTm n :=
  GaussianEulerDerivativeSlopeVariation.source u (succ j) z R B A h D N i
def gain (s u : PTm n) : PTm n := two*unit u+num 5*unit (s+num 6)
def denominator (s u : PTm n) : PTm n := unit (s+num 6)*unit u

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (u j z R B A h D N i : PTm n) :
    (source u j z R B A h D N i).subst σ = source (Syn.subst σ u) (Syn.subst σ j) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ h) (Syn.subst σ D) (Syn.subst σ N) (Syn.subst σ i) := by simp [source]
@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (s u : PTm n) :
    Syn.subst σ (gain s u) = gain (Syn.subst σ s) (Syn.subst σ u) := by simp [gain]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (s u : PTm n) :
    Syn.subst σ (denominator s u) = denominator (Syn.subst σ s) (Syn.subst σ u) := by simp [denominator]

theorem denominator_positive (s u : PTm n) : Γ ⊢[PRAAx] le one (denominator s u) :=
  positive_product _ _ (unit_positive _) (unit_positive _)

theorem original_diagonal (t r s u j z R B A h D N i : PTm n)
    (hs : Γ ⊢[PRAAx] source u j z R B A h D N i) : Γ ⊢[PRAAx]
    distanceBounded (ap2 C t (compactData r s j (succ j) z R B A h D N i))
      (ap2 I t (data (succ j) z R B A))
      (diagonalNumerator (gain s u) (denominator s u) (num 4) t) (diagonalDenominator (denominator s u) t) := by
  let S := unit (s+num 6)
  let U := unit u
  let V := unit t
  let Q := denominator s u*V
  have path := GaussianEulerLogarithmicContinuity.path_source u (succ j) z R B A h D hs.andE₁
  have cut := GaussianEulerDerivativeCommonInterval.next_observations t t r s j z R B A h D N i
    path hs.andE₂.andE₁ hs.andE₂.andE₂
  have vary := GaussianNamedInverseRate.rate_at I I _ _ (num 5) U t t
    (GaussianEulerDerivativeSlopeVariation.original_parameter_path_rate u (succ j) z R B A h D N i hs)
  have oldCut := GaussianNamedInverseRate.denominator_positive (Γ := Γ) S t t (unit_positive _)
  have oldVary := GaussianNamedInverseRate.denominator_positive (Γ := Γ) U t t (unit_positive _)
  have qpos : Γ ⊢[PRAAx] le one Q := positive_product _ _ (denominator_positive s u) (unit_positive t)
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 C t (compactData r s j (succ j) z R B A h D N i))
      (ap2 I t (improperData (succ j) z R B A h D N i)) (two*U*V+two*S*U) Q :=
    distance_radius_mono _ _ (rateNumerator two S t t) (rateDenominator S t t) _ Q oldCut qpos
      (le_of_eq_add (d := ConciseIPRA.PTm.zero)
        (by dsimp only [rateNumerator,rateDenominator,Q,S,U,V,denominator]; ipra_ring))
      (distance_symmetric _ _ _ _ oldCut cut)
  have last : Γ ⊢[PRAAx] distanceBounded (ap2 I t (improperData (succ j) z R B A h D N i))
      (ap2 I t (data (succ j) z R B A)) (num 5*S*V+two*S*U) Q :=
    distance_radius_mono _ _ (rateNumerator (num 5) U t t) (rateDenominator U t t) _ Q oldVary qpos
      (le_of_eq_add (d := ConciseIPRA.PTm.zero)
        (by dsimp only [rateNumerator,rateDenominator,Q,S,U,V,denominator]; ipra_ring)) vary
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [diagonalNumerator,gain,denominator,S,U,V]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ qpos first last)

/-- Both original observations are independent. No path query remains
in the stated error, and the fixed base keeps its original certificate. -/
theorem original_rate (r s u j z R B A h D N i : PTm n)
    (hs : Γ ⊢[PRAAx] source u j z R B A h D N i) : Γ ⊢[PRAAx]
    independentRate C I (compactData r s j (succ j) z R B A h D N i) (data (succ j) z R B A)
      (gain s u) (denominator s u) := by
  have path := GaussianEulerLogarithmicContinuity.path_source u (succ j) z R B A h D hs.andE₁
  have compactCN : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN C (compactData r s j (succ j) z R B A h D N i) :=
    GaussianEulerLogarithmicIntervalName.name_regular (succ j)
      (GaussianEulerDerivativeParameterPath.numerator z B h D N i) (R+one) (GaussianEulerDerivativeParameterPath.denominator B D N)
      one (GaussianEulerDerivativeCommonInterval.intervalWidth r s j R A)
      (GaussianEulerDerivativeCommonInterval.intervalDen r s j R A) (GaussianEulerDerivativeCommonInterval.intervalTop r s j R A)
      (GaussianEulerDerivativeCommonInterval.interval_source r s j z R B A h D N i path hs.andE₂.andE₁ hs.andE₂.andE₂)
  have baseCN := GaussianEulerLogarithmicImproperName.name_regular (succ j) z R B A hs.andE₁.andE₁
  apply GaussianNamedLipschitzRate.independent_rate C I _ _ (gain s u) (denominator s u) (num 4)
    (denominator_positive s u) compactCN baseCN
  refine .allI ?_
  let sh (x : PTm n) := Syn.shift x
  have ss : Γ.map Fm.shift ⊢[PRAAx] source (sh u) (sh j) (sh z) (sh R) (sh B) (sh A) (sh h) (sh D) (sh N) (sh i) :=
    by simpa only [Fm.shift,subst_source,Syn.shift,sh] using hs.shift
  simpa only [diagonalEnvelope,GaussianEulerDerivativeCommonInterval.subst_compactData,
    GaussianEulerLogarithmicImproperName.subst_data,subst_gain,subst_denominator,ConciseIPRA.PTm.subst_succ,PTm.subst_num,Syn.shift,sh] using
    original_diagonal (var 0) (sh r) (sh s) (sh u) (sh j) (sh z) (sh R) (sh B) (sh A) (sh h) (sh D) (sh N) (sh i) ss

theorem original_observations (q v r s u j z R B A h D N i : PTm n)
    (hs : Γ ⊢[PRAAx] source u j z R B A h D N i) : Γ ⊢[PRAAx]
    distanceBounded (ap2 C q (compactData r s j (succ j) z R B A h D N i)) (ap2 I v (data (succ j) z R B A))
      (rateNumerator (gain s u) (denominator s u) q v) (rateDenominator (denominator s u) q v) :=
  GaussianNamedInverseRate.rate_at C I _ _ _ _ q v (original_rate r s u j z R B A h D N i hs)

theorem actual_original_compact_parameter_slope_binding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) ⟶
      independentRate C I
        (compactData (var 0) (var 1) (var 3) (succ (var 3)) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11))
        (data (succ (var 3)) (var 4) (var 5) (var 6) (var 7)) (gain (var 1) (var 2)) (denominator (var 1) (var 2))) :=
  closeUniv 12 (.impI (original_rate _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerDerivativeCompactSlopeBinding
