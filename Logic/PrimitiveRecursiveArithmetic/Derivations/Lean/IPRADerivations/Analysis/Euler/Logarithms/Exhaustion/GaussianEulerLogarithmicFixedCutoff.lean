import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicImproperName

/-!
# Compare the original logarithmic name with a fixed late cutoff

For each requested tail budget, every sufficiently late fixed interval
represents the varying-cutoff name within twice that budget. Observation
queries on the original improper and compact programs stay independent.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicFixedCutoff

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLogarithmicCutoffCauchy (source subst_source observation pairNumerator pairDenominator)
open GaussianEulerLogarithmicCommonCutoff (cutoff cutoff_later)
open GaussianEulerCutoffCauchyComparison (clock)
open GaussianEulerLogarithmicCutoffSplit (fullData)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalNumerator diagonalDenominator diagonalEnvelope independent_rate)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "I" => GaussianEulerLogarithmicImproperName.nameF
local notation "C" => GaussianEulerLogarithmicIntervalName.nameF
local notation "input" => GaussianEulerLogarithmicImproperName.data

theorem original_diagonal_rate (t r j z R B A k : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hk : Γ ⊢[PRAAx] le (cutoff r j A) k) : Γ ⊢[PRAAx]
    distanceBounded (ap2 I t (input j z R B A)) (observation t j z R B A k)
      (diagonalNumerator two (unit (r+num 6)) (num 12) t) (diagonalDenominator (unit (r+num 6)) t) := by
  let m := t+succ k
  let s := clock m
  let U := unit t
  let M := unit m
  let S := unit s
  let K := unit (r+num 6)
  let D := K*U
  let Y := ap2 I m (input j z R B A)
  have hU := unit_positive (Γ := Γ) t
  have hM := unit_positive (Γ := Γ) m
  have hS := unit_positive (Γ := Γ) s
  have hK := unit_positive (Γ := Γ) (r+num 6)
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hK hU
  have htm : Γ ⊢[PRAAx] le t m := le_add_right _ _
  have hUM : Γ ⊢[PRAAx] le U M := GaussianExponentialReference.unit_monotone htm
  have hUS : Γ ⊢[PRAAx] le U S := GaussianExponentialReference.unit_monotone
    (le_trans htm (le_add_right m (num 4)))
  have kl : Γ ⊢[PRAAx] lt k (cutoff m j A) := le_trans (le_add_left (succ k) t) (cutoff_later m j A)
  have close := GaussianEulerLogarithmicImproperName.name_observations t m j z R B A h
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 I t (input j z R B A)) Y (two*K) D :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU hM) hD
      (by dsimp only [D,U,M]; ipra_le (𝔞(unit (r+num 6))*𝔞(unit t))*sl hUM) close
  have pair := GaussianEulerLogarithmicCutoffCauchy.strict_pair_bound s t r j z R B A k (cutoff m j A) h hk kl
  have converted : Γ ⊢[PRAAx] distanceBounded (observation s j z R B A (cutoff m j A))
      (observation t j z R B A k) (two*U+num 10*K) D :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hS hU) hK) hD
      (by dsimp only [pairNumerator,pairDenominator,D,U,K,S]
          ipra_le (𝔞(unit (r+num 6))*𝔞(unit (r+num 6))*𝔞(unit t))*sl hUS) pair
  have second : Γ ⊢[PRAAx] distanceBounded Y (observation t j z R B A k) (two*U+num 10*K) D :=
    distance_congr (GaussianEulerLogarithmicImproperName.name_at m j z R B A).eqSymm
      (.eqRefl _) (.eqRefl _) (.eqRefl _) converted
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold diagonalNumerator; dsimp only [U,K]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD first second)

theorem original_fixed_cutoff_rate (r j z R B A k : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hk : Γ ⊢[PRAAx] le (cutoff r j A) k) : Γ ⊢[PRAAx]
    independentRate I C (input j z R B A) (fullData j z R B A k) two (unit (r+num 6)) := by
  apply independent_rate I C _ _ two (unit (r+num 6)) (num 12) (unit_positive _)
    (GaussianEulerLogarithmicImproperName.name_regular j z R B A h)
    (GaussianEulerLogarithmicCutoffCauchy.observation_regular j z R B A k h)
  refine .allI ?_
  let sh := fun t : PTm n => Syn.shift t
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh A) :=
    by simpa only [Fm.shift,Syn.shift,subst_source,sh] using h.shift
  have ks : Γ.map Fm.shift ⊢[PRAAx] le (cutoff (sh r) (sh j) (sh A)) (sh k) :=
    by simpa [Fm.shift,Syn.shift,sh] using hk.shift
  simpa [diagonalEnvelope,Syn.shift,observation,sh] using
    original_diagonal_rate (var 0) (sh r) (sh j) (sh z) (sh R) (sh B) (sh A) (sh k) hs ks

theorem actual_original_logarithmic_fixed_cutoff_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 2) (var 3) (var 4) (var 5) ⟶ le (cutoff (var 0) (var 1) (var 5)) (var 6) ⟶
      independentRate I C (input (var 1) (var 2) (var 3) (var 4) (var 5))
        (fullData (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) two (unit (var 0+num 6))) :=
  closeUniv 7 (.impI (.impI (original_fixed_cutoff_rate _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicFixedCutoff
