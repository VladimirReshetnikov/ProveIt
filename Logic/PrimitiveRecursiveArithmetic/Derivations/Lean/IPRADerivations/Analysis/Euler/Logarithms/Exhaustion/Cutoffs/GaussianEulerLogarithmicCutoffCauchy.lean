import IPRADerivations.Analysis.Euler.Logarithms.Exhaustion.Cutoffs.GaussianEulerLogarithmicCommonTails
import IPRADerivations.Analysis.Euler.Logarithms.Exhaustion.Cutoffs.GaussianEulerLogarithmicCutoffSplit
import IPRADerivations.Analysis.Euler.CompactExhaustion.Cutoffs.GaussianEulerCutoffCauchyComparison

/-!
# Cauchy estimates for the actual logarithmic Euler quadratures

On a later interval split, compare the original compact observation
with the earlier interval and both original tails. The compact rounding
and two tail bounds are all paid for by the computed observation clock.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicCutoffCauchy

open_ipra
open GaussianEulerLogarithmicIntervalName (nameF name_regular)
open GaussianEulerLogarithmicCutoffSplit (fullData lowerData upperData)
open GaussianEulerLogarithmicCommonCutoff (cutoff)
open GaussianEulerCutoffCauchyComparison (clock clock_unit)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (canonical positive_product qzero qadd)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianNameEquivalence (point_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def observation (p j z R B A k : PTm n) : PTm n := ap2 nameF p (fullData j z R B A k)
def source (z R B A : PTm n) : Fm PTm n := GaussianEulerLowerPowerCoefficients.source z R B A
def pairNumerator (s t r : PTm n) : PTm n :=
  unit t*unit (r+num 6)+num 9*unit s*unit (r+num 6)+two*unit s*unit t
def pairDenominator (s t r : PTm n) : PTm n := unit s*unit t*unit (r+num 6)

ipra_subst observation
ipra_subst source

theorem observation_regular (j z R B A k : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN nameF (fullData j z R B A k) :=
  name_regular j z R B _ _ _ _ (GaussianEulerLogarithmicCutoffSplit.full_source j z R B A k h.andE₂.andE₁)

theorem observation_canonical (p j z R B A k : PTm n) : Γ ⊢[PRAAx] canonical (observation p j z R B A k) :=
  GaussianCompactRiemannName.name_canonical GaussianEulerLogarithmicCompactName.evaluatorF p _ _ _ _ _ _

private theorem raw_sum_bound (x y z U K : PTm n) (hU : Γ ⊢[PRAAx] le one U) (hK : Γ ⊢[PRAAx] le one K)
    (hy : Γ ⊢[PRAAx] canonical y) (hx : Γ ⊢[PRAAx] bounded x (U+K) (K*U))
    (hz : Γ ⊢[PRAAx] bounded z (U+K) (K*U)) : Γ ⊢[PRAAx]
    distanceBounded (qadd x (qadd y z)) y (two*(U+K)) (K*U) := by
  have hD := positive_product _ _ hK hU
  have left := (GaussianReconstructionRoots.distance_zero_iff x _ _ hD).iffMpr hx
  have right := (GaussianReconstructionRoots.distance_zero_iff z _ _ hD).iffMpr hz
  have held := GaussianRationalPowerDifference.distance_refl_zero y (K*U) hD
  have inner := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hD held right
  have reduced : Γ ⊢[PRAAx] distanceBounded (qadd y z) y (U+K) (K*U) :=
    distance_congr (.eqRefl _) (GaussianRationalLinearProduct.qadd_zero_right y hy)
    (by ipra_ring) (.eqRefl _) inner
  have outer := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hD left reduced
  exact distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qzero_add y hy)
    (by ipra_ring) (.eqRefl _) outer

theorem strict_pair_bound (s t r j z R B A k l : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hk : Γ ⊢[PRAAx] le (cutoff r j A) k) (hkl : Γ ⊢[PRAAx] lt k l) : Γ ⊢[PRAAx]
    distanceBounded (observation s j z R B A l) (observation t j z R B A k)
      (pairNumerator s t r) (pairDenominator s t r) := by
  let S := unit s
  let U := unit t
  let K := unit (r+num 6)
  let D := pairDenominator s t r
  have hS := unit_positive (Γ := Γ) s
  have hU := unit_positive (Γ := Γ) t
  have hK := unit_positive (Γ := Γ) (r+num 6)
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ hS hU) hK
  have split := GaussianEulerLogarithmicCutoffSplit.original_observations s t j z R B A k l
    (.andI h.andE₂.andE₁ (.andI h.andE₁ hkl))
  have hl := GaussianEulerLogarithmicCommonTails.lower_bound t r j z R B A k l h hk (le_of_lt hkl)
  have hu := GaussianEulerLogarithmicCommonTails.upper_bound t r j z R B A k l h hk (le_of_lt hkl)
  have tails : Γ ⊢[PRAAx] distanceBounded
      (qadd (ap2 nameF t (lowerData j z R B A k l)) (qadd (observation t j z R B A k) (ap2 nameF t (upperData j z R B A k l))))
      (observation t j z R B A k)
      (two*(U+K)) (K*U) := raw_sum_bound _ _ _ U K hU hK (observation_canonical t j z R B A k) hl hu
  have first := distance_radius_mono _ _ _ _ ((U+num 7*S)*K) D (positive_product _ _ hS hU) hD
    (le_congr (.eqRefl _) (by unfold D pairDenominator; ipra_ring) (le_refl _)) split
  have second := distance_radius_mono _ _ _ _ (two*(U+K)*S) D (positive_product _ _ hK hU) hD
    (le_congr (.eqRefl _) (by unfold D pairDenominator; ipra_ring) (le_refl _)) tails
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold pairNumerator S U K; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD first second)

theorem strict_cutoff_increase (p q j A : PTm n) (h : Γ ⊢[PRAAx] lt p q) : Γ ⊢[PRAAx]
    lt (cutoff p j A) (cutoff q j A) := by
  have hc : Γ ⊢[PRAAx] le (GaussianEulerLogarithmicLowerCutoffBudget.clock p j A)
      (GaussianEulerLogarithmicLowerCutoffBudget.clock q j A) := by
    unfold GaussianEulerLogarithmicLowerCutoffBudget.clock GaussianFastValueCut.exponent
    exact add_le_add_right _ (add_le_add_right (num 6) (le_of_lt h))
  exact le_congr (by unfold cutoff; ipra_ring) (.eqRefl _) (add_le_add₂ h hc)

theorem ordered_clock_comparison (p q j z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hpq : Γ ⊢[PRAAx] lt p q) : Γ ⊢[PRAAx]
    distanceBounded (observation (clock q) j z R B A (cutoff q j A)) (observation (clock p) j z R B A (cutoff p j A))
      (unit p+unit q) (unit p*unit q) := by
  let s := clock q
  let t := clock p
  let S := unit s
  let U := unit t
  let K := unit (p+num 6)
  have hS := unit_positive (Γ := Γ) s
  have hU := unit_positive (Γ := Γ) t
  have hK := unit_positive (Γ := Γ) (p+num 6)
  have hSU : Γ ⊢[PRAAx] le one (S*U) := positive_product _ _ hS hU
  have hD : Γ ⊢[PRAAx] le one (pairDenominator s t p) := positive_product _ _ hSU hK
  have hUK : Γ ⊢[PRAAx] le U K := GaussianExponentialReference.unit_monotone
    (le_of_eq_add (d := two) (by unfold t clock; ipra_ring))
  have pair := strict_pair_bound s t p j z R B A (cutoff p j A) (cutoff q j A) h (le_refl _)
    (strict_cutoff_increase p q j A hpq)
  have reduced := distance_radius_mono _ _ _ _ (U+num 11*S) (S*U) hD hSU
    (by unfold pairNumerator pairDenominator
        ipra_le (2*𝔞(S)*𝔞(S)*𝔞(U))*sl hUK) pair
  apply distance_radius_mono _ _ _ _ _ _ hSU (positive_product _ _ (unit_positive p) (unit_positive q)) _ reduced
  have ep := natEq (clock_unit (Γ := Γ) p)
  have eq := natEq (clock_unit (Γ := Γ) q)
  refine le_of_eq_add (d := num 240*unit p*unit p*unit q+num 80*unit p*unit q*unit q) ?_
  apply deriveNat
  dsimp only [S,U,s,t]
  ipra_simps
  rw [ep,eq]
  ring

theorem actual_original_logarithmic_cutoff_clock_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 3) (var 4) (var 5) (var 6) ⟶ lt (var 0) (var 1) ⟶
      distanceBounded (observation (clock (var 1)) (var 2) (var 3) (var 4) (var 5) (var 6) (cutoff (var 1) (var 2) (var 6)))
        (observation (clock (var 0)) (var 2) (var 3) (var 4) (var 5) (var 6) (cutoff (var 0) (var 2) (var 6)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 7 (.impI (.impI (ordered_clock_comparison _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicCutoffCauchy
