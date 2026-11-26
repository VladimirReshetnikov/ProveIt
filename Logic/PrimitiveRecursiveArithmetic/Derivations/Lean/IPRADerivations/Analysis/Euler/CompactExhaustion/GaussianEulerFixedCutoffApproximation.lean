import IPRADerivations.Analysis.Euler.GaussianEulerImproperName
import IPRADerivations.Analysis.Names.Rates.GaussianNamedLipschitzRate

/-!
# Exact approximation by any original fixed Euler cutoff

The actual later cutoff t+k is used to compare the returned varying
name with the unchanged original fixed-cutoff name. Both requested
observation errors are preserved. Only the auxiliary finite errors are
removed by the existing genuine integer-gap precision. No approximation,
limit, or independent output law is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerFixedCutoffApproximation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerCutoffCauchyComparison (input combined oldData observation clock pairNumerator pairDenominator)
open GaussianEulerVaryingCutoffName (nameF data)
open GaussianGammaIntegralCutoffs (height)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- One genuinely cofinal cutoff suffices for each fixed precision t.
The diagonal error is combined/H_k +12*eps_t. -/
theorem diagonal_at (t z R B A k : PTm n) (h : Γ ⊢[PRAAx] input z R B A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF t (data z R B A)) (observation t z R B k A)
      (diagonalNumerator (combined A R) (unit (height k A R)) (num 12) t)
      (diagonalDenominator (unit (height k A R)) t) := by
  let j := t+k
  let H := unit (height k A R)
  let U := unit t
  let D := H*U
  have htj : Γ ⊢[PRAAx] le t j := le_add_right t k
  have hkj : Γ ⊢[PRAAx] le k j := le_add_left k t
  have hjc : Γ ⊢[PRAAx] le t (clock j) := le_trans htj (le_add_right _ _)
  have uj := GaussianExponentialReference.unit_monotone htj
  have uc := GaussianExponentialReference.unit_monotone hjc
  have hH := unit_positive (Γ := Γ) (height k A R)
  have hU := unit_positive (Γ := Γ) t
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hH hU
  have near := GaussianNameEquivalence.point_at nameF (data z R B A) t j
    (GaussianEulerVaryingCutoffName.conditional_name_regular z R B A h)
  have firstBudget : Γ ⊢[PRAAx] le ((unit t+unit j)*D) ((two*H)*(unit t*unit j)) :=
    le_congr (by dsimp only [D,H,U]; ipra_ring) (by dsimp only [D,H,U]; ipra_ring)
      (add_le_add_right (H*U*unit j) (mul_le_mul_right (H*U) uj))
  have first := distance_radius_mono _ _ _ _ (two*H) D
    (positive_product _ _ hU (unit_positive j)) hD firstBudget near
  have raw := GaussianEulerCutoffCauchyComparison.pair_bound (clock j) t z R B k j A h hkj
  have big : Γ ⊢[PRAAx] le one (pairDenominator (clock j) t k A R) :=
    positive_product _ _ (positive_product _ _ hH (unit_positive _)) hU
  have secondBudget : Γ ⊢[PRAAx] le (pairNumerator (clock j) t k A R*D)
      ((combined A R*U+num 10*H)*pairDenominator (clock j) t k A R) :=
    le_congr (by dsimp only [pairNumerator,D,H,U]; ipra_ring) (by dsimp only [pairDenominator,D,H,U]; ipra_ring)
      (add_le_add_right (combined A R*H*unit (clock j)*U*U+num 9*H*H*unit (clock j)*U)
        (mul_le_mul_right (H*H*U) uc))
  have second := distance_congr (GaussianEulerVaryingCutoffName.name_at j z R B A).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ (combined A R*U+num 10*H) D big hD secondBudget raw)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [diagonalNumerator,H,U]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD first second)

theorem diagonal_bound (z R B A k : PTm n) (h : Γ ⊢[PRAAx] input z R B A) : Γ ⊢[PRAAx]
    diagonalEnvelope nameF GaussianGammaEulerCompactQuadrature.nameF (data z R B A) (oldData z R B k A)
      (combined A R) (unit (height k A R)) (num 12) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa [diagonalEnvelope,diagonalNumerator,diagonalDenominator,observation,combined,height,
      GaussianGammaIntegralCutoffs.tailCoefficient,Products.fact,GaussianGammaEulerCompactQuadrature.nameF,
      GaussianEulerCompactModulus.nameF,GaussianEulerCompactAdditivity.nameF,Syn.shift] using
    diagonal_at (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift k) hs

/-- Every requested pair of observations retains its exact ordinary
errors. Only the fourteen auxiliary dyadic errors are removed. -/
theorem conditional_fixed_cutoff_rate (z R B A k : PTm n) (h : Γ ⊢[PRAAx] input z R B A) : Γ ⊢[PRAAx]
    independentRate nameF GaussianGammaEulerCompactQuadrature.nameF (data z R B A) (oldData z R B k A)
      (combined A R) (unit (height k A R)) :=
  GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ (num 12) (unit_positive _)
    (GaussianEulerVaryingCutoffName.conditional_name_regular z R B A h)
    (GaussianGammaEulerCompactQuadrature.fixed_interval_regular z R B k A h.andE₁) (diagonal_bound z R B A k h)

theorem conditional_observations (p q z R B A k : PTm n) (h : Γ ⊢[PRAAx] input z R B A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B A)) (observation q z R B k A)
      (rateNumerator (combined A R) (unit (height k A R)) p q)
      (rateDenominator (unit (height k A R)) p q) :=
  GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q (conditional_fixed_cutoff_rate z R B A k h)

/-- Original numerical input guards discharge all prior tail hypotheses. -/
theorem original_fixed_cutoff_rate (z R B A k : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerImproperName.source z R B A) : Γ ⊢[PRAAx]
    independentRate nameF GaussianGammaEulerCompactQuadrature.nameF (data z R B A) (oldData z R B k A)
      (combined A R) (unit (height k A R)) :=
  conditional_fixed_cutoff_rate z R B A k (GaussianEulerImproperName.cauchy_input z R B A h)

theorem original_observations (p q z R B A k : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerImproperName.source z R B A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B A)) (observation q z R B k A)
      (rateNumerator (combined A R) (unit (height k A R)) p q)
      (rateDenominator (unit (height k A R)) p q) :=
  GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q (original_fixed_cutoff_rate z R B A k h)

theorem actual_cofinal_fixed_cutoff_diagonal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 1) (var 2) (var 3) (var 4) ⟶ distanceBounded
      (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4)))
      (observation (var 0) (var 1) (var 2) (var 3) (var 5) (var 4))
      (diagonalNumerator (combined (var 4) (var 2)) (unit (height (var 5) (var 4) (var 2))) (num 12) (var 0))
      (diagonalDenominator (unit (height (var 5) (var 4) (var 2))) (var 0))) :=
  closeUniv 6 (.impI (diagonal_at _ _ _ _ _ _ Prf.hyp0))
theorem source_only_original_fixed_Euler_cutoff_approximation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianEulerImproperName.source (var 0) (var 1) (var 2) (var 3) ⟶
      independentRate nameF GaussianGammaEulerCompactQuadrature.nameF (data (var 0) (var 1) (var 2) (var 3))
        (oldData (var 0) (var 1) (var 2) (var 4) (var 3))
        (combined (var 3) (var 1)) (unit (height (var 4) (var 3) (var 1)))) :=
  closeUniv 5 (.impI (original_fixed_cutoff_rate _ _ _ _ _ Prf.hyp0))
theorem source_only_original_fixed_Euler_cutoff_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (GaussianEulerImproperName.source (var 2) (var 3) (var 4) (var 5) ⟶ distanceBounded
      (ap2 nameF (var 0) (data (var 2) (var 3) (var 4) (var 5)))
      (observation (var 1) (var 2) (var 3) (var 4) (var 6) (var 5))
      (rateNumerator (combined (var 5) (var 3)) (unit (height (var 6) (var 5) (var 3))) (var 0) (var 1))
      (rateDenominator (unit (height (var 6) (var 5) (var 3))) (var 0) (var 1))) :=
  closeUniv 7 (.impI (original_observations _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerFixedCutoffApproximation
