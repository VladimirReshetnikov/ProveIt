import IPRADerivations.Analysis.GaussianEulerIncompleteDyadicEndpointAlignment
import IPRADerivations.Analysis.GaussianEulerIncompleteFixedCutoff
import IPRADerivations.Analysis.GaussianEulerIncompleteSum

/-!
# Incomplete Gamma as the original lower cutoff tends to zero

At the original dyadic split, the lower cofinal name is observed on
the same physical interval as the checked original lower tail.
The finite error-removal query preserves the exact root coefficient.
The sum identity then gives the corresponding upper convergence.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteDyadicEndpoint

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegralGammaIdentification (source subst_source original_gamma_regular)
open GaussianEulerIncompleteName (lowerF upperF data lower_at upper_at original_regular_names)
open GaussianGammaIntegralCutoffs (etaDen height)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianEulerCutoffCauchyComparison (combined)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product qzero qadd)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianNameEquivalence (cross_at)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator)
open GaussianRationalSlackRemoval (precision slack slack_removal_at)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def splitData (z R B A k : PTm n) : PTm n := data z R B A one (etaDen k A R)

@[simp] theorem subst_splitData {m : ℕ} (σ : Fin n → PTm m) (z R B A k : PTm n) :
    Syn.subst σ (splitData z R B A k) =
      splitData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ k) := by
  simp [splitData,etaDen,height,GaussianGammaIntegralCutoffs.tailCoefficient]

theorem split_source (z R B A k : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] GaussianEulerIncompleteCofinalRate.source z R B A one (etaDen k A R) :=
  .andI h (.andI (le_refl _) (GaussianGammaIntegralCutoffs.eta_den_positive k A R))

private theorem lower_slack (p t z R B A k : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] slack (ap2 lowerF p (splitData z R B A k))
      (A*unit p+unit (height k A R)) (unit (height k A R)*unit p) (num 5) t := by
  let P := unit p
  let U := unit t
  let H := unit (height k A R)
  let E := etaDen k A R
  let C := GaussianEulerIncompleteCutoff.clock t one E
  let j := k+C
  let J := unit (height j A R)
  let K := combined A R
  let D := H*P*U
  let V := ap2 lowerF p (splitData z R B A k)
  let X := ap2 GaussianEulerCompactAdditivity.nameF t (GaussianEulerIncompleteCutoffParts.lowerData z R B j A one E)
  let Y := GaussianEulerNamedLowerTail.point t z R B k j A
  have hP := unit_positive (Γ := Γ) p
  have hU := unit_positive (Γ := Γ) t
  have hH := unit_positive (Γ := Γ) (height k A R)
  have hJ := unit_positive (Γ := Γ) (height j A R)
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ hH hP) hU
  have hj : Γ ⊢[PRAAx] le C j := le_add_left _ _
  have kj : Γ ⊢[PRAAx] le k j := le_add_right _ _
  have later := le_trans (GaussianEulerIncompleteCutoff.clock_later (Γ := Γ) t one E) hj
  have tail := GaussianEulerIncompleteCofinalRate.cutoff_budget t j A R later
  have lc : Γ ⊢[PRAAx] le t (GaussianEulerCutoffCauchyComparison.clock t) := le_add_right _ _
  have tail' : Γ ⊢[PRAAx] le (K*U) J :=
    le_trans (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl K) (GaussianExponentialReference.unit_monotone lc)) tail
  have rates := GaussianEulerIncompleteFixedCutoff.original_cutoff_rates t j z R B A one E (.andI (split_source z R B A k h) hj)
  have first : Γ ⊢[PRAAx] distanceBounded V X ((U+two*P)*H) D :=
    distance_radius_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive J p t hJ) hD
      (by dsimp only [D,P,U,K,H,J,rateNumerator,rateDenominator]
          ipra_le (𝔞(unit (height k A R))*𝔞(unit p)*𝔞(unit p)*𝔞(unit t))*sl tail')
      (rate_at _ _ _ _ _ _ p t rates.andE₁)
  have align := GaussianEulerIncompleteDyadicEndpointAlignment.original_endpoint_alignment z R B A k j (.andI h kj)
  have second : Γ ⊢[PRAAx] distanceBounded X Y (two*H*P) D :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU hU) hD
      (le_of_eq_add (d := zero) (by dsimp only [D]; ipra_ring))
      (cross_at _ _ _ _ t t align)
  have hTail := GaussianEulerNamedLowerTail.lower_observation_bound t z R B k j A (.andI h.andE₁.andE₂.andE₁ h.andE₁) kj
  have td : Γ ⊢[PRAAx] le one (H*U) := positive_product _ _ hH hU
  have last : Γ ⊢[PRAAx] distanceBounded Y qzero ((A*U+H)*P) D :=
    distance_radius_mono _ _ _ _ _ _ td hD
      (le_of_eq_add (d := zero) (by dsimp only [D]; ipra_ring))
      ((GaussianReconstructionRoots.distance_zero_iff _ _ _ td).iffMpr hTail)
  have total := distance_triangle_same V X qzero _ _ D hD first
    (distance_triangle_same X Y qzero _ _ D hD second last)
  exact (GaussianReconstructionRoots.distance_zero_iff _ _ _ hD).iffMp
    (distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [P,U,H,unit]; ipra_ring) (.eqRefl _) total)

theorem original_lower_dyadic_bound (p z R B A k : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] bounded (ap2 lowerF p (splitData z R B A k))
      (A*unit p+unit (height k A R)) (unit (height k A R)*unit p) := by
  let V := ap2 lowerF p (splitData z R B A k)
  let N := A*unit p+unit (height k A R)
  let D := unit (height k A R)*unit p
  let t := precision V N D (num 5)
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive _) (unit_positive _)
  have late : Γ ⊢[PRAAx] slack V N D (num 5) t := lower_slack p t z R B A k h
  exact slack_removal_at V N D (num 5) hD late

theorem original_upper_diagonal_of_lower (t z R B A a b H : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerIncompleteCofinalRate.source z R B A a b)
    (hH : Γ ⊢[PRAAx] le one H)
    (hLower : Γ ⊢[PRAAx] bounded (ap2 lowerF t (data z R B A a b)) (A*unit t+H) (H*unit t)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 upperF t (data z R B A a b)) (ap2 gammaF t (gammaData z R B A))
      (GaussianNamedLipschitzRate.diagonalNumerator A H (num 6) t)
      (GaussianNamedLipschitzRate.diagonalDenominator H t) := by
  let T := unit t
  let D := H*T
  let x := data z R B A a b
  let V := ap2 gammaF t (gammaData z R B A)
  let W := ap2 GaussianEulerIncompleteSum.sumF t (GaussianEulerIncompleteSum.sumData z R B A a b)
  let L := ap2 lowerF t x
  let U := ap2 upperF t x
  have hT := unit_positive (Γ := Γ) t
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hH hT
  have both := original_regular_names z R B A a b h
  have eq := GaussianEulerIncompleteSum.original_Gamma_is_incomplete_sum z R B A a b h
  have first : Γ ⊢[PRAAx] distanceBounded V W (two*H) D :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hT hT) hD
      (le_of_eq_add (d := zero) (by dsimp only [D]; ipra_ring)) (cross_at _ _ _ _ t t eq)
  have separate := GaussianNameRingLaws.add_sample_error lowerF upperF x x t both.andE₁ both.andE₂
  have second : Γ ⊢[PRAAx] distanceBounded W (qadd L U) (num 3*H) D :=
    distance_radius_mono _ _ _ _ _ _ hT hD
      (le_of_eq_add (d := zero) (by dsimp only [D,GaussianNameRingLaws.three]; ipra_ring)) separate
  have lower := (GaussianReconstructionRoots.distance_zero_iff _ _ _ hD).iffMpr hLower
  have same := GaussianRationalPowerDifference.distance_refl_zero (Γ := Γ) U D hD
  have cU : Γ ⊢[PRAAx] GaussianRationalHorner.canonical U :=
    GaussianRationalHorner.canonical_congr (upper_at t z R B A a b)
      (GaussianCompactRiemannName.name_canonical GaussianEulerIntegrandName.evaluatorF _ _ _ _ _ _ _)
  have last : Γ ⊢[PRAAx] distanceBounded (qadd L U) U (A*T+H) D :=
    distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qzero_add _ cU) (by ipra_ring) (.eqRefl _)
      (GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hD lower same)
  exact distance_symmetric _ _ _ _ hD (distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [GaussianNamedLipschitzRate.diagonalNumerator]; ipra_ring) (.eqRefl _)
    (distance_triangle_same V W U _ _ D hD first (distance_triangle_same W (qadd L U) U _ _ D hD second last)))

theorem original_upper_diagonal (t z R B A k : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] distanceBounded (ap2 upperF t (splitData z R B A k)) (ap2 gammaF t (gammaData z R B A))
      (GaussianNamedLipschitzRate.diagonalNumerator A (unit (height k A R)) (num 6) t)
      (GaussianNamedLipschitzRate.diagonalDenominator (unit (height k A R)) t) :=
  original_upper_diagonal_of_lower t z R B A one (etaDen k A R) (unit (height k A R))
    (split_source z R B A k h) (unit_positive _) (original_lower_dyadic_bound t z R B A k h)

theorem original_upper_dyadic_rate (z R B A k : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] independentRate upperF gammaF (splitData z R B A k) (gammaData z R B A) A (unit (height k A R)) := by
  exact GaussianNamedLipschitzRate.independent_rate upperF gammaF (splitData z R B A k) (gammaData z R B A)
    A (unit (height k A R)) (num 6) (unit_positive _)
    (original_regular_names z R B A one (etaDen k A R) (split_source z R B A k h)).andE₂ (original_gamma_regular z R B A h) (by
      refine .allI ?_
      have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) :=
        by simpa only [Fm.shift,Syn.shift,subst_source] using h.shift
      simpa [GaussianNamedLipschitzRate.diagonalEnvelope, Syn.shift, height, GaussianGammaIntegralCutoffs.tailCoefficient]
        using original_upper_diagonal (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift k) hs)

theorem actual_original_lower_incomplete_dyadic_bound_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source (var 1) (var 2) (var 3) (var 4) ⟶ bounded
        (ap2 lowerF (var 0) (splitData (var 1) (var 2) (var 3) (var 4) (var 5)))
        (var 4*unit (var 0)+unit (height (var 5) (var 4) (var 2))) (unit (height (var 5) (var 4) (var 2))*unit (var 0))) :=
  closeUniv 6 (.impI (original_lower_dyadic_bound _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_upper_incomplete_dyadic_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source (var 0) (var 1) (var 2) (var 3) ⟶ independentRate upperF gammaF
        (splitData (var 0) (var 1) (var 2) (var 3) (var 4)) (gammaData (var 0) (var 1) (var 2) (var 3))
        (var 3) (unit (height (var 4) (var 3) (var 1)))) :=
  closeUniv 5 (.impI (original_upper_dyadic_rate _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteDyadicEndpoint
