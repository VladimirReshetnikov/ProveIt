import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIncompleteName
import IPRADerivations.Analysis.Names.Rates.GaussianNamedLipschitzRate

/-!
# The actual incomplete names at a fixed later cutoff

Compare each original incomplete name with the corresponding original
compact piece at a fixed, independently chosen cutoff. The existing
whole-integral tail coefficient remains in the bound. A finite gap
query removes the temporary observation errors at the auxiliary cutoff.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteFixedCutoff

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIncompleteCofinalRate (source)
open GaussianEulerIncompleteName (lowerF upperF data lower_at upper_at original_observations original_regular_names)
open GaussianEulerIncompleteCutoffParts (lowerData upperData piece_sources)
open GaussianEulerCompactAdditivity (nameF)
open GaussianEulerCutoffCauchyComparison (combined)
open GaussianGammaIntegralCutoffs (height)
open GaussianNamedLipschitzRate (diagonalNumerator diagonalDenominator diagonalEnvelope)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def input (s k z R B A a b : PTm n) : Fm PTm n :=
  source z R B A a b ⋏ le (GaussianEulerIncompleteCutoff.clock s a b) k

@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (s k z R B A a b : PTm n) :
    (input s k z R B A a b).subst σ = input (Syn.subst σ s) (Syn.subst σ k) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ a) (Syn.subst σ b) := by simp [input]

private theorem join_cutoff (t u v K H x y z : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (hu : Γ ⊢[PRAAx] le t u) (hv : Γ ⊢[PRAAx] le t v)
    (h₁ : Γ ⊢[PRAAx] distanceBounded x y (unit t+unit u) (unit t*unit u))
    (h₂ : Γ ⊢[PRAAx] distanceBounded y z (GaussianEulerIncompleteCutoffRate.numerator v t K H)
      (GaussianEulerIncompleteCutoffRate.denominator v t H)) :
    Γ ⊢[PRAAx] distanceBounded x z (diagonalNumerator K H (num 8) t) (diagonalDenominator H t) := by
  let T := unit t
  let D := H*T
  have hT := unit_positive (Γ := Γ) t
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hH hT
  have hp := unit_monotone hu
  have hq := unit_monotone hv
  have first := distance_radius_mono _ _ _ _ (two*H) D (positive_product _ _ hT (unit_positive u)) hD
    (by dsimp only [D, T]; ipra_le (𝔞 H*𝔞(unit t))*sl hp) h₁
  have second := distance_radius_mono _ _ _ _ (K*T+num 6*H) D
    (positive_product _ _ (positive_product _ _ hH (unit_positive v)) hT) hD
    (by dsimp only [D, T, GaussianEulerIncompleteCutoffRate.numerator, GaussianEulerIncompleteCutoffRate.denominator]
        ipra_le (𝔞 H*𝔞 H*𝔞(unit t))*sl hq) h₂
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold diagonalNumerator; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD first second)

theorem original_diagonal_comparison (t s k z R B A a b : PTm n) (h : Γ ⊢[PRAAx] input s k z R B A a b) :
    Γ ⊢[PRAAx]
      distanceBounded (ap2 lowerF t (data z R B A a b)) (ap2 nameF t (lowerData z R B k A a b))
        (diagonalNumerator (combined A R) (unit (height k A R)) (num 8) t) (diagonalDenominator (unit (height k A R)) t) ⋏
      distanceBounded (ap2 upperF t (data z R B A a b)) (ap2 nameF t (upperData z R B k A a b))
        (diagonalNumerator (combined A R) (unit (height k A R)) (num 8) t) (diagonalDenominator (unit (height k A R)) t) := by
  let u := succ k+t
  let j := GaussianEulerIncompleteCutoff.clock u a b
  let v := GaussianEulerCutoffCauchyComparison.clock u
  have hu : Γ ⊢[PRAAx] le t u := le_add_left _ _
  have hv : Γ ⊢[PRAAx] le t v := le_trans hu (le_add_right _ _)
  have hk : Γ ⊢[PRAAx] lt k j := le_trans (le_add_right (succ k) t) (GaussianEulerIncompleteCutoff.clock_later u a b)
  have old := original_observations t u z R B A a b h.andE₁
  have late := GaussianEulerIncompleteCutoffRate.original_cutoff_piece_observations v t s k j z R B A a b
    h.andE₁.andE₁ h.andE₁.andE₂.andE₁ h.andE₁.andE₂.andE₂ h.andE₂ hk
  have l := distance_congr (lower_at u z R B A a b).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) late.andE₁
  have r := distance_congr (upper_at u z R B A a b).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) late.andE₂
  exact .andI (join_cutoff _ _ _ _ _ _ _ _ (unit_positive _) hu hv old.andE₁ l)
    (join_cutoff _ _ _ _ _ _ _ _ (unit_positive _) hu hv old.andE₂ r)

theorem original_cutoff_rates (s k z R B A a b : PTm n) (h : Γ ⊢[PRAAx] input s k z R B A a b) :
    Γ ⊢[PRAAx]
      independentRate lowerF nameF (data z R B A a b) (lowerData z R B k A a b) (combined A R) (unit (height k A R)) ⋏
      independentRate upperF nameF (data z R B A a b) (upperData z R B k A a b) (combined A R) (unit (height k A R)) := by
  let K := combined A R
  let H := unit (height k A R)
  let X := data z R B A a b
  let L := lowerData z R B k A a b
  let U := upperData z R B k A a b
  have source : Γ ⊢[PRAAx] GaussianEulerIncompleteCutoff.source z R B A a b :=
    .andI h.andE₁.andE₁.andE₁.andE₂.andE₁ (.andI h.andE₁.andE₁.andE₁.andE₁ h.andE₁.andE₂)
  have names := original_regular_names z R B A a b h.andE₁
  have compact := piece_sources s k z R B A a b source h.andE₂
  have low := GaussianEulerCompactAdditivity.name_regular _ _ _ _ _ _ _ compact.andE₁
  have high := GaussianEulerCompactAdditivity.name_regular _ _ _ _ _ _ _ compact.andE₂
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift s) (Syn.shift k) (Syn.shift z) (Syn.shift R)
      (Syn.shift B) (Syn.shift A) (Syn.shift a) (Syn.shift b) := by
    simpa only [Fm.shift, Syn.shift, subst_input] using h.shift
  have observations := original_diagonal_comparison (var 0) (Syn.shift s) (Syn.shift k) (Syn.shift z) (Syn.shift R)
    (Syn.shift B) (Syn.shift A) (Syn.shift a) (Syn.shift b) hs
  have lower : Γ ⊢[PRAAx] diagonalEnvelope lowerF nameF X L K H (num 8) := by
    refine .allI ?_
    simpa [diagonalEnvelope, Syn.shift, X, L, K, H, combined, height, GaussianGammaIntegralCutoffs.tailCoefficient] using observations.andE₁
  have upper : Γ ⊢[PRAAx] diagonalEnvelope upperF nameF X U K H (num 8) := by
    refine .allI ?_
    simpa [diagonalEnvelope, Syn.shift, X, U, K, H, combined, height, GaussianGammaIntegralCutoffs.tailCoefficient] using observations.andE₂
  exact .andI
    (GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ _ (unit_positive _) names.andE₁ low lower)
    (GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ _ (unit_positive _) names.andE₂ high upper)

/-- At any later fixed cutoff, a common precision pays for the true tail
and each of the two independent observation errors. -/
theorem original_late_observations (p q t k z R B A a b : PTm n)
    (h : Γ ⊢[PRAAx] input t k z R B A a b)
    (hp : Γ ⊢[PRAAx] le t p) (hq : Γ ⊢[PRAAx] le t q) : Γ ⊢[PRAAx]
    distanceBounded (ap2 lowerF p (data z R B A a b)) (ap2 nameF q (lowerData z R B k A a b)) (num 3) (unit t) ⋏
    distanceBounded (ap2 upperF p (data z R B A a b)) (ap2 nameF q (upperData z R B k A a b)) (num 3) (unit t) := by
  let K := combined A R
  let H := unit (height k A R)
  have kLater := le_trans (GaussianEulerIncompleteCutoff.clock_later (Γ := Γ) t a b) h.andE₂
  have tLater : Γ ⊢[PRAAx] le t (GaussianEulerCutoffCauchyComparison.clock t) := le_add_right _ _
  have tail : Γ ⊢[PRAAx] le (K*unit t) H :=
    le_trans (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl K) (unit_monotone tLater))
      (GaussianEulerIncompleteCofinalRate.cutoff_budget t k A R kLater)
  have up := unit_monotone hp
  have uq := unit_monotone hq
  have clear : Γ ⊢[PRAAx] le (GaussianNamedInverseRate.rateNumerator K H p q*unit t)
      (num 3*GaussianNamedInverseRate.rateDenominator H p q) := by
    unfold GaussianNamedInverseRate.rateNumerator GaussianNamedInverseRate.rateDenominator
    ipra_le (𝔞(unit p)*𝔞(unit q))*sl tail+(𝔞 H*𝔞(unit q))*sl up+(𝔞 H*𝔞(unit p))*sl uq
  have den := GaussianNamedInverseRate.denominator_positive H p q (unit_positive (Γ := Γ) (height k A R))
  have pair := original_cutoff_rates t k z R B A a b h
  exact .andI
    (distance_radius_mono _ _ _ _ _ _ den (unit_positive t) clear (GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q pair.andE₁))
    (distance_radius_mono _ _ _ _ _ _ den (unit_positive t) clear (GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q pair.andE₂))

theorem actual_original_incomplete_names_fixed_cutoff_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
        (independentRate lowerF nameF (data (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
          (lowerData (var 2) (var 3) (var 4) (var 1) (var 5) (var 6) (var 7))
          (combined (var 5) (var 3)) (unit (height (var 1) (var 5) (var 3))) ⋏
         independentRate upperF nameF (data (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
          (upperData (var 2) (var 3) (var 4) (var 1) (var 5) (var 6) (var 7))
          (combined (var 5) (var 3)) (unit (height (var 1) (var 5) (var 3))))) :=
  closeUniv 8 (.impI (original_cutoff_rates _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteFixedCutoff
