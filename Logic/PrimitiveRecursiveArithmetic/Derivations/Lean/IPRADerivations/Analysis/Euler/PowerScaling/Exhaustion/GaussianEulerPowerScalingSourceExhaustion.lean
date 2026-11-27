import IPRADerivations.Analysis.Euler.PowerScaling.Observations.GaussianEulerPowerScalingCofinalObservation

/-!
# Exhaustion of the physical positive half-line by the actual source panels

Each sampling panel at a sufficiently late index contains any given
positive rational interval. The panel is the one sampled by the original
compact power-damped Euler name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingSourceExhaustion

open_ipra
open GaussianEulerPowerScalingCofinalObservation (grid)
open GaussianEulerPowerChartCofinalSchedule (source cutoffSize)
open GaussianEulerPowerChartCofinalEndpoints (lowerDenominator upperNumerator)
open GaussianGammaIntegralCutoffs (height top tailCoefficient)
open GaussianEulerCompactExhaustionScaled (cutoff)
open GaussianFastValueCut (exponent)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def contains (s z R B A e f d h L Q S a b c j : PTm n) : Fm PTm n :=
  let G := grid s z R B A e f d h L Q S
  le b (a*G.lower) ⋏ le c (j*G.upper)

private theorem times_power_later (S V f : PTm n) (hs : Γ ⊢[PRAAx] le one S)
    (hv : Γ ⊢[PRAAx] le one V) (hf : Γ ⊢[PRAAx] le one f) :
    Γ ⊢[PRAAx] le V (pw (S*V) f) := by
  have base : Γ ⊢[PRAAx] le V (S*V) := le_congr (one_mul V) (.eqRefl _) (mul_le_mul_right V hs)
  exact le_trans base (le_congr (pw_one _) (.eqRefl _)
    (GaussianFactorBudget.power_monotone_length (S*V) one f (le_trans hv base) hf))

theorem physical_endpoints_later (s z R B A e f d h L Q S : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S) :
    let G := grid s z R B A e f d h L Q S
    Γ ⊢[PRAAx] le s G.lower ⋏ le s G.upper := by
  dsimp only
  let G := grid s z R B A e f d h L Q S
  let V := cutoffSize G.cutoffIndex (Q*A) (L*R)
  let j := G.cutoffIndex
  have index : Γ ⊢[PRAAx] le s j :=
    le_trans (le_add_right s two) (le_trans (le_succ_self (s+two)) (le_add_right _ _))
  have topIndex : Γ ⊢[PRAAx] le j (top j (Q*A) (L*R)) := by
    unfold top height
    ipra_le 𝔞 j+2*𝔞(Q*A)+2*𝔞(tailCoefficient (L*R))+20
  have guard := GaussianEulerPowerChartCofinalSchedule.cutoff_guards (Γ := Γ) j (Q*A) (L*R)
  have hV : Γ ⊢[PRAAx] le one V := le_trans (le_succ_self one) guard.andE₁
  have growth : Γ ⊢[PRAAx] le s V := le_trans (le_trans index topIndex)
    (le_trans (le_add_right _ _) guard.andE₂.andE₂)
  have hf := hs.andE₂.andE₁.andE₂
  exact .andI (le_trans growth (times_power_later S V f hs.andE₂.andE₂.andE₂.andE₁.andE₂ hV hf))
    (le_trans growth (times_power_later h V f hs.andE₂.andE₂.andE₁.andE₂ hV hf))

theorem original_source_contains (s z R B A e f d h L Q S a b c j : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S)
    (ha : Γ ⊢[PRAAx] le one a) (hj : Γ ⊢[PRAAx] le one j)
    (hbs : Γ ⊢[PRAAx] le b s) (hcs : Γ ⊢[PRAAx] le c s) :
    Γ ⊢[PRAAx] contains s z R B A e f d h L Q S a b c j := by
  let G := grid s z R B A e f d h L Q S
  have ends := physical_endpoints_later s z R B A e f d h L Q S hs
  exact .andI (le_trans (le_trans hbs ends.andE₁)
    (le_congr (one_mul G.lower) (.eqRefl _) (mul_le_mul_right G.lower ha)))
    (le_trans (le_trans hcs ends.andE₂)
      (le_congr (one_mul G.upper) (.eqRefl _) (mul_le_mul_right G.upper hj)))

theorem actual_power_damped_source_panels_exhaust_positive_times_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 16
      ((source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) ⋏
        ((le one (var 12) ⋏ le one (var 15)) ⋏ (le (var 13) (var 0) ⋏ le (var 14) (var 0)))) ⟶
        contains (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10)
          (var 11) (var 12) (var 13) (var 14) (var 15)) :=
  closeUniv 16 (.impI (original_source_contains _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁.andE₁ Prf.hyp0.andE₂.andE₁.andE₂
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingSourceExhaustion
