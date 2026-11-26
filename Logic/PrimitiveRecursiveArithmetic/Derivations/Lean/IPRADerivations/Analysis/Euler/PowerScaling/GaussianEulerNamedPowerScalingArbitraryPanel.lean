import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerPowerScalingArbitraryObservation
import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerNamedPowerScalingImproper

/-!
# Every enclosing physical panel converges to the named Euler value

Choose the physical cutoff before freezing the damping parameters. On
any larger positive rational interval, pay for the fixed compact modulus,
the named Gamma formula, and the inverse-scale radius with one later
parameter query. The returned original compact and formula observations
retain their separate requested clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerNamedPowerScalingArbitraryPanel

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerNamedPowerScalingFormula (source)
open GaussianEulerNamedPowerScalingFormulaFrozen (freezeClock original_frozen_source original_independent_rate)
open GaussianEulerNamedPowerScalingPowerFrozen (powerClock)
open GaussianEulerNamedPowerScalingImproper (scaleBound)
open GaussianEulerPowerChartUniformSchedule (cutoffIndex cutoff_later)
open GaussianEulerPowerChartCofinalSchedule (cutoffSize)
open GaussianEulerPowerChartCofinalEndpoints (lowerDenominator upperNumerator)
open GaussianNamedDampingPowerCompactPaid (parameterClock original_paid_observations)
open GaussianNamedPositiveLogarithm (numerator denominator)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive rate_at)
open GaussianNameEquivalence (point_at)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric distance_triangle_same distance_congr)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent query_budget)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def contains (F G : PR 2) (s z R B A x E T y H J a W D : PTm n) : Fm PTm n :=
  let M := scaleBound F G z R B x E y H
  let V := cutoffSize (cutoffIndex s (J*A) (H*R) H M) (J*A) (H*R)
  le (a*lowerDenominator T V H) D ⋏ le (D*upperNumerator E V H) (a+W)

def panelSource (F G : PR 2) (s z R B A x E T y H J a W D U : PTm n) : Fm PTm n :=
  source F G z R B A x E T y H J ⋏
    ((le one a ⋏ (le one D ⋏ le (a+W) (D*U))) ⋏ contains F G s z R B A x E T y H J a W D)

def frozenIndex (F G : PR 2) (t z R B A x E T y H J D U : PTm n) : PTm n :=
  parameterClock t R T J D U + freezeClock F G t z R B A x E y H J + powerClock F G zero z R B x E y H

private theorem compact_source (F G : PR 2) (s z R B A x E T y H J a W D U : PTm n)
    (hs : Γ ⊢[PRAAx] panelSource F G s z R B A x E T y H J a W D U) : Γ ⊢[PRAAx]
    GaussianNamedDampingPowerCompact.source F G z R B x y E T H J a W D U := by
  have base := hs.andE₁.andE₁.andE₁.andE₁.andE₂.andE₁
  have geom := hs.andE₂.andE₁
  exact .andI (.andI (.andI base.andE₁ (.andI geom.andE₂.andE₁ base.andE₂))
    (.andI geom.andE₁ geom.andE₂.andE₂)) (.andI hs.andE₁.andE₂ hs.andE₁.andE₁.andE₂.andE₂)

private theorem composed (s p t q a b c d e : PTm n)
    (budget : Γ ⊢[PRAAx] le (num 14*unit s) (unit t))
    (h₁ : Γ ⊢[PRAAx] distanceBounded a b (unit p+unit t) (unit p*unit t))
    (h₂ : Γ ⊢[PRAAx] distanceBounded b c (num 9) (unit t))
    (h₃ : Γ ⊢[PRAAx] distanceBounded c d (unit t+two*unit s) (unit s*unit t))
    (h₄ : Γ ⊢[PRAAx] distanceBounded d e (two*unit q+unit t) (unit t*unit q)) : Γ ⊢[PRAAx]
    distanceBounded a e (rateNumerator two (unit s) p q) (rateDenominator (unit s) p q) := by
  let S := unit s
  let P := unit p
  let T := unit t
  let Q := unit q
  let K := S*P*Q*T
  have pos := positive_product (Γ := Γ) _ _
    (denominator_positive S p q (unit_positive s)) (unit_positive t)
  have hs := unit_positive (Γ := Γ) s
  have hp := unit_positive (Γ := Γ) p
  have ht := unit_positive (Γ := Γ) t
  have hq := unit_positive (Γ := Γ) q
  have step₁ : Γ ⊢[PRAAx] distanceBounded a b ((P+T)*S*Q) K :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp ht) pos (le_of_eq_add (d := zero) (by dsimp only [K]; ipra_ring)) h₁
  have step₂ : Γ ⊢[PRAAx] distanceBounded b c (num 9*S*P*Q) K :=
    distance_radius_mono _ _ _ _ _ _ ht pos (le_of_eq_add (d := zero) (by dsimp only [K]; ipra_ring)) h₂
  have step₃ : Γ ⊢[PRAAx] distanceBounded c d ((T+two*S)*P*Q) K :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hs ht) pos (le_of_eq_add (d := zero) (by dsimp only [K]; ipra_ring)) h₃
  have step₄ : Γ ⊢[PRAAx] distanceBounded d e ((two*Q+T)*S*P) K :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ ht hq) pos (le_of_eq_add (d := zero) (by dsimp only [K]; ipra_ring)) h₄
  have raw := distance_triangle_same _ b _ _ _ K pos step₁
    (distance_triangle_same _ c _ _ _ K pos step₂ (distance_triangle_same _ d _ _ _ K pos step₃ step₄))
  refine distance_radius_mono _ _ _ _ _ _ pos (denominator_positive S p q hs) ?_ raw
  unfold rateNumerator rateDenominator
  change Γ ⊢[PRAAx] le (((P+T)*S*Q+(num 9*S*P*Q+((T+two*S)*P*Q+(two*Q+T)*S*P)))*(S*P*Q)) ((two*P*Q+S*(P+Q))*K)
  dsimp only [K]
  ipra_le 𝔞(S*P*P*Q*Q)*sl budget

theorem original_observations (F G : PR 2) (s p q z R B A x E T y H J a W D U : PTm n)
    (hs : Γ ⊢[PRAAx] panelSource F G s z R B A x E T y H J a W D U) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (GaussianNamedDampingPowerCompact.nameF F G) p (GaussianNamedDampingPowerCompact.data z R B x y T J a W D U))
      (ap2 (GaussianEulerNamedPowerScalingFormula.nameF F G) q (GaussianEulerNamedPowerScalingFormula.data F G z R B A x E y H J))
      (rateNumerator two (unit s) p q) (rateDenominator (unit s) p q) := by
  let t := exponent (num 14) s
  let M := scaleBound F G z R B x E y H
  let j := cutoffIndex s (J*A) (H*R) H M
  let k := frozenIndex F G t z R B A x E T y H J D U
  let a₁ := numerator G k y
  let b₁ := denominator G k y
  let a₂ := numerator F k x
  let b₂ := denominator F k x
  let C := parameterClock t R T J D U
  let Z := freezeClock F G t z R B A x E y H J
  let P := powerClock F G zero z R B x E y H
  let U₀ := unit s
  let V₀ := unit t
  let Q₀ := unit q
  let named := GaussianNamedDampingPowerCompact.nameF F G
  let data := GaussianNamedDampingPowerCompact.data z R B x y T J a W D U
  have hk₁ : Γ ⊢[PRAAx] le C k := le_trans (le_add_right C Z) (le_add_right _ _)
  have hk₂ : Γ ⊢[PRAAx] le Z k := le_trans (le_add_left Z C) (le_add_right _ _)
  have hk₃ : Γ ⊢[PRAAx] le P k := le_add_left _ _
  have src := compact_source F G s z R B A x E T y H J a W D U hs
  have reg := GaussianNamedDampingPowerCompact.name_regular F G z R B x y E T H J a W D U src
  have step₁ := point_at named data p t reg
  have fixed := original_paid_observations F G t k z R B x y E T H J a W D U src hk₁
  have step₂ := distance_radius_mono _ _ _ _ (num 9) V₀ (unit_positive _) (unit_positive t)
    (le_congr (mul_comm V₀ (num 9)) (mul_comm (unit (t+num 6)) (num 9))
      (mul_le_mul_right (num 9) (GaussianCompactRiemannName.dyadic_monotone t (t+num 6) (le_add_right _ _)))) fixed
  have params := original_frozen_source F G k z R B A x E T y H J hs.andE₁
  have geom := hs.andE₂.andE₁
  have hsR : Γ ⊢[PRAAx] GaussianEulerPowerScalingGridSchedule.source z R B A a₁ b₁ a₂ b₂ H J T D U a W :=
    .andI params.andE₁ (.andI params.andE₂ (.andI geom.andE₂.andE₁ (.andI geom.andE₁
      (le_congr (.eqRefl _) (mul_comm D U) geom.andE₂.andE₂))))
  have dec := GaussianNamedPositiveLogarithm.decoded_domain F k x E T hs.andE₁.andE₂
  have inv : Γ ⊢[PRAAx] le b₂ (a₂*E) := le_congr (.eqRefl _) (mul_comm E a₂) dec.andE₂.andE₁
  have scaled := GaussianEulerNamedPowerScalingCutoff.frozen_power_bound F G k z R B A x E T y H J hs.andE₁ hk₃
  have atZero := GaussianNamedMultiplyRate.sample_bound_at _ _ _ zero scaled
  have cap := GaussianEulerPowerChartUniformSchedule.scale_bound_from_zero z B a₁ b₁ a₂ b₂ _ atZero
  have cutoff := cutoff_later s z R B A a₁ b₁ a₂ b₂ H J M cap
  have rational := GaussianEulerPowerScalingArbitraryObservation.original_enclosing_observations s j t t z R B A
    a₁ b₁ a₂ b₂ H J T E D U a W hsR hs.andE₁.andE₂.andE₂.andE₁ inv cutoff hs.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₂
  have step₃ := distance_radius_mono _ _ _ _ (V₀+two*U₀) (U₀*V₀) (denominator_positive U₀ t t (unit_positive s))
    (positive_product _ _ (unit_positive s) (unit_positive t))
    (le_of_eq_add (d := zero) (by unfold rateNumerator rateDenominator; ipra_ring)) rational
  have formula := original_independent_rate F G t k z R B A x E T y H J hs.andE₁ hk₂
  have reversed := distance_symmetric _ _ _ _ (denominator_positive V₀ q t (unit_positive t)) (rate_at _ _ _ _ _ _ q t formula)
  have step₄ := distance_radius_mono _ _ _ _ (two*Q₀+V₀) (V₀*Q₀) (denominator_positive V₀ q t (unit_positive t))
    (positive_product _ _ (unit_positive t) (unit_positive q))
    (le_of_eq_add (d := zero) (by unfold rateNumerator rateDenominator; ipra_ring)) reversed
  exact composed s p t q _ _ _ _ _ (query_budget (num 14) s) step₁ step₂ step₃ step₄

theorem actual_original_named_power_damped_Euler_arbitrary_enclosing_panels_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 17
      (panelSource F G (var 0) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11)
        (var 12) (var 13) (var 14) (var 15) (var 16) ⟶
        distanceBounded (ap2 (GaussianNamedDampingPowerCompact.nameF F G) (var 1)
          (GaussianNamedDampingPowerCompact.data (var 3) (var 4) (var 5) (var 7) (var 10) (var 9) (var 12)
            (var 13) (var 14) (var 15) (var 16)))
          (ap2 (GaussianEulerNamedPowerScalingFormula.nameF F G) (var 2)
            (GaussianEulerNamedPowerScalingFormula.data F G (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 10) (var 11) (var 12)))
          (rateNumerator two (unit (var 0)) (var 1) (var 2)) (rateDenominator (unit (var 0)) (var 1) (var 2))) :=
  closeUniv 17 (.impI (original_observations F G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerNamedPowerScalingArbitraryPanel
