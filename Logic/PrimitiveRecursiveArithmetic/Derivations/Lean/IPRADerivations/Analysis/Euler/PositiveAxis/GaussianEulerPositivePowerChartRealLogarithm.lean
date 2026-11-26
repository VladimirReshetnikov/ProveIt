import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerPositivePowerChartLogarithm
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerPositivePowerChartOrder
import IPRADerivations.Analysis.Exponential.GaussianRealNameExponentialInjectivity

/-!
# A uniform real disk for the original power-chart logarithm

The logged chart coordinate is exactly real at every observation. A
uniform disk follows from the original compact logarithm bounds for
t and d/h and the upper bound on e/f.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartRealLogarithm

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPositivePowerChart (argument source)
open GaussianEulerPositivePowerChartLogarithm (logarithmF logarithmData logarithm_regular)
open GaussianEulerIntegrandName (powerExponentF powerExponentData power_exponent_at powerClock)
open GaussianPositiveRationalLogarithm (logF fraction)
open GaussianRationalHorner (qadd qmul qadd_canonical)
open GaussianRationalMetric (bounded)
open RationalGaussianEmbedding (axis axis_congr axis_add axis_multiply)
open GaussianRationalReciprocal (bound_congr bounded_sum bounded_product)
open GaussianRadiusExponentialName (input boundedSamples)
open GaussianRealNameExponentialInjectivity (axisSamples)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def disk (h Q S E T : PTm n) : PTm n :=
  GaussianCompactLogarithmBounds.radius h S+Q*GaussianCompactLogarithmBounds.radius E T

@[simp] theorem subst_disk {m : ℕ} (σ : Fin n → PTm m) (h Q S E T : PTm n) :
    Syn.subst σ (disk h Q S E T) = disk (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ S)
      (Syn.subst σ E) (Syn.subst σ T) := by simp [disk,GaussianCompactLogarithmBounds.radius]

theorem sample_at (p e f d h a b : PTm n) : Γ ⊢[PRAAx] ap2 logarithmF p (logarithmData e f d h a b) ≐
    qadd (GaussianPositiveRationalLogarithm.sample (GaussianFastValueCut.exponent two p) d h)
      (ap2 powerExponentF (GaussianFastValueCut.exponent two p) (powerExponentData (argument e f) f a b)) :=
  (GaussianNameArithmetic.add_at logF powerExponentF _ _ p).eqTrans
    (GaussianExponentialReference.recode_fixed _ (qadd_canonical _ _))

theorem power_exponent_at_ratio (p e f a b : PTm n) (hf : Γ ⊢[PRAAx] le one f) :
    Γ ⊢[PRAAx] ap2 powerExponentF p (powerExponentData (argument e f) f a b) ≐
      qmul (fraction e f) (GaussianPositiveRationalLogarithm.sample (powerClock p (argument e f) f a b) a b) :=
  (power_exponent_at p (argument e f) f a b).eqTrans (GaussianRationalSyntheticDivision.qmul_congr
    (GaussianEulerPositivePowerChart.coefficient_exact e f hf) (.eqRefl _))

theorem sample_real (p e f d h a b : PTm n) (hf : Γ ⊢[PRAAx] le one f) :
    Γ ⊢[PRAAx] axis (ap2 logarithmF p (logarithmData e f d h a b)) := by
  let k := GaussianFastValueCut.exponent two p
  let j := powerClock k (argument e f) f a b
  have hr : Γ ⊢[PRAAx] axis (fraction e f) := (GaussianEulerPositivePowerChartOrder.fraction_positive e f hf).andE₁
  have right := axis_congr (power_exponent_at_ratio k e f a b hf).eqSymm
    (axis_multiply (fraction e f) (GaussianPositiveRationalLogarithm.sample j a b) hr
      (GaussianPositiveRationalLogarithm.sample_axis j a b))
  exact axis_congr (sample_at p e f d h a b).eqSymm
    (axis_add _ _ (GaussianPositiveRationalLogarithm.sample_axis k d h) right)

theorem sample_bound (p e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) :
    Γ ⊢[PRAAx] bounded (ap2 logarithmF p (logarithmData e f d h a b)) (disk h Q S E T) one := by
  let k := GaussianFastValueCut.exponent two p
  let j := powerClock k (argument e f) f a b
  have scalePositive := hs.andE₁.andE₂.andE₁
  have scaleDomain : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain d h h S :=
    .andI scalePositive (.andI
      (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right h scalePositive.andE₁))
      hs.andE₁.andE₂.andE₂.andE₂.andE₂)
  have rr := GaussianEulerPositivePowerChartOrder.coefficient_bound e f Q hs.andE₁.andE₁.andE₂
    hs.andE₁.andE₂.andE₂.andE₂.andE₁
  have left := GaussianCompactLogarithmBounds.sample_bound k d h h S scalePositive.andE₂ scaleDomain
  have right := GaussianCompactLogarithmBounds.sample_bound j a b E T hs.andE₂.andE₁ hs.andE₂.andE₂
  have prod : Γ ⊢[PRAAx] bounded (ap2 powerExponentF k (powerExponentData (argument e f) f a b))
      (Q*GaussianCompactLogarithmBounds.radius E T) one :=
    bound_congr (power_exponent_at_ratio k e f a b hs.andE₁.andE₁.andE₂).eqSymm (.eqRefl _) (by ipra_ring)
    (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) rr right)
  exact bound_congr (sample_at p e f d h a b).eqSymm (by unfold disk; ipra_ring) (by ipra_ring)
    (bounded_sum _ _ _ _ _ _ (le_refl one) (le_refl one) left prod)

theorem real_samples (e f d h a b : PTm n) (hf : Γ ⊢[PRAAx] le one f) :
    Γ ⊢[PRAAx] axisSamples logarithmF (logarithmData e f d h a b) := by
  refine .allI ?_
  have fs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift f) := by
    simpa [Fm.shift,Syn.shift,one] using hf.shift
  simpa only [axisSamples,GaussianEulerPositivePowerChartLogarithm.subst_logarithmData,Syn.shift] using
    sample_real (var 0) (Syn.shift e) (Syn.shift f) (Syn.shift d) (Syn.shift h) (Syn.shift a) (Syn.shift b) fs

theorem original_input (e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) :
    Γ ⊢[PRAAx] input logarithmF (disk h Q S E T) (logarithmData e f d h a b) := by
  refine .andI (logarithm_regular e f d h Q S E T a b hs) (.allI ?_)
  have ss : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift e) (Syn.shift f) (Syn.shift d) (Syn.shift h)
      (Syn.shift Q) (Syn.shift S) (Syn.shift E) (Syn.shift T) (Syn.shift a) (Syn.shift b) := by
    simpa only [Fm.shift,GaussianEulerPositivePowerChart.subst_source,Syn.shift] using hs.shift
  simpa only [boundedSamples,subst_disk,GaussianEulerPositivePowerChartLogarithm.subst_logarithmData,Syn.shift] using
    sample_bound (var 0) (Syn.shift e) (Syn.shift f) (Syn.shift d) (Syn.shift h)
      (Syn.shift Q) (Syn.shift S) (Syn.shift E) (Syn.shift T) (Syn.shift a) (Syn.shift b) ss

theorem actual_original_power_chart_logarithm_is_real_and_bounded_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
        (axisSamples logarithmF (logarithmData (var 0) (var 1) (var 2) (var 3) (var 8) (var 9)) ⋏
          input logarithmF (disk (var 3) (var 4) (var 5) (var 6) (var 7))
            (logarithmData (var 0) (var 1) (var 2) (var 3) (var 8) (var 9)))) :=
  closeUniv 10 (.impI (.andI (real_samples _ _ _ _ _ _ Prf.hyp0.andE₁.andE₁.andE₂)
    (original_input _ _ _ _ _ _ _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartRealLogarithm
