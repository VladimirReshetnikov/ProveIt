import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeIntervalStepCoefficient
import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeIntervalInverseBound
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaNegativeIntervalInverseRecurrence
import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeProductDerivativeInverseRate

/-!
# The reciprocal shift-product difference at the original unit step

Both finite coefficients are original pole multipliers. Their exact
inverse identities compute the divided difference. Uniform bounds on
them preserve convergence to the original correction.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalInverseStepCoefficient

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode)
open GaussianGammaNegativeCriticalCorrection (guard correction)
open GaussianGammaNegativeIntervalInverseBound (base_bound neighbor_bound literal_inverse)
open GaussianGammaNegativeIntervalInverseRecurrence (inverse correctionFactor)
open GaussianGammaNegativeIntervalRescale (original_product_rescale guard_rescale)
open GaussianGammaNegativeIntervalStep (numerator denominator neighbor_guard denominator_positive)
open GaussianGammaNegativeIntervalStepCoefficient (finiteCoefficient exact_product_step step_bound neighborProduct)
open GaussianGammaNegativeIntervalNative (product)
open GaussianGammaNegativeProductDerivativeInverse (inverseCoefficient inverse_coefficient_difference)
open GaussianGammaNegativeProductDerivativeInverseRate (inverseGapCost inverseRateCost original_inverse_gap_bound original_inverse_coefficient_rate)
open GaussianRationalHorner (ofGaussian qmul canonical qmul_canonical)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalSyntheticDivision (qmul_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def neighborInverse (a b N D : PTm n) : PTm n := inverse (numerator a b D) (denominator b D) N
def finiteInverseCoefficient (a b N D : PTm n) : PTm n :=
  inverseCoefficient (neighborInverse a b N D) (inverse a b N) (finiteCoefficient a b N D)
def inverseCap (b : PTm n) : PTm n := two*(b*b)

theorem step_inside (a b D : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hr : Γ ⊢[PRAAx] le (two*b) D) :
    Γ ⊢[PRAAx] lt b D := by
  have hb := le_trans h.andE₁ (le_of_lt h.andE₂)
  exact le_trans (by ipra_le sl hb) hr

private theorem inverse_canonical (a b N : PTm n) : Γ ⊢[PRAAx] canonical (inverse a b N) :=
  qmul_canonical _ _

theorem exact_inverse_step (a b N D : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hr : Γ ⊢[PRAAx] le (two*b) D) :
    Γ ⊢[PRAAx] qsub (neighborInverse a b N D) (inverse a b N) ≐ qmul (ofGaussian oneCode D) (finiteInverseCoefficient a b N D) := by
  have hd := step_inside a b D h hr
  exact inverse_coefficient_difference (neighborProduct a b N D) (product a b N) _ _ _ _
    (inverse_canonical _ _ _) (inverse_canonical _ _ _)
    (literal_inverse _ _ _ (neighbor_guard a b D h hd)) (literal_inverse a b N h) (exact_product_step a b N D h hd)

theorem next_inverse_bound (a b N D : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hr : Γ ⊢[PRAAx] le (two*b) D) :
    Γ ⊢[PRAAx] bounded (neighborInverse a b N D) (inverseCap b) one :=
  neighbor_bound a b N D h hr

private theorem base_inverse_bound (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] bounded (inverse a b N) (inverseCap b) one := by
  apply GaussianCoefficientNameBounds.bounded_radius_mono (inverse a b N) (b*b) one (inverseCap b) one
    (le_refl one) (le_refl one)
  · unfold inverseCap
    ipra_le 𝔞(b)*𝔞(b)
  · exact base_bound a b N h

theorem coefficient_rates (a b N D : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hr : Γ ⊢[PRAAx] le (two*b) D) : Γ ⊢[PRAAx]
    distanceBounded (neighborInverse a b N D) (inverse a b N) (inverseGapCost (succ N) (inverseCap b)) D ⋏
    distanceBounded (finiteInverseCoefficient a b N D) (correctionFactor a b N) (inverseRateCost (succ N) (inverseCap b)) D := by
  let A := D*a
  let B := denominator b D
  let C := numerator a b D
  let c₀ := inverse a b N
  let c₁ := neighborInverse a b N D
  let H := inverseCap b
  have hinside := step_inside a b D h hr
  have hD := denominator_positive h hinside
  have hb := le_trans h.andE₁ (le_of_lt h.andE₂)
  have hBase := guard_rescale a b D h hD
  have hNext := neighbor_guard a b D h hinside
  have hc₀ : Γ ⊢[PRAAx] canonical c₀ := inverse_canonical _ _ _
  have hc₁ : Γ ⊢[PRAAx] canonical c₁ := inverse_canonical _ _ _
  have hi₀ : Γ ⊢[PRAAx] qmul (product A B N) c₀ ≐ GaussianRationalSyntheticDivision.qone :=
    (qmul_congr (original_product_rescale a b D N h hD) (.eqRefl _)).eqTrans (literal_inverse a b N h)
  have hi₁ := literal_inverse C B N hNext
  have hb₀ := base_inverse_bound a b N h
  have hb₁ := next_inverse_bound a b N D h hr
  have hstep := step_bound a b D hb hD
  have gap := original_inverse_gap_bound A C B N c₁ c₀ H one D
    hBase hNext hc₁ hc₀ hi₁ hi₀ hb₁ hb₀ hD hstep
  have rate := original_inverse_coefficient_rate A C B N c₁ c₀ H one D
    hBase hNext hc₁ hc₀ hi₁ hi₀ hb₁ hb₀ hD hstep
  have same := GaussianGammaNegativeCriticalRescale.correction_rescale a b N D h hD
  exact .andI (distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) gap)
    (distance_congr (.eqRefl _) (qmul_congr (.eqRefl _) same) (by ipra_ring) (.eqRefl _) rate)

theorem actual_original_negative_Gamma_inverse_step_coefficients_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((guard (var 0) (var 1) ⋏ le (two*var 1) (var 3)) ⟶
        distanceBounded (neighborInverse (var 0) (var 1) (var 2) (var 3)) (inverse (var 0) (var 1) (var 2))
          (inverseGapCost (succ (var 2)) (inverseCap (var 1))) (var 3) ⋏
        distanceBounded (finiteInverseCoefficient (var 0) (var 1) (var 2) (var 3)) (correctionFactor (var 0) (var 1) (var 2))
          (inverseRateCost (succ (var 2)) (inverseCap (var 1))) (var 3)) :=
  closeUniv 4 (.impI (coefficient_rates _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalInverseStepCoefficient
