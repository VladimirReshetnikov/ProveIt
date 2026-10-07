import OAI.Combinatorics.Progressions.Estimates.SelectedWindowIndicator
import OAI.Combinatorics.Progressions.Geometry.SupportedFiberApproximation

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory
open scoped BigOperators Classical

theorem toPMF_bind_zero_component {Ω X : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (K : Ω → PMF X) (a : Ω)
    (ha : p.weight a ≠ 0) (x : X) (hx : p.toPMF.bind K x = 0) : K a x = 0 := by
  by_contra hk
  have hp : p.toPMF a ≠ 0 := by
    intro h
    apply ha
    rw [← p.toPMF_toReal a, h, ENNReal.toReal_zero]
  exact ((PMF.mem_support_bind_iff p.toPMF K x).mpr ⟨a, hp, hk⟩) hx

theorem conditional_window_weighted_integral_error
    {Ω R X Y : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype R] [DecidableEq R]
    [Countable X] [DecidableEq X] [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y]
    (p : FiniteProbabilityWeights Ω) (F : Ω → R) (K : Ω → PMF X)
    (W : Finset X) (g : R → X → ℂ) (μ : Measure Y) (z : Y → X) (w : R → Y → ℂ)
    (hz : Measurable z) {N ε : ℝ} (hN : 0 < N)
    (hw : ∀ r, Measurable (w r))
    (hzero : ∀ r (hr : 0 < p.mass (Finset.univ.filter (fun a => F a = r))) x,
      x ∉ W → ((p.condition _ hr).toPMF.bind K x = 0 ∧ g r x = 0))
    (he : ∀ r (hr : 0 < p.mass (Finset.univ.filter (fun a => F a = r))) x,
      ‖(N : ℂ) * (((p.condition _ hr).toPMF.bind K x).toReal : ℂ) - g r x‖ ≤ ε)
    (hweight : ∀ r, 0 < p.mass (Finset.univ.filter (fun a => F a = r)) →
      Integrable (fun y => if z y ∈ W then ‖w r y‖ else 0) μ) :
    ‖p.complexMean (fun a => ∫ y, w (F a) y * ((K a (z y)).toReal : ℂ) ∂μ) -
      (p.fiberLaw F).complexMean (fun r => ∫ y, w r y * g r (z y) ∂μ) / (N : ℂ)‖ ≤
      (ε / N) * (p.fiberLaw F).mean (fun r => ∫ y, if z y ∈ W then ‖w r y‖ else 0 ∂μ) := by
  have hdiv : (p.fiberLaw F).complexMean
      (fun r => (∫ y, w r y * g r (z y) ∂μ) / (N : ℂ)) =
      (p.fiberLaw F).complexMean (fun r => ∫ y, w r y * g r (z y) ∂μ) / (N : ℂ) := by
    simp only [complexMean, Finset.sum_div, mul_div_assoc]
  rw [← hdiv, ← (p.fiberLaw F).mean_const_mul]
  apply p.complexMean_supported_fiber_variable_error F
  intro r hr
  let c : FiniteProbabilityWeights Ω := p.condition (Finset.univ.filter (fun a => F a = r)) hr
  have hi (a : Ω) (ha : c.weight a ≠ 0) :
      Integrable (fun y => w r y * ((K a (z y)).toReal : ℂ)) μ := by
    apply finite_window_weighted_integrable W (fun x => ((K a x).toReal : ℂ)) μ z (w r) hz (hw r)
    · intro x hx
      rw [c.toPMF_bind_zero_component K a ha x (hzero r hr x hx).1,
        ENNReal.toReal_zero, Complex.ofReal_zero]
    · exact hweight r hr
  have hsplit : c.complexMean (fun a => ∫ y, w (F a) y * ((K a (z y)).toReal : ℂ) ∂μ) =
      ∫ y, w r y * ((c.toPMF.bind K (z y)).toReal : ℂ) ∂μ := by
    calc
      _ = c.complexMean (fun a => ∫ y, w r y * ((K a (z y)).toReal : ℂ) ∂μ) := by
        apply c.complexMean_congr_support
        intro a ha
        have har : F a = r := (Finset.mem_filter.mp (condition_weight_support p _ hr a ha).1).2
        rw [har]
      _ = ∫ y, c.complexMean (fun a => w r y * ((K a (z y)).toReal : ℂ)) ∂μ :=
        (c.integral_complexMean_of_support μ _ hi).symm
      _ = _ := by
        apply integral_congr_ae
        apply ae_of_all
        intro y
        change c.complexMean (fun a => w r y * ((K a (z y)).toReal : ℂ)) =
          w r y * ((c.toPMF.bind K (z y)).toReal : ℂ)
        rw [c.complexMean_mul_left, c.complexMean_ofReal, ← c.toPMF_bind_toReal]
  rw [hsplit]
  apply finite_window_weighted_integral_error W
    (fun x => ((c.toPMF.bind K x).toReal : ℂ)) (g r) μ z (w r) hz (hw r) hN
  · intro x hx
    refine ⟨?_, (hzero r hr x hx).2⟩
    rw [(hzero r hr x hx).1, ENNReal.toReal_zero, Complex.ofReal_zero]
  · exact he r hr
  · exact hweight r hr

end Erdos3.FiniteProbabilityWeights

end

end OAI
