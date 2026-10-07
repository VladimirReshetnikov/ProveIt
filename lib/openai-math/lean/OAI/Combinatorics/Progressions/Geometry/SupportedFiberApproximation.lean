/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.FiniteGoodPartTransfer
import OAI.Combinatorics.Progressions.Probability.WeightedSupportedComplexMixture

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory
open scoped BigOperators

variable {X Y : Type*} [Fintype X] [MeasurableSpace Y]

theorem complexMean_integrable_of_support (p : FiniteProbabilityWeights X)
    (μ : Measure Y) (f : Y → X → ℂ)
    (hf : ∀ x, p.weight x ≠ 0 → Integrable (fun y => f y x) μ) :
    Integrable (fun y => p.complexMean (f y)) μ := by
  apply integrable_finsetSum
  intro x _
  by_cases hx : p.weight x = 0
  · simp only [hx, Complex.ofReal_zero, zero_mul, integrable_fun_zero]
  · exact (hf x hx).const_mul (p.weight x : ℂ)

theorem integral_complexMean_of_support (p : FiniteProbabilityWeights X)
    (μ : Measure Y) (f : Y → X → ℂ)
    (hf : ∀ x, p.weight x ≠ 0 → Integrable (fun y => f y x) μ) :
    (∫ y, p.complexMean (f y) ∂μ) = p.complexMean (fun x => ∫ y, f y x ∂μ) := by
  have hi (x : X) : Integrable (fun y => (p.weight x : ℂ) * f y x) μ := by
    by_cases hx : p.weight x = 0
    · simp only [hx, Complex.ofReal_zero, zero_mul, integrable_fun_zero]
    · exact (hf x hx).const_mul (p.weight x : ℂ)
  unfold complexMean
  rw [integral_finsetSum _ (fun x _ => hi x)]
  simp only [integral_const_mul]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory
open scoped BigOperators Classical

variable {X R Y : Type*} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]
variable [MeasurableSpace Y]

theorem complexMean_supported_fiber_l1_error (p : FiniteProbabilityWeights X) (F : X → R)
    (μ : Measure Y) (f : X → Y → ℂ) (target : R → Y → ℂ) (ε : R → ℝ)
    (he : ∀ r (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))),
      Integrable (fun y => (p.condition _ hr).complexMean (fun x => f x y) - target r y) μ ∧
      (∫ y, ‖(p.condition _ hr).complexMean (fun x => f x y) - target r y‖ ∂μ) ≤ ε r) :
    Integrable (fun y => p.complexMean (fun x => f x y) - (p.fiberLaw F).complexMean (fun r => target r y)) μ ∧
      (∫ y, ‖p.complexMean (fun x => f x y) - (p.fiberLaw F).complexMean (fun r => target r y)‖ ∂μ) ≤
        (p.fiberLaw F).mean ε := by
  let w := p.fiberLaw F
  let D (r : R) (y : Y) : ℂ := p.fiberComplexMean F r (fun x => f x y) - (w.weight r : ℂ) * target r y
  have hD (r : R) : Integrable (D r) μ ∧ (∫ y, ‖D r y‖ ∂μ) ≤ w.weight r * ε r := by
    by_cases hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))
    · have hw : w.weight r = p.mass (Finset.univ.filter (fun x => F x = r)) :=
        p.fiberLaw_weight_eq_mass F r
      have hEq : D r = fun y => (w.weight r : ℂ) *
          ((p.condition _ hr).complexMean (fun x => f x y) - target r y) := by
        funext y
        dsimp only [D]
        rw [p.fiberComplexMean_eq_condition F r _ hr, ← hw, mul_sub]
      rw [hEq]
      refine ⟨(he r hr).1.const_mul (w.weight r : ℂ), ?_⟩
      simp_rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (w.nonneg r)]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (he r hr).2 (w.nonneg r)
    · have hz : w.weight r = 0 := by
        rw [p.fiberLaw_weight_eq_mass]
        exact le_antisymm (le_of_not_gt hr) (p.mass_nonneg _)
      have hEq : D r = fun _ => 0 := by
        funext y
        dsimp only [D]
        rw [p.fiberComplexMean_zero F r hz, hz, Complex.ofReal_zero, zero_mul, sub_zero]
      rw [hEq]
      constructor
      · exact integrable_fun_zero Y ℂ μ
      · simp only [norm_zero, integral_zero, hz, zero_mul, le_refl]
  have hEq : (fun y => p.complexMean (fun x => f x y) - w.complexMean (fun r => target r y)) =
      (fun y => ∑ r, D r y) := by
    funext y
    have hs : p.complexMean (fun x => f x y) = ∑ r, p.fiberComplexMean F r (fun x => f x y) := by
      simpa only [Finset.mem_univ, ite_true] using
        (p.sum_fiberComplexMean_on F Finset.univ (fun x => f x y)).symm
    rw [hs]
    change (∑ r, p.fiberComplexMean F r (fun x => f x y)) -
      (∑ r, (w.weight r : ℂ) * target r y) = ∑ r, D r y
    rw [← Finset.sum_sub_distrib]
  change Integrable (fun y => p.complexMean (fun x => f x y) - w.complexMean (fun r => target r y)) μ ∧
    (∫ y, ‖p.complexMean (fun x => f x y) - w.complexMean (fun r => target r y)‖ ∂μ) ≤ w.mean ε
  have hpoint (y : Y) := congrFun hEq y
  simp_rw [hpoint]
  have hi : Integrable (fun y => ∑ r, D r y) μ := integrable_finsetSum _ (fun r _ => (hD r).1)
  have hn : Integrable (fun y => ∑ r, ‖D r y‖) μ := integrable_finsetSum _ (fun r _ => (hD r).1.norm)
  refine ⟨hi, ?_⟩
  calc
    (∫ y, ‖∑ r, D r y‖ ∂μ) ≤ ∫ y, ∑ r, ‖D r y‖ ∂μ :=
      integral_mono hi.norm hn (fun y => norm_sum_le _ _)
    _ = ∑ r, ∫ y, ‖D r y‖ ∂μ := integral_finsetSum _ (fun r _ => (hD r).1.norm)
    _ ≤ ∑ r, w.weight r * ε r := Finset.sum_le_sum (fun r _ => (hD r).2)
    _ = w.mean ε := rfl

theorem complexMean_supported_fiber_l1_error_uniform (p : FiniteProbabilityWeights X) (F : X → R)
    (μ : Measure Y) (f : X → Y → ℂ) (target : R → Y → ℂ) {ε : ℝ}
    (he : ∀ r (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))),
      Integrable (fun y => (p.condition _ hr).complexMean (fun x => f x y) - target r y) μ ∧
      (∫ y, ‖(p.condition _ hr).complexMean (fun x => f x y) - target r y‖ ∂μ) ≤ ε) :
    Integrable (fun y => p.complexMean (fun x => f x y) - (p.fiberLaw F).complexMean (fun r => target r y)) μ ∧
      (∫ y, ‖p.complexMean (fun x => f x y) - (p.fiberLaw F).complexMean (fun r => target r y)‖ ∂μ) ≤ ε := by
  simpa only [(p.fiberLaw F).mean_const] using p.complexMean_supported_fiber_l1_error F μ f target (fun _ => ε) he

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory
open scoped Classical

variable {X R Y : Type*} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]
variable [MeasurableSpace Y]

omit [Fintype R] [MeasurableSpace Y] in
theorem exists_mem_positive_fiber (p : FiniteProbabilityWeights X) (F : X → R) (r : R)
    (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))) : ∃ x, F x = r := by
  obtain ⟨x, hx⟩ := (p.condition _ hr).exists_weight_pos
  exact ⟨x, (Finset.mem_filter.mp (condition_weight_support p _ hr x hx.ne').1).2⟩

theorem exists_supported_fiber_l1_approximation
    (p : FiniteProbabilityWeights X) (F : X → R) (μ : Measure Y)
    (f : X → Y → ℂ) (ε : R → ℝ) (Spec : R → (Y → ℂ) → Prop)
    (hlocal : ∀ r (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))),
      ∃ g : Y → ℂ, Spec r g ∧ Measurable g ∧
        Integrable (fun y => (p.condition _ hr).complexMean (fun x => f x y) - g y) μ ∧
        (∫ y, ‖(p.condition _ hr).complexMean (fun x => f x y) - g y‖ ∂μ) ≤ ε r) :
    ∃ target : R → Y → ℂ,
      (∀ r, Measurable (target r)) ∧
      (∀ r, 0 < p.mass (Finset.univ.filter (fun x => F x = r)) → Spec r (target r)) ∧
      Integrable (fun y => p.complexMean (fun x => f x y) - (p.fiberLaw F).complexMean (fun r => target r y)) μ ∧
      (∫ y, ‖p.complexMean (fun x => f x y) - (p.fiberLaw F).complexMean (fun r => target r y)‖ ∂μ) ≤
        (p.fiberLaw F).mean ε := by
  let target (r : R) : Y → ℂ := if hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))
    then Classical.choose (hlocal r hr) else fun _ => 0
  have ht (r : R) (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))) :
      Spec r (target r) ∧ Measurable (target r) ∧
        Integrable (fun y => (p.condition _ hr).complexMean (fun x => f x y) - target r y) μ ∧
        (∫ y, ‖(p.condition _ hr).complexMean (fun x => f x y) - target r y‖ ∂μ) ≤ ε r := by
    simpa only [target, dite_eq_left hr] using Classical.choose_spec (hlocal r hr)
  refine ⟨target, ?_, fun r hr => (ht r hr).1, ?_⟩
  · intro r
    by_cases hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))
    · exact (ht r hr).2.1
    · simpa only [target, dite_eq_right hr] using (measurable_const : Measurable (fun _ : Y => (0 : ℂ)))
  · exact p.complexMean_supported_fiber_l1_error F μ f target ε (fun r hr => (ht r hr).2.2)

end Erdos3.FiniteProbabilityWeights

end

end OAI
