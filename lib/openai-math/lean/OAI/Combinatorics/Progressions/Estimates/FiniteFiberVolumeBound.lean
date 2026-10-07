import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem integral_indicator_fiber (ν : Measure B) (s : Set (A × B)) (hs : MeasurableSet s) (x : A) :
    (∫ y, s.indicator (fun _ => (1 : ℝ)) (x, y) ∂ν) = ν.real {y | (x, y) ∈ s} := by
  have ht : MeasurableSet {y | (x, y) ∈ s} := hs.preimage (measurable_const.prodMk measurable_id)
  have heq : (fun y => s.indicator (fun _ => (1 : ℝ)) (x, y)) =
      {y | (x, y) ∈ s}.indicator (fun _ => (1 : ℝ)) := by
    funext y
    rfl
  rw [heq]
  exact integral_indicator_one ht

theorem product_measureReal_eq_integral_fiber
    (μ : Measure A) (ν : Measure B) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (s : Set (A × B)) (hs : MeasurableSet s) :
    (μ.prod ν).real s = ∫ x, ν.real {y | (x, y) ∈ s} ∂μ := by
  rw [← integral_indicator_one hs]
  change (∫ z, s.indicator (fun _ => (1 : ℝ)) z ∂μ.prod ν) = _
  rw [integral_prod _ ((integrable_const (1 : ℝ)).indicator hs)]
  apply integral_congr_ae
  filter_upwards [] with x
  exact integral_indicator_fiber ν s hs x

theorem product_probability_le_bad_set_add
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : Set (A × B)) (hs : MeasurableSet s) (bad : Set A) (hbad : MeasurableSet bad)
    {b : ℝ} (hb : 0 ≤ b) (hgood : ∀ x, x ∉ bad → ν.real {y | (x, y) ∈ s} ≤ b) :
    (μ.prod ν).real s ≤ μ.real bad + b := by
  have hi : Integrable (s.indicator (fun _ => (1 : ℝ))) (μ.prod ν) :=
    (integrable_const (1 : ℝ)).indicator hs
  rw [← integral_indicator_one hs]
  change (∫ z, s.indicator (fun _ => (1 : ℝ)) z ∂μ.prod ν) ≤ _
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ x, bad.indicator (fun _ => (1 : ℝ)) x + b ∂μ := by
      apply integral_mono hi.integral_prod_left
        (((integrable_const (1 : ℝ)).indicator hbad).add (integrable_const b))
      intro x
      change (∫ y, s.indicator (fun _ => (1 : ℝ)) (x, y) ∂ν) ≤
        bad.indicator (fun _ => (1 : ℝ)) x + b
      rw [integral_indicator_fiber ν s hs x]
      by_cases hx : x ∈ bad
      · rw [Set.indicator_of_mem hx]
        have hle : ν.real {y | (x, y) ∈ s} ≤ 1 := by
          have h := measureReal_mono (μ := ν) (Set.subset_univ {y | (x, y) ∈ s})
          simp only [probReal_univ] at h
          exact h
        linarith
      · rw [Set.indicator_of_notMem hx, zero_add]
        exact hgood x hx
    _ = _ := by
      rw [integral_add ((integrable_const (1 : ℝ)).indicator hbad) (integrable_const b),
        integral_indicator_const (1 : ℝ) hbad, integral_const]
      simp

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem product_measureReal_eq_integral_fiber_of_finite {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (s : Set (A × B)) (hs : MeasurableSet s) (hfin : (μ.prod ν) s ≠ ⊤) :
    (μ.prod ν).real s = ∫ x, ν.real {y | (x, y) ∈ s} ∂μ := by
  have hi : Integrable (s.indicator (fun _ => (1 : ℝ))) (μ.prod ν) :=
    (integrableOn_const hfin).integrable_indicator hs
  rw [← integral_indicator_one hs]
  change (∫ z, s.indicator (fun _ => (1 : ℝ)) z ∂μ.prod ν) = _
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with x
  exact integral_indicator_fiber ν s hs x

theorem product_measureReal_le_of_fiber_bound {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (s : Set (A × B)) (hs : MeasurableSet s) (hsfin : (μ.prod ν) s ≠ ⊤)
    (T : Set A) (hT : MeasurableSet T) (hTfin : μ T ≠ ⊤)
    (hbase : ∀ z ∈ s, z.1 ∈ T) {b : ℝ}
    (hbound : ∀ x, ν.real {y | (x, y) ∈ s} ≤ b) :
    (μ.prod ν).real s ≤ μ.real T * b := by
  have hi : Integrable (s.indicator (fun _ => (1 : ℝ))) (μ.prod ν) :=
    (integrableOn_const hsfin).integrable_indicator hs
  have hmajor : Integrable (T.indicator (fun _ => b)) μ :=
    (integrableOn_const hTfin).integrable_indicator hT
  rw [← integral_indicator_one hs]
  change (∫ z, s.indicator (fun _ => (1 : ℝ)) z ∂μ.prod ν) ≤ _
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ x, T.indicator (fun _ => b) x ∂μ := by
      apply integral_mono hi.integral_prod_left hmajor
      intro x
      change (∫ y, s.indicator (fun _ => (1 : ℝ)) (x, y) ∂ν) ≤ T.indicator (fun _ => b) x
      rw [integral_indicator_fiber ν s hs]
      by_cases hx : x ∈ T
      · rw [Set.indicator_of_mem hx]
        exact hbound x
      · have hempty : {y | (x, y) ∈ s} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro y hy
          exact hx (hbase (x, y) hy)
        rw [hempty, measureReal_empty, Set.indicator_of_notMem hx]
    _ = _ := by rw [integral_indicator_const _ hT, smul_eq_mul]

end Erdos3

end

end OAI
