import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# The eventual good set of a sequence of refinements
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace GlobeFlattening

variable {X : Type*}

/-- The points in every sufficiently late trimmed tile union. -/
def eventualGoodSet (good : ℕ → Set X) : Set X :=
  ⋃ N, ⋂ n ≥ N, good n

theorem mem_eventualGoodSet {good : ℕ → Set X} {x : X} :
    x ∈ eventualGoodSet good ↔ ∀ᶠ n in atTop, x ∈ good n := by
  simp [eventualGoodSet, eventually_atTop]

variable [MeasurableSpace X]

theorem measurableSet_eventualGoodSet {good : ℕ → Set X}
    (hgood : ∀ n, MeasurableSet (good n)) : MeasurableSet (eventualGoodSet good) :=
  MeasurableSet.iUnion (fun _ => MeasurableSet.iInter (fun n =>
    MeasurableSet.iInter (fun _ => hgood n)))

/-- Apply Borel–Cantelli inside the domain. Nullity of the bad sets outside the
domain is unnecessary. -/
theorem measure_diff_eventualGoodSet (μ : Measure X) {domain : Set X} {good : ℕ → Set X}
    (hsum : (∑' n, μ (domain \ good n)) ≠ ∞) :
    μ (domain \ eventualGoodSet good) = 0 := by
  classical
  have hfinite := ae_eventually_notMem (μ := μ) hsum
  have hae : ∀ᵐ x ∂μ, x ∉ domain \ eventualGoodSet good := by
    filter_upwards [hfinite] with x hx
    intro hxBad
    apply hxBad.2
    exact mem_eventualGoodSet.2 (hx.mono (fun n hn => by
      by_contra hnot
      exact hn ⟨hxBad.1, hnot⟩))
  simpa only [not_not, setOf_mem_eq] using (ae_iff.1 hae)

end GlobeFlattening
