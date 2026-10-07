import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def independentProductPMF {D X : Type*} [Fintype D] [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : D → PMF X) : PMF (D → X) :=
  (Measure.pi (fun d => (p d).toMeasure)).toPMF

theorem independentProductPMF_apply {D X : Type*} [Fintype D] [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : D → PMF X) (x : D → X) :
    independentProductPMF p x = ∏ d, p d (x d) := by
  simp only [independentProductPMF, Measure.toPMF_apply, Measure.pi_singleton]
  exact Finset.prod_congr rfl (fun d _ => (p d).toMeasure_apply_singleton (x d) (measurableSet_singleton _))

theorem independentProductPMF_toReal {D X : Type*} [Fintype D] [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : D → PMF X) (x : D → X) :
    (independentProductPMF p x).toReal = ∏ d, (p d (x d)).toReal := by
  rw [independentProductPMF_apply, ENNReal.toReal_prod]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def dependentProductPMF {D : Type*} [Fintype D] {X : D → Type*}
    [∀ d, Countable (X d)] [∀ d, MeasurableSpace (X d)] [∀ d, MeasurableSingletonClass (X d)]
    (p : ∀ d, PMF (X d)) : PMF (∀ d, X d) :=
  (Measure.pi (fun d => (p d).toMeasure)).toPMF

theorem dependentProductPMF_apply {D : Type*} [Fintype D] {X : D → Type*}
    [∀ d, Countable (X d)] [∀ d, MeasurableSpace (X d)] [∀ d, MeasurableSingletonClass (X d)]
    (p : ∀ d, PMF (X d)) (x : ∀ d, X d) : dependentProductPMF p x = ∏ d, p d (x d) := by
  simp only [dependentProductPMF, Measure.toPMF_apply, Measure.pi_singleton]
  exact Finset.prod_congr rfl (fun d _ => (p d).toMeasure_apply_singleton (x d) (measurableSet_singleton _))

theorem dependentProductPMF_scaled {D : Type*} [Fintype D] {X : D → Type*}
    [∀ d, Countable (X d)] [∀ d, MeasurableSpace (X d)] [∀ d, MeasurableSingletonClass (X d)]
    (p : ∀ d, PMF (X d)) (S : D → ℝ) (x : ∀ d, X d) :
    (∏ d, S d) * (dependentProductPMF p x).toReal = ∏ d, S d * (p d (x d)).toReal := by
  rw [dependentProductPMF_apply, ENNReal.toReal_prod, Finset.prod_mul_distrib]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

theorem dependentProductPMF_map {J : Type*} [Fintype J] {X Y : J → Type*}
    [∀ j, Countable (X j)] [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSingletonClass (X j)]
    [∀ j, Countable (Y j)] [∀ j, MeasurableSpace (Y j)] [∀ j, MeasurableSingletonClass (Y j)]
    (p : ∀ j, PMF (X j)) (f : ∀ j, X j → Y j) :
    (dependentProductPMF p).map (fun x j => f j (x j)) =
      dependentProductPMF (fun j => (p j).map (f j)) := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  simp only [dependentProductPMF, Measure.toPMF_toMeasure]
  rw [Measure.pi_map_pi (fun j => (measurable_of_countable (f j)).aemeasurable)]
  congr 1
  funext j
  exact PMF.toMeasure_map (f j) (p j) (measurable_of_countable _)

end Erdos3

end

end OAI
