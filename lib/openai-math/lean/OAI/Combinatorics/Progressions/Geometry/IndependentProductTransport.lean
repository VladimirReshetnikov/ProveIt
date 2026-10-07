import OAI.Combinatorics.Progressions.Estimates.ProductPMFMap
import OAI.Combinatorics.Progressions.Estimates.RealWeightPMF

namespace OAI

section

namespace Erdos3

theorem pmf_map_injective_at {X Y : Type*} (p : PMF X) (f : X → Y)
    (hf : Function.Injective f) (x : X) : p.map f (f x) = p x := by
  classical
  rw [PMF.map_apply, tsum_eq_single x]
  · simp
  · intro y hy
    have hne : f x ≠ f y := fun h => hy (hf h).symm
    simp only [hne, ite_false]

theorem pmf_map_zero_off_range {X Y : Type*} (p : PMF X) (f : X → Y) (y : Y)
    (hy : y ∉ Set.range f) : p.map f y = 0 := by
  classical
  have hne (x) : y ≠ f x := fun h => hy ⟨x, h.symm⟩
  simp only [PMF.map_apply, hne, ite_false, tsum_zero]

theorem pmf_map_injective_expectation {X Y : Type*} (p : PMF X) (f : X → Y)
    (hf : Function.Injective f) (φ : Y → ℂ) :
    (∑' y, ((p.map f y).toReal : ℂ) * φ y) =
      ∑' x, ((p x).toReal : ℂ) * φ (f x) := by
  have hs : Function.support (fun y => ((p.map f y).toReal : ℂ) * φ y) ⊆ Set.range f := by
    intro y hy
    by_contra hn
    have hz := pmf_map_zero_off_range p f y hn
    exact hy (by simp only [hz, ENNReal.toReal_zero, Complex.ofReal_zero, zero_mul])
  have he := hf.tsum_eq hs
  simpa only [pmf_map_injective_at p f hf] using he.symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem independentProductPMF_map {D X Y : Type*} [Fintype D]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    [Countable Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (p : D → PMF X) (f : D → X → Y) :
    (independentProductPMF p).map (fun x i => f i (x i)) =
      independentProductPMF (fun i => (p i).map (f i)) := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (fun (x : D → X) i => f i (x i)) _ (measurable_of_countable _)]
  simp only [independentProductPMF, Measure.toPMF_toMeasure]
  rw [Measure.pi_map_pi (fun i => (measurable_of_countable (f i)).aemeasurable)]
  congr 1
  funext i
  exact PMF.toMeasure_map (f i) (p i) (measurable_of_countable _)

def independentArrayRows {J I X : Type*} (z : J × I → X) : I → J → X :=
  fun i j => z (j, i)

theorem independentArrayRows_injective {J I X : Type*} :
    Function.Injective (independentArrayRows (J := J) (I := I) (X := X)) := by
  intro x y h
  funext ji
  exact congrFun (congrFun h ji.2) ji.1

theorem independentProductPMF_rows {J I X : Type*} [Fintype J] [Fintype I]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : J × I → PMF X) :
    (independentProductPMF p).map independentArrayRows =
      independentProductPMF (fun i => independentProductPMF (fun j => p (j, i))) := by
  ext y
  let z : J × I → X := fun ji => y ji.2 ji.1
  change (independentProductPMF p).map independentArrayRows (independentArrayRows z) = _
  rw [pmf_map_injective_at _ _ independentArrayRows_injective]
  simp only [independentProductPMF_apply, Fintype.prod_prod_type, z]
  exact Finset.prod_comm

theorem independentProductPMF_reindex {D E X : Type*} [Fintype D] [Fintype E]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (e : D ≃ E) (p : E → PMF X) :
    (independentProductPMF p).map (fun x d => x (e d)) =
      independentProductPMF (fun d => p (e d)) := by
  have hinj : Function.Injective (fun (x : E → X) d => x (e d)) := by
    intro x y h
    funext a
    simpa using congrFun h (e.symm a)
  ext y
  let z : E → X := fun a => y (e.symm a)
  have hz : (fun d => z (e d)) = y := by funext d; simp [z]
  rw [← hz, pmf_map_injective_at _ _ hinj]
  simp only [independentProductPMF_apply]
  exact (e.prod_comp (fun a => p a (z a))).symm

end Erdos3

end

end OAI
