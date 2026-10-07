import OAI.Combinatorics.Progressions.Probability.ObservedProductDensity

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem mean_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y) (e : X ≃ Y)
    (hweight : ∀ x, q.weight (e x) = p.weight x) (f : Y → ℝ) :
    p.mean (fun x => f (e x)) = q.mean f := by
  calc
    _ = ∑ x, q.weight (e x) * f (e x) := by
      unfold mean
      simp only [hweight]
    _ = _ := e.sum_comp (fun y => q.weight y * f y)

theorem uniform_mean_equiv {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (e : X ≃ Y) (f : Y → ℝ) :
    (uniform X).mean (fun x => f (e x)) = (uniform Y).mean f := by
  simp only [uniform_mean]
  exact Fintype.expect_equiv e _ f (fun _ => rfl)

theorem fiberMean_equiv {Ω X Y : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (e : X ≃ Y) (F : Ω → X) (w : Ω → ℝ) (x : X) :
    p.fiberMean (fun z => e (F z)) (e x) w = p.fiberMean F x w := by
  unfold fiberMean
  simp only [e.injective.eq_iff]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped Classical

theorem uniform_observedProductDensity_source_equiv {Ω Ω' ι : Type*}
    [Fintype Ω] [Fintype Ω'] [Nonempty Ω] [Nonempty Ω'] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (e : Ω ≃ Ω')
    (F : Ω' → ∀ i, X i) (w : Ω' → ℝ) :
    observedProductDensity μ (FiniteProbabilityWeights.uniform Ω)
      (fun z => F (e z)) (fun z => w (e z)) =
      observedProductDensity μ (FiniteProbabilityWeights.uniform Ω') F w := by
  classical
  funext x
  unfold observedProductDensity finiteWeightDensity
  congr 1
  unfold FiniteProbabilityWeights.fiberMean
  dsimp only
  rw [FiniteProbabilityWeights.uniform_mean, FiniteProbabilityWeights.uniform_mean]
  exact Fintype.expect_equiv e _ _ (fun _ => rfl)

end Erdos3

end

end OAI
