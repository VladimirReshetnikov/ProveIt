import Mathlib.Data.Fintype.BigOperators
import OAI.Combinatorics.Progressions.Geometry.IndependentProductTransport

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem independentProductPMF_sum {A B X : Type*} [Fintype A] [Fintype B]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : A ⊕ B → PMF X) :
    independentProductPMF p =
      (independentProductPMF (fun a => p (Sum.inl a))).bind (fun a =>
        (independentProductPMF (fun b => p (Sum.inr b))).map (Sum.elim a)) := by
  ext z
  have hz : Sum.elim (fun a => z (Sum.inl a)) (fun b => z (Sum.inr b)) = z := by
    funext q
    cases q <;> rfl
  have hinj (a : A → X) : Function.Injective (Sum.elim a : (B → X) → A ⊕ B → X) := by
    intro x y h
    funext b
    exact congrFun h (Sum.inr b)
  rw [PMF.bind_apply, tsum_eq_single (fun a => z (Sum.inl a))]
  · have hm := pmf_map_injective_at (independentProductPMF (fun b => p (Sum.inr b)))
      (Sum.elim (fun a => z (Sum.inl a))) (hinj (fun a => z (Sum.inl a)))
      (fun b => z (Sum.inr b))
    rw [hz] at hm
    rw [hm]
    simp only [independentProductPMF_apply, Fintype.prod_sum_type]
  · intro a ha
    have hr : z ∉ Set.range (Sum.elim a : (B → X) → A ⊕ B → X) := by
      rintro ⟨b, he⟩
      apply ha
      funext i
      exact congrFun he (Sum.inl i)
    rw [pmf_map_zero_off_range _ _ _ hr, mul_zero]

end Erdos3

end

end OAI
