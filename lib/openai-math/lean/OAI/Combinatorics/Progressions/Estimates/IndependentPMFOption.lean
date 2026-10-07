import Mathlib.Data.Fintype.BigOperators
import OAI.Combinatorics.Progressions.Geometry.IndependentProductTransport

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem independentProductPMF_option {B X : Type*} [Fintype B]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : Option B → PMF X) :
    independentProductPMF p = (p none).bind (fun c =>
      (independentProductPMF (fun b => p (some b))).map
        (fun x q => q.elim c x)) := by
  ext z
  have hz : (fun q : Option B => q.elim (z none) (fun b => z (some b))) = z := by
    funext q
    cases q <;> rfl
  have hinj (c : X) : Function.Injective (fun (x : B → X) (q : Option B) => q.elim c x) := by
    intro x y h
    funext b
    exact congrFun h (some b)
  rw [PMF.bind_apply, tsum_eq_single (z none)]
  · have hm := pmf_map_injective_at (independentProductPMF (fun b => p (some b)))
      (fun (x : B → X) (q : Option B) => q.elim (z none) x) (hinj (z none))
      (fun b => z (some b))
    rw [hz] at hm
    rw [hm]
    simp only [independentProductPMF_apply, Fintype.prod_option]
  · intro c hc
    have hr : z ∉ Set.range (fun (x : B → X) (q : Option B) => q.elim c x) := by
      rintro ⟨x, he⟩
      exact hc (congrFun he none)
    rw [pmf_map_zero_off_range _ _ _ hr, mul_zero]

end Erdos3

end

end OAI
