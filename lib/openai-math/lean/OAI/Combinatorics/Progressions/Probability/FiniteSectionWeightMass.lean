import OAI.Combinatorics.Progressions.Estimates.FiniteSectionPermutation

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteSectionWeight_mass_true (w : X → ℝ) (z : X) :
    (∑ x, finiteSectionWeight w true z x) = 1 := by
  simpa only [mul_one] using finiteSectionWeight_sum_true w z (fun _ => 1)

theorem finiteSectionWeight_mass_one (w : X → ℝ) (hw : ∑ x, w x = 1) (b : Bool) (z : X) :
    (∑ x, finiteSectionWeight w b z x) = 1 := by
  cases b with
  | false => simpa only [finiteSectionWeight_false] using hw
  | true => exact finiteSectionWeight_mass_true w z

end Erdos3

end

end OAI
