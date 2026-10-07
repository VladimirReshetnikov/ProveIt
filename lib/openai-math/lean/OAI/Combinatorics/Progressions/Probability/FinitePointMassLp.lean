import OAI.Combinatorics.Progressions.Estimates.FiniteSectionPermutation

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

omit [Fintype X] in
theorem finiteSectionWeight_nonneg (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (b : Bool) (z x : X) : 0 ≤ finiteSectionWeight w b z x := by
  classical
  unfold finiteSectionWeight
  split_ifs <;> first | positivity | exact hw x

theorem finiteWeightedLp_pointMass (w : X → ℝ) (z : X) {p : ℝ}
    (hp : 0 < p) (f : X → ℝ) :
    finiteWeightedLp (finiteSectionWeight w true z) p f = |f z| := by
  unfold finiteWeightedLp
  rw [finiteSectionWeight_sum_true, ← Real.rpow_mul (abs_nonneg _)]
  have he : p * (1 / p) = 1 := by field_simp
  rw [he, Real.rpow_one]

theorem finiteMixedLp_abs (w : ℕ → X → ℝ) (p : ℕ → ℝ) (n : ℕ)
    (f : (Fin n → X) → ℝ) :
    finiteMixedLp w p n (fun v => |f v|) = finiteMixedLp w p n f := by
  cases n with
  | zero => simp only [finiteMixedLp, abs_abs]
  | succ n => simp only [finiteMixedLp, finiteWeightedLp, abs_abs]

end Erdos3

end

end OAI
