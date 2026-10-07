/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem selected_nonnegative_product_le {A D : Type*} [Fintype A] [Fintype D]
    (f : D → ℝ) (hf : ∀ d, 0 ≤ f d) (selected : A → D)
    (hselected : Function.Injective selected) :
    (∏ a, f (selected a)) ≤ (1 + ∑ d, f d) ^ Fintype.card D := by
  let C := 1 + ∑ d, f d
  have hs : 0 ≤ ∑ d, f d := Finset.sum_nonneg (fun d _ => hf d)
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  have hbound (a : A) : f (selected a) ≤ C := by
    have h := Finset.single_le_sum (fun d _ => hf d) (Finset.mem_univ (selected a))
    dsimp only [C]
    linarith
  calc
    _ ≤ ∏ _a : A, C := Finset.prod_le_prod₀ (fun index _ => hf (selected index))
      (fun index _ => hbound index)
    _ = C ^ Fintype.card A := by simp only [Finset.prod_const, Finset.card_univ]
    _ ≤ C ^ Fintype.card D := pow_le_pow_right₀ hC (Fintype.card_le_of_injective selected hselected)

end Erdos3

end

end OAI
