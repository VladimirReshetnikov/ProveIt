/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3
open scoped BigOperators

theorem recursive_density_discount_pow {s n : ℕ} {δ ε : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hn : n ≤ s + 1)
    (hbudget : ((s + 1 : ℕ) : ℝ) * δ ≤ ε) :
    1 - ε ≤ (1 - δ) ^ n := by
  have hbern : 1 - (n : ℝ) * δ ≤ (1 - δ) ^ n := by
    simpa only [sub_eq_add_neg, mul_neg] using
      (one_add_mul_le_pow (show (-2 : ℝ) ≤ -δ by linarith [hδ.2]) n)
  have hcount : (n : ℝ) * δ ≤ ((s + 1 : ℕ) : ℝ) * δ :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) hδ.1
  exact (sub_le_sub_left (hcount.trans hbudget) 1).trans hbern

theorem recursive_density_discount_prod {ι : Type*} (S : Finset ι)
    {s : ℕ} {δ ε : ℝ} (discount : ι → ℝ)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hcount : S.card ≤ s + 1)
    (hbudget : ((s + 1 : ℕ) : ℝ) * δ ≤ ε)
    (hdiscount : ∀ i ∈ S, discount i ∈ Set.Icc (0 : ℝ) δ) :
    1 - ε ≤ ∏ i ∈ S, (1 - discount i) := by
  calc
    1 - ε ≤ (1 - δ) ^ S.card := recursive_density_discount_pow hδ hcount hbudget
    _ = ∏ _i ∈ S, (1 - δ) := (Finset.prod_const _).symm
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => sub_nonneg.mpr hδ.2)
      (fun i hi => sub_le_sub_left (hdiscount i hi).2 1)

theorem recursive_density_discount_scaled {s n : ℕ} {δ ε Λ : ℝ}
    (hΛ : 0 ≤ Λ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hn : n ≤ s + 1)
    (hbudget : ((s + 1 : ℕ) : ℝ) * δ ≤ ε) :
    (1 - ε) * Λ ≤ (1 - δ) ^ n * Λ :=
  mul_le_mul_of_nonneg_right (recursive_density_discount_pow hδ hn hbudget) hΛ

end Erdos3

end

end OAI
