import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-! Exact finite-update algebra. No digit bound, radix lower bound, or modular
    nonwrapping premise is needed for a natural packed-word increment. -/
namespace AdditionalSimplifications
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem weighted_update_add (w c : ι → ℕ) (i : ι) (delta : ℕ) :
    (∑ j, Function.update c i (c i + delta) j * w j) =
      (∑ j, c j * w j) + delta * w i := by
  simp_rw [Function.apply_update (fun j v => v * w j)]
  rw [Finset.sum_update_of_mem (Finset.mem_univ i),
    Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) (fun j => c j * w j)]
  ring

-- The defining expression is the maintained word expression, with section parameters explicit.
def word {n : ℕ} [NeZero n] (ρ : ℕ) (a : ZMod n → ℕ) : ℕ :=
  ∑ i, a i * ρ ^ i.val

theorem word_update_increment_new {n : ℕ} [NeZero n] (ρ : ℕ)
    (c : ZMod n → ℕ) (i : ZMod n) :
    word ρ (Function.update c i (c i+1)) = word ρ c+ρ^i.val := by
  unfold word
  simp_rw [Function.apply_update (fun (j : ZMod n) v => v * ρ ^ j.val)]
  rw [Finset.sum_update_of_mem (Finset.mem_univ i),
    Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) (fun j => c j * ρ ^ j.val)]
  ring

theorem update_boolean_new {N : ℕ} (dummy : ZMod N → ℕ)
    (hd : ∀ i, dummy i ≤ 1) (j i : ZMod N) :
    Function.update dummy j 1 i ≤ 1 := by
  exact (Function.forall_update_iff dummy (fun _ v => v ≤ 1)).mpr
    ⟨le_rfl, fun k _ => hd k⟩ i

#print axioms weighted_update_add
#print axioms word_update_increment_new
#print axioms update_boolean_new
end AdditionalSimplifications
