import Mathlib

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sum_integerInterval_eq_range {M : Type*} [AddCommMonoid M]
    (f : ℤ → M) (u v : ℤ) :
    (∑ x ∈ Finset.Ico u v, f x) =
      ∑ n ∈ Finset.range (v - u).toNat, f (u + (n : ℤ)) := by
  symm
  apply Finset.sum_bij (fun (n : ℕ) _ => u + (n : ℤ))
  · intro n hn
    simp only [Finset.mem_range] at hn
    simp only [Finset.mem_Ico]
    omega
  · intro n hn m hm heq
    omega
  · intro x hx
    simp only [Finset.mem_Ico] at hx
    refine ⟨(x - u).toNat, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro n hn
    rfl

end Erdos3

end

end OAI
