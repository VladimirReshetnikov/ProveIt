import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

namespace AdditionalProofSimplifications

/-- Adding a distinguished zero preserves injectivity after shifting the tail. -/
theorem zeroExtension_injective {n : ℕ} (f : Fin n → ℕ)
    (hf : Function.Injective f) :
    Function.Injective (Fin.cons 0 (fun i => 1 + f i)) := by
  apply Fin.cons_injective_iff.mpr
  refine ⟨?_, ?_⟩
  · simp
  · intro i j h
    exact hf (Nat.add_left_cancel h)

/-- Existing zero/successor equations are enough to reuse the library API. -/
theorem named_zeroExtension_injective {n : ℕ} (g : Fin (n + 1) → ℕ)
    (f : Fin n → ℕ) (hzero : g 0 = 0)
    (hsucc : ∀ i, g i.succ = 1 + f i) (hf : Function.Injective f) :
    Function.Injective g := by
  have hg : g = Fin.cons 0 (fun i => 1 + f i) := by
    funext i
    exact Fin.cases hzero hsucc i
  rw [hg]
  exact zeroExtension_injective f hf

#print axioms named_zeroExtension_injective

end AdditionalProofSimplifications
