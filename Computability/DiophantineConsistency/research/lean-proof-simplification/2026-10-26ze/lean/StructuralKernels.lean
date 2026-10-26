import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.Ring

namespace StructuralKernels

theorem row_zero_of_helix {α : Type*} (T : ℤ → ℤ → α) (w : ℤ)
    (hhelix : ∀ x t, T (x+w) (t-1) = T x t) (x t : ℤ) :
    T x t = T (x+w*t) 0 := by
  let f : ℤ → α := fun s => T (x+w*s) (t-s)
  have hp : Function.Periodic f 1 := by
    intro s
    dsimp [f]
    convert hhelix (x+w*s) (t-s) using 1; congr 1 <;> ring
  simpa [f] using hp.sub_int_mul_eq (x := t) t

theorem eliminate_function_witness {ι α : Type*}
    (P : (ι → α) → Prop) (f : ι → α) :
    (∃ a, P a ∧ ∀ i, a i = f i) ↔ P f := by
  simp only [← funext_iff, exists_eq_right]

theorem helix_iff_unique_factorization {α : Type*} (T : ℤ → ℤ → α) (w : ℤ) :
    (∀ x t, T (x+w) (t-1) = T x t) ↔
      ∃! F : ℤ → α, ∀ x t, T x t = F (x+w*t) := by
  constructor
  · intro hh
    refine ⟨fun z => T z 0, row_zero_of_helix T w hh, ?_⟩
    intro F hF
    funext z
    simpa using (hF z 0).symm
  · rintro ⟨F, hF, _⟩ x t
    rw [hF, hF]
    congr 1
    ring

#print axioms helix_iff_unique_factorization
#print axioms row_zero_of_helix
#print axioms eliminate_function_witness
end StructuralKernels
