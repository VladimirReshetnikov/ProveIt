import Diophantine.Paper1980.Necessity93
import Diophantine.Paper1982.RecursivelyEnumerableQuartic

/-!
# The 93-operation system is universal

For every Diophantine (equivalently, recursively enumerable) set `S` of
natural numbers there is a fixed index `(V, H, Tindex)` such that, for every
positive `x`, `x ∈ S` if and only if the 22 equations of the 93-operation
system have a solution in positive integers.  This is the universality
theorem for the encodings of `FACTORED_MASK_93_PROOF.md`: the sufficiency
direction is `Iso.sufficiency`, the necessity direction `Iso.necessity`, and
the circuit is supplied by `Gates.exists_circuit`.
-/

namespace Jones1980

/-- Universality of the 93-operation system for Diophantine sets. -/
theorem universal93 {S : Set ℕ} (hS : Jones1978.IsDiophantine S) :
    ∃ V H Tindex : ℕ, ∀ x : ℕ, 0 < x → (x ∈ S ↔ Solvable93 x V H Tindex) := by
  obtain ⟨C, hC⟩ := Gates.exists_circuit hS
  refine ⟨Iso.cV C, Iso.cH C, Iso.cT C, fun x hx => ?_⟩
  rw [hC x hx]
  exact ⟨fun hacc => Iso.necessity C hx hacc, fun hsolv => Iso.sufficiency C hx hsolv⟩

/-- Universality of the 93-operation system for recursively enumerable sets. -/
theorem universal93_re {S : Set ℕ} (hS : REPred S) :
    ∃ V H Tindex : ℕ, ∀ x : ℕ, 0 < x → (x ∈ S ↔ Solvable93 x V H Tindex) :=
  universal93 (Jones1978.isDiophantine_of_rePred hS)

end Jones1980
