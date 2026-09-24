import Diophantine.Paper1980.Necessity90
import Diophantine.Paper1982.RecursivelyEnumerableQuartic

/-!
# The 90-operation system is universal

For every Diophantine (equivalently, recursively enumerable) set `S` of
natural numbers there is a fixed index `(V, H, Tindex)` such that, for every
positive `x`, `x ∈ S` if and only if the 22 equations of the 90-operation
system have a solution in positive integers.  This is the universality
theorem for the encodings of `BINARY_PRODUCT_90_PROOF.md` and
`BASE_TWO_PELL_90_PROOF.md`: the sufficiency direction is
`L90.sufficiency`, the necessity direction `L90.necessity`, and the circuit
is supplied by `Gates.exists_circuit`.
-/

namespace Jones1980

/-- Universality of the 90-operation system for Diophantine sets. -/
theorem universal90 {S : Set ℕ} (hS : Jones1978.IsDiophantine S) :
    ∃ V H Tindex : ℕ, ∀ x : ℕ, 0 < x → (x ∈ S ↔ Solvable90 x V H Tindex) := by
  obtain ⟨C, hC⟩ := Gates.exists_circuit hS
  refine ⟨L90.cV C, L90.cH C, L90.cT C, fun x hx => ?_⟩
  rw [hC x hx]
  exact ⟨fun hacc => L90.necessity C hx hacc, fun hsolv => L90.sufficiency C hx hsolv⟩

/-- Universality of the 90-operation system for recursively enumerable sets. -/
theorem universal90_re {S : Set ℕ} (hS : REPred S) :
    ∃ V H Tindex : ℕ, ∀ x : ℕ, 0 < x → (x ∈ S ↔ Solvable90 x V H Tindex) :=
  universal90 (Jones1978.isDiophantine_of_rePred hS)

end Jones1980
