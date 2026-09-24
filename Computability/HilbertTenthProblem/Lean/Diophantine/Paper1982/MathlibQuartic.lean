import Diophantine.Paper1978.MathlibDiophBridge
import Diophantine.Paper1982.DiophantineQuartic

/-!
# Fifty-eight witnesses for Mathlib Diophantine sets

The representation adapter makes Mathlib's proved Diophantine constructions
available to the article's quartic compression theorem. Neither the adapter
nor the compression asserts that every recursively enumerable set is
Diophantine.
-/

namespace Jones1982

/-- Every Mathlib Diophantine subset of the natural numbers has one
normalized 58-witness quartic representing all its positive members. -/
theorem mathlib_dioph_quartic58 {S : Set ℕ}
    (hS : Dioph {v : Unit → ℕ | v () ∈ S}) :
    ∃ Q : MvPolynomial (Fin 59) ℤ, Q.totalDegree ≤ 4 ∧ Normalized Q ∧
      ∀ x : ℕ, 0 < x → (x ∈ S ↔ Wset Q x) :=
  diophantine_quartic58 (Jones1978.isDiophantine_iff_mathlib_dioph.mpr hS)

/-- In particular, each fixed-base power set has such a representation.
Mathlib proves the exponentiation representation used here. -/
theorem powers_quartic58 (a : ℕ) :
    ∃ Q : MvPolynomial (Fin 59) ℤ, Q.totalDegree ≤ 4 ∧ Normalized Q ∧
      ∀ x : ℕ, 0 < x → ((∃ n : ℕ, a ^ n = x) ↔ Wset Q x) :=
  diophantine_quartic58 (Jones1978.isDiophantine_powers a)

end Jones1982
