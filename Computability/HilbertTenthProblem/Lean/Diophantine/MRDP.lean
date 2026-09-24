import Diophantine.Common.RecursivelyEnumerableDioph
import Diophantine.Common.DiophantineEnumerable

/-!
# The Matiyasevich–Robinson–Davis–Putnam theorem

A set of natural numbers is recursively enumerable if and only if it is
Diophantine. The finite-polynomial statement uses an ordinary integer
polynomial and finitely many natural witnesses. One polynomial and one
witness dimension serve every input, including zero.

The hard direction is the concise Chinese-remainder proof transplanted from
the standalone MRDP extraction into `Common/MRDPCore.lean`. Its arithmetic closure lemmas,
primitive-recursive graphs, bounded-evaluator argument, and finite polynomial
support use Mathlib alone. No MRDP axiom or arithmetic closure hypothesis is
assumed. `Common/RecursivelyEnumerableDioph.lean` exposes the same proof through
the `Dioph` interface used by the article formalizations.
The converse searches encoded finite witness tuples with a primitive-recursive
polynomial equality test, as proved in `Common/DiophantineEnumerable.lean`.
-/

namespace Diophantine

/-- The computability and Diophantine definitions describe the same subsets
of the naturals. This uses Mathlib's `Dioph` interface. -/
theorem mrdp_dioph_iff {S : Set ℕ} :
    REPred S ↔ Dioph {v : Unit → ℕ | v () ∈ S} :=
  ⟨rePred_dioph, dioph_rePred⟩

/-- MRDP, with an explicit finite integer polynomial: every recursively
enumerable subset of `ℕ` is the projection of its natural zero set. The
polynomial and its finite witness dimension are chosen before the input. -/
theorem mrdp {S : Set ℕ} (hS : REPred S) :
    ∃ k : ℕ, ∃ P : MvPolynomial (Unit ⊕ Fin k) ℤ,
      ∀ n : ℕ, n ∈ S ↔ ∃ w : Fin k → ℕ,
        MvPolynomial.eval
          (fun idx => ((Sum.elim (fun _ : Unit => n) w idx : ℕ) : ℤ)) P = 0 :=
  MRDP.mrdp hS

/-- Full MRDP equivalence with an ordinary integer polynomial and finitely
many natural witnesses. It includes the input zero and permits no witnesses. -/
theorem mrdp_iff {S : Set ℕ} :
    REPred S ↔ ∃ k : ℕ, ∃ P : MvPolynomial (Unit ⊕ Fin k) ℤ,
      ∀ n : ℕ, n ∈ S ↔ ∃ w : Fin k → ℕ,
        MvPolynomial.eval
          (fun idx => ((Sum.elim (fun _ : Unit => n) w idx : ℕ) : ℤ)) P = 0 := by
  constructor
  · exact mrdp
  · rintro ⟨k, P, hP⟩
    refine (finite_polynomial_rePred P).of_eq ?_
    intro n
    exact (hP n).symm

end Diophantine
