import Diophantine.Common.RecursivelyEnumerableDioph
import Diophantine.Paper1982.MathlibQuartic

/-!
# Quartic representations of recursively enumerable sets

The computability-to-Diophantine bridge supplies a polynomial representation
for every recursively enumerable subset of the natural numbers. Combining
it with the article's proved algebraic compression yields a normalized
quartic with 58 natural witnesses, uniformly on all positive inputs.
-/

namespace Jones1978

/-- Every recursively enumerable natural-number set is Diophantine in the
article's finite-polynomial convention, including at input zero. -/
theorem isDiophantine_of_rePred {S : Set ℕ} (hS : REPred S) : IsDiophantine S :=
  isDiophantine_iff_mathlib_dioph.mpr (Diophantine.rePred_dioph hS)

end Jones1978

namespace Jones1982

/-- Every recursively enumerable set has a normalized quartic representation
with 58 natural witnesses on positive inputs. A fixed parameter family is
packaged separately in `UniversalQuartic.lean`. -/
theorem rePred_quartic58 {S : Set ℕ} (hS : REPred S) :
    ∃ Q : MvPolynomial (Fin 59) ℤ, Q.totalDegree ≤ 4 ∧ Normalized Q ∧
      ∀ x : ℕ, 0 < x → (x ∈ S ↔ Wset Q x) :=
  mathlib_dioph_quartic58 (Diophantine.rePred_dioph hS)

end Jones1982
