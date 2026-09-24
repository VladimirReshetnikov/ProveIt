import Diophantine.Paper1976.NthPrimeGraph
import Diophantine.Common.DiophantineFunctionPolynomial

/-!
# Theorem 4: a polynomial for the nth prime

The article numbers the primes starting at one. Mathlib's `Nat.nth` starts
at zero, so its index is `n - 1`. Only positive input indices are asserted
in the article theorem. The auxiliary variables are nonnegative naturals,
and polynomial evaluation is over the integers.

The proved Diophantine graph and Putnam's positive-value construction give
one finite polynomial, chosen before its input and output. The further
remark that fourteen witnesses suffice requires a separate bound on the
graph representation and is not asserted here.
-/

namespace JSWW1976

/-- The article's one-based prime enumeration; its unused value at zero
is totalized by natural subtraction. -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- Theorem 4: at each positive input index, the positive values of one
integer polynomial are exactly the corresponding prime. The polynomial
has a fixed finite family of natural witnesses. -/
theorem theorem_4 :
    ∃ k : ℕ, ∃ P : MvPolynomial (Unit ⊕ Fin k) ℤ,
      ∀ n m : ℕ, 0 < n → 0 < m →
        (nthPrime n = m ↔ ∃ w : Fin k → ℕ,
          MvPolynomial.eval
            (fun idx => ((Sum.elim (fun _ : Unit => n) w idx : ℕ) : ℤ)) P =
              (m : ℤ)) := by
  obtain ⟨k, P, hP⟩ := Diophantine.exists_polynomial_of_dioph_graph
    (f := nthPrime) nthPrime_graph_dioph
  exact ⟨k, P, fun n m _ hm => hP n m hm⟩

end JSWW1976
