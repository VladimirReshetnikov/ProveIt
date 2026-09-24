import Diophantine.Paper1982.Theorem3
import Diophantine.Paper1982.RecursivelyEnumerableQuartic

/-!
# Jones 1980, Theorem 5 (also Theorem 5 of Jones 1982)

The announcement's Theorems 1–3 are, equation for equation, Theorems 1–3 of
the 1982 article with `ν = 58` (exponent `5^60`); they are formalized once, as
`Jones1982.theorem_1`, `Jones1982.theorem_2` and `Jones1982.theorem_3`, and
are not restated here.  The row `(58, 4)` of Theorem 4 is
`Jones1982.universal_quartic58`.

Theorem 5 reads: for any effectively axiomatizable theory `T` and any
proposition `P`, if `P` has a proof in `T`, then `P` has "another proof"
consisting of 100 additions and multiplications of integers.  The
corrected edition's footnote explains that "another proof" means an
arithmetic certificate: under Gödel numbering the theorems of `T` form a
recursively enumerable set, so by Theorem 3 provability of `P` is equivalent
to the solvability of the fixed polynomial system of Theorem 3 at the index
of that set, and a solution is the certificate.

That reading is what is formalized: an effectively axiomatizable theory is
represented by the recursively enumerable set `S` of the Gödel numbers of its
theorems (`REPred S`), and the conclusion is the equivalence, for every
positive Gödel number, between membership in `S` and the existence of
twenty-eight positive integers satisfying the eighteen equations of
Theorem 3.  The count of the indicated arithmetical operations of that
system, and the question of which operation-counting convention the
announcement intends, are discussed in the satellite article
`Papers/1980/jones1980_theorem5_operations.tex`; they are statements about
the printed syntax of the system and are not part of this theorem.
-/

namespace Jones1980

open Jones1982

/-- Theorem 5 of the 1980 announcement (and of the 1982 article), certificate
reading: every recursively enumerable set `S` — in particular the set of Gödel
numbers of the theorems of an effectively axiomatizable theory — has an index
`⟨z, u, y⟩` of a normalized quartic `P` in 58 witnesses such that, for every
positive `x`, `x ∈ S` if and only if the eighteen equations of Theorem 3 have
a solution in positive integers.  Such a solution is the "other proof". -/
theorem theorem_5 {S : Set ℕ} (hS : REPred S) :
    ∃ (P : MvPolynomial (Fin 59) ℤ) (z u y : ℕ), 0 < z ∧ 0 < u ∧ 0 < y ∧
      P.totalDegree ≤ 4 ∧ Normalized P ∧ Index 58 P z u y ∧
      ∀ x : ℕ, 0 < x →
        (x ∈ S ↔ ∃ a b c d e f g h i j k l m n o p q r s t w α γ η θ lam τ φ : ℕ,
          0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f ∧ 0 < g ∧ 0 < h ∧
          0 < i ∧ 0 < j ∧ 0 < k ∧ 0 < l ∧ 0 < m ∧ 0 < n ∧ 0 < o ∧ 0 < p ∧
          0 < q ∧ 0 < r ∧ 0 < s ∧ 0 < t ∧ 0 < w ∧ 0 < α ∧ 0 < γ ∧ 0 < η ∧
          0 < θ ∧ 0 < lam ∧ 0 < τ ∧ 0 < φ ∧
          Thm3 58 x z u y a b c d e f g h i j k l m n o p q r s t w α γ η θ lam τ φ) := by
  obtain ⟨Q, hQ, hnorm, hrep⟩ := rePred_quartic58 hS
  obtain ⟨z, u, y, hz, hu, hy, hI⟩ := exists_index (ν := 58) Q (by norm_num)
  exact ⟨Q, z, u, y, hz, hu, hy, hQ, hnorm, hI,
    fun x hx => (hrep x hx).trans (theorem_3 (by norm_num) hQ hnorm hI hx)⟩

end Jones1980
