import Diophantine.Paper1982.ShortQuadraticNecessity
import Diophantine.Paper1982.ShortQuadraticSoundness
import Diophantine.Paper1982.ShortQuartic
import Diophantine.Paper1982.ShortPolynomialMaster

/-!
# Jones 1982, §5: reduction to a normalized quartic with 58 witnesses

The substitutions preserve solvability in both directions. Combined with
the full polynomial master theorem, they give one explicit normalized
quartic representing every positive input of a supplied normalized quartic
with an arbitrary positive number of witnesses. A representation theorem
for arbitrary recursively enumerable sets is a further obligation.
-/

namespace Jones1982

theorem short_polynomial_iff_quadratic {ν x z u y : ℕ}
    (hz : 2 ≤ z) (hx : 0 < x) :
    Nonempty (ShortPolynomialWitnesses ν x z u y) ↔
      Nonempty (ShortQuadratic.PositiveWitnesses x z u y (L4 ν)) := by
  constructor
  · rintro ⟨h⟩
    exact h.exists_positiveWitnesses hz hx
  · rintro ⟨h⟩
    exact h.exists_shortPolynomial hz hx

/-- The explicit 58-witness quartic represents the supplied polynomial
at every positive input, for any admissible coding triple. -/
theorem short_quartic_master {ν : ℕ}
    {P : MvPolynomial (Fin (ν + 1)) ℤ} {z u y x : ℕ}
    (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4) (hnorm : Normalized P)
    (hI : Index ν P z u y) (hx : 0 < x) :
    Wset P x ↔ Wset (ShortQuadratic.quartic58 z u y (L4 ν)) x := by
  rw [short_polynomial_master hν hP hnorm hI hx,
    ShortQuadratic.wset_quartic58_iff]
  exact short_polynomial_iff_quadratic hI.two_le hx

/-- Choose the positive coding parameters once for all positive inputs.
The resulting polynomial has 58 natural witnesses, degree at most four,
and the normalization required by the earlier master theorems. -/
theorem short_quartic_representation {ν : ℕ}
    (P : MvPolynomial (Fin (ν + 1)) ℤ)
    (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4) (hnorm : Normalized P) :
    ∃ z u y : ℕ, 0 < z ∧ 0 < u ∧ 0 < y ∧ Index ν P z u y ∧
      (ShortQuadratic.quartic58 z u y (L4 ν)).totalDegree ≤ 4 ∧
      Normalized (ShortQuadratic.quartic58 z u y (L4 ν)) ∧
      ∀ x : ℕ, 0 < x →
        (Wset P x ↔ Wset (ShortQuadratic.quartic58 z u y (L4 ν)) x) := by
  obtain ⟨z, u, y, hz, hu, hy, hI⟩ := exists_index P hν
  exact ⟨z, u, y, hz, hu, hy, hI,
    ShortQuadratic.quartic58_totalDegree_le_four z u y (L4 ν),
    ShortQuadratic.quartic58_index_normalized hI hν,
    fun _ hx => short_quartic_master hν hP hnorm hI hx⟩

end Jones1982
