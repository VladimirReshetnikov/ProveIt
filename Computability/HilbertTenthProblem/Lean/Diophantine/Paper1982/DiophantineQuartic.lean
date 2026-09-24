import Diophantine.Paper1982.EnumerationQuartic
import Diophantine.Paper1982.ShortQuarticMaster

/-!
# Fifty-eight witnesses for every Diophantine set

The 1978 enumeration first gives a finite quadratic gate system for an
arbitrary Diophantine set. Splitting its integer nodes into differences of
natural witnesses gives a normalized quartic. The explicit §5 compression
then reduces its witness count to 58, uniformly for all positive inputs.

This theorem assumes a Diophantine representation, with no restriction on
its original degree or number of variables. The further statement that
every recursively enumerable set has such a representation is not assumed.
-/

namespace Jones1982

/-- Every Diophantine set has a normalized polynomial representation of
degree at most four with 58 natural witnesses, on all positive inputs. -/
theorem diophantine_quartic58 {S : Set ℕ} (hS : Jones1978.IsDiophantine S) :
    ∃ Q : MvPolynomial (Fin 59) ℤ, Q.totalDegree ≤ 4 ∧ Normalized Q ∧
      ∀ x : ℕ, 0 < x → (x ∈ S ↔ Wset Q x) := by
  obtain ⟨ν, hν, P, hP, hnorm, hSrep⟩ :=
    EnumerationQuartic.exists_normalized_quartic_representation hS
  obtain ⟨z, u, y, _, _, _, _, hdegree, hnormalized, hcompression⟩ :=
    short_quartic_representation P hν hP hnorm
  exact ⟨ShortQuadratic.quartic58 z u y (L4 ν), hdegree, hnormalized,
    fun x hx => (hSrep x hx).trans (hcompression x hx)⟩

end Jones1982
