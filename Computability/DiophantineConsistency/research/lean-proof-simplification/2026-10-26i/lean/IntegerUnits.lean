import Mathlib.Algebra.Group.Int.Units
import Mathlib.Tactic

namespace ProofSimplification.IntegerUnits

/-- Extract all factor units in one pass, then choose the forced signs. -/
theorem product_eq_one_iff (n0 n1 na nk nt ns : ℤ)
    (h0 : n0 ≠ -1) (h1 : n1 ≠ -1) (hs : ns ≠ -1)
    (ha : ns = 1 → na ≠ -1) :
    n0 * n1 * na * nk * nt * ns = 1 ↔
      n0 = 1 ∧ n1 = 1 ∧ na = 1 ∧ ns = 1 ∧ nk * nt = 1 := by
  constructor
  · intro hp
    have hu : IsUnit (n0 * n1 * na * nk * nt * ns) := hp.symm ▸ isUnit_one
    simp only [IsUnit.mul_iff, Int.isUnit_iff, or_iff_left h0,
      or_iff_left h1, or_iff_left hs] at hu
    rcases hu with ⟨⟨⟨⟨⟨h01, h11⟩, hau⟩, _⟩, _⟩, hs1⟩
    have ha1 := hau.resolve_right (ha hs1)
    exact ⟨h01, h11, ha1, hs1, by simpa only [h01, h11, ha1, hs1, one_mul, mul_one] using hp⟩
  · rintro ⟨h01, h11, ha1, hs1, hkt⟩
    simpa only [h01, h11, ha1, hs1, one_mul, mul_one] using hkt

#print axioms product_eq_one_iff
end ProofSimplification.IntegerUnits
