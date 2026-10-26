import Mathlib.Tactic
import Mathlib.Data.Int.Order.Units

namespace DiophantineConsistency.ShortSystem

private theorem unit_eq_one {a b : ℤ} (h : a * b = 1) (hne : a ≠ -1) : a = 1 := by
  exact (Int.eq_one_or_neg_one_of_mul_eq_one h).resolve_right hne

def residualSum {R : Type*} [CommRing R] (n0 n1 na ns nk nt : R) : R :=
  (n0 - 1) ^ 2 + (n1 - 1) ^ 2 + (na - 1) ^ 2 + (ns - 1) ^ 2 + (nk * nt - 1) ^ 2

theorem product_eq_one_iff (n0 n1 na nk nt ns : ℤ)
    (h0 : n0 ≠ -1) (h1 : n1 ≠ -1) (hs : ns ≠ -1)
    (ha : ns = 1 → na ≠ -1) :
    n0 * n1 * na * nk * nt * ns = 1 ↔
      n0 = 1 ∧ n1 = 1 ∧ na = 1 ∧ ns = 1 ∧ nk * nt = 1 := by
  constructor
  · intro hp
    have hs1 : ns = 1 := unit_eq_one (b := n0 * n1 * na * nk * nt)
      (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hp) hs
    have h01 : n0 = 1 := unit_eq_one (b := n1 * na * nk * nt * ns)
      (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hp) h0
    have h11 : n1 = 1 := unit_eq_one (b := n0 * na * nk * nt * ns)
      (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hp) h1
    have ha1 : na = 1 := unit_eq_one (b := n0 * n1 * nk * nt * ns)
      (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hp) (ha hs1)
    exact ⟨h01, h11, ha1, hs1, by simpa only [h01, h11, ha1, hs1, one_mul, mul_one] using hp⟩
  · rintro ⟨h01, h11, ha1, hs1, hkt⟩
    simpa only [h01, h11, ha1, hs1, one_mul, mul_one] using hkt

#print axioms product_eq_one_iff

theorem residualSum_zero_iff (n0 n1 na ns nk nt : ℤ) :
    residualSum n0 n1 na ns nk nt = 0 ↔
      n0 = 1 ∧ n1 = 1 ∧ na = 1 ∧ ns = 1 ∧ nk * nt = 1 := by
  simp (disch := positivity) only [residualSum, add_eq_zero_iff_of_nonneg,
    sq_eq_zero_iff, sub_eq_zero, and_assoc]

#print axioms residualSum_zero_iff

end DiophantineConsistency.ShortSystem
