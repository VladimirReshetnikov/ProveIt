import Mathlib.Tactic
import Mathlib.Data.Int.Order.Units

namespace DiophantineConsistency.ShortSystem

private theorem unit_eq_one {a b : ℤ} (h : a * b = 1) (hne : a ≠ -1) : a = 1 := by
  have hu : IsUnit a := IsUnit.of_mul_eq_one_right b (by simpa only [mul_comm] using h)
  rcases Int.isUnit_iff.mp hu with hpos | hneg
  · exact hpos
  · exact (hne hneg).elim

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
      (by calc ns * (n0 * n1 * na * nk * nt) = n0 * n1 * na * nk * nt * ns := by ring
               _ = 1 := hp) hs
    have h01 : n0 = 1 := unit_eq_one (b := n1 * na * nk * nt * ns)
      (by calc n0 * (n1 * na * nk * nt * ns) = n0 * n1 * na * nk * nt * ns := by ring
               _ = 1 := hp) h0
    have h11 : n1 = 1 := unit_eq_one (b := n0 * na * nk * nt * ns)
      (by calc n1 * (n0 * na * nk * nt * ns) = n0 * n1 * na * nk * nt * ns := by ring
               _ = 1 := hp) h1
    have ha1 : na = 1 := unit_eq_one (b := n0 * n1 * nk * nt * ns)
      (by calc na * (n0 * n1 * nk * nt * ns) = n0 * n1 * na * nk * nt * ns := by ring
               _ = 1 := hp) (ha hs1)
    exact ⟨h01, h11, ha1, hs1, by simpa only [h01, h11, ha1, hs1, one_mul, mul_one] using hp⟩
  · rintro ⟨h01, h11, ha1, hs1, hkt⟩
    simpa only [h01, h11, ha1, hs1, one_mul, mul_one] using hkt

#print axioms product_eq_one_iff

theorem residualSum_zero_iff (n0 n1 na ns nk nt : ℤ) :
    residualSum n0 n1 na ns nk nt = 0 ↔
      n0 = 1 ∧ n1 = 1 ∧ na = 1 ∧ ns = 1 ∧ nk * nt = 1 := by
  unfold residualSum
  constructor
  · intro h
    have h0 : (n0 - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (n1 - 1), sq_nonneg (na - 1), sq_nonneg (ns - 1),
        sq_nonneg (nk * nt - 1), sq_nonneg (n0 - 1)]
    have h1 : (n1 - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (n0 - 1), sq_nonneg (na - 1), sq_nonneg (ns - 1),
        sq_nonneg (nk * nt - 1), sq_nonneg (n1 - 1)]
    have ha : (na - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (n0 - 1), sq_nonneg (n1 - 1), sq_nonneg (ns - 1),
        sq_nonneg (nk * nt - 1), sq_nonneg (na - 1)]
    have hs : (ns - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (n0 - 1), sq_nonneg (n1 - 1), sq_nonneg (na - 1),
        sq_nonneg (nk * nt - 1), sq_nonneg (ns - 1)]
    have hkt : (nk * nt - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (n0 - 1), sq_nonneg (n1 - 1), sq_nonneg (na - 1),
        sq_nonneg (ns - 1), sq_nonneg (nk * nt - 1)]
    exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp h0), sub_eq_zero.mp (sq_eq_zero_iff.mp h1),
      sub_eq_zero.mp (sq_eq_zero_iff.mp ha), sub_eq_zero.mp (sq_eq_zero_iff.mp hs),
      sub_eq_zero.mp (sq_eq_zero_iff.mp hkt)⟩
  · rintro ⟨rfl, rfl, rfl, rfl, hkt⟩
    simp only [hkt, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero]

#print axioms residualSum_zero_iff

end DiophantineConsistency.ShortSystem
