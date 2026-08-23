import IntegerPoints.GKSec33LGeHalf

/-!
# Graham--Kolesnik section 3.3: nonnegativity of `k`

Integer reciprocal phases at a common-multiple scale make every summand
equal to one.  They rule out `k < 0`; in the boundary case `k = 0`, the same
construction forces `l >= 1`.
-/

open Real Finset Filter

namespace LeanProofs.IntegerPoints

namespace GKSec33

/-- At any positive-factorial common-multiple scale, every character in the
Appendix A sum is exactly one. -/
theorem appendixSum_factorial_mul (N ν : ℕ) :
    GKAppendixA.appendixSum N
      (((2 * N).factorial * ν : ℕ) : ℝ) = (N : ℂ) := by
  unfold GKAppendixA.appendixSum
  rw [GKAppendixA.intRange_nat_two]
  calc
    ∑ n ∈ Finset.Ioc N (2 * N),
        e ((((2 * N).factorial * ν : ℕ) : ℝ) / (n : ℝ)) =
        ∑ _n ∈ Finset.Ioc N (2 * N), (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [Finset.mem_Ioc] at hn
      have hn0 : 0 < n := by omega
      have hd : n ∣ (2 * N).factorial :=
        Nat.dvd_factorial hn0 hn.2
      obtain ⟨m, hm⟩ := hd
      have hquot :
          (((2 * N).factorial * ν : ℕ) : ℝ) / (n : ℝ) =
            ((((m * ν : ℕ) : ℤ) : ℝ)) := by
        rw [hm]
        push_cast
        field_simp
      rw [hquot]
      exact KL.e_int ((m * ν : ℕ) : ℤ)
    _ = (N : ℂ) := by
      have hcard : 2 * N - N = N := by omega
      rw [Finset.sum_const, Nat.card_Ioc, hcard]
      simp

end GKSec33

end LeanProofs.IntegerPoints
