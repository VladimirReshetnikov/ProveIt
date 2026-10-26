/-!
UNCOMPILED audit candidates against the pinned ProveIt checkout.
These prove replacement statements without invoking the theorem being replaced.
No modifications to the source snapshot are required.
-/
import DiophantineConsistency.ShortSystem
import DiophantineConsistency.SelectiveCoefficientBounds
import DiophantineConsistency.CurrentHighDigits2011

namespace DiophantineConsistency.ShortSystem

theorem residualSum_zero_iff_candidate (n0 n1 na ns nk nt : ℤ) :
    residualSum n0 n1 na ns nk nt = 0 ↔
      n0 = 1 ∧ n1 = 1 ∧ na = 1 ∧ ns = 1 ∧ nk * nt = 1 := by
  simp only [residualSum, add_eq_zero_iff_of_nonneg, add_nonneg,
    sq_nonneg, sq_eq_zero_iff, sub_eq_zero, and_assoc]

-- Fallback: expose every nonnegative summand; no conditional simp discharge.
theorem residualSum_zero_iff_explicit_candidate (n0 n1 na ns nk nt : ℤ) :
    residualSum n0 n1 na ns nk nt = 0 ↔
      n0 = 1 ∧ n1 = 1 ∧ na = 1 ∧ ns = 1 ∧ nk * nt = 1 := by
  have h01 := add_nonneg (sq_nonneg (n0 - 1)) (sq_nonneg (n1 - 1))
  have h01a := add_nonneg h01 (sq_nonneg (na - 1))
  have h01as := add_nonneg h01a (sq_nonneg (ns - 1))
  rw [residualSum, add_eq_zero_iff_of_nonneg h01as (sq_nonneg (nk * nt - 1)),
    add_eq_zero_iff_of_nonneg h01a (sq_nonneg (ns - 1)),
    add_eq_zero_iff_of_nonneg h01 (sq_nonneg (na - 1)),
    add_eq_zero_iff_of_nonneg (sq_nonneg (n0 - 1)) (sq_nonneg (n1 - 1))]
  simp only [sq_eq_zero_iff, sub_eq_zero, and_assoc]

end DiophantineConsistency.ShortSystem

namespace DiophantineConsistency.SelectiveCoefficientBounds
open Polynomial
open SelectiveQuadraticCoding

-- T09: reuse the existing generic theorem immediately preceding the special case.
theorem half_base_bound_31_candidate (w : Fin 32 → ℕ) (u : Fin 31 → ℕ) (p : ℤ[X])
    {H : ℤ} (hH : 0 < H) (hp : ∀ i, |p.coeff i| ≤ H)
    {b t : ℕ} (hb : 0 < b) (ht : 1 ≤ t) (hu : ∀ i, u i < b)
    (hbase : (2 : ℤ) ^ t = 4096 * H * (b : ℤ) ^ 2) (n : ℕ) :
    |(encoded w (Fin.cases 1 (fun i => (u i : ℤ))) ^ 2 * p).coeff n| <
      2 ^ (t - 1) := by
  refine half_base_bound w u p hH hp hb ht hu ?_ n
  norm_num [hbase]

end DiophantineConsistency.SelectiveCoefficientBounds

namespace DiophantineConsistency.CurrentHighDigits2011
open CurrentMasks2011

-- T08: cosmetic experiment, NOT the preferred architecture.
-- Profile this branching proof before replacing the shared highDigits_lt proof.
theorem cellDigit_lt_candidate (j : ℕ) : cellDigit j < radix := by
  rw [cellDigit_formula]
  split_ifs <;> norm_num [radix]

end DiophantineConsistency.CurrentHighDigits2011

#print axioms DiophantineConsistency.ShortSystem.residualSum_zero_iff_candidate
#print axioms DiophantineConsistency.ShortSystem.residualSum_zero_iff_explicit_candidate
#print axioms DiophantineConsistency.SelectiveCoefficientBounds.half_base_bound_31_candidate
#print axioms DiophantineConsistency.CurrentHighDigits2011.cellDigit_lt_candidate
