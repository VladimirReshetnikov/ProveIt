import DiophantineConsistency.FirstPellCarrier

/-!
# Focused checks for the first-Pell witness maps

The nontrivial example uses the second Pell solution for `E=7,Y=1`:
`tau=449,k=60,R=3`, with recovered quotient `h=8` and carrier `n=56`.
The least Pell solution illustrates why the strict rank hypothesis `1<R`
cannot simply be deleted from the forward theorem.
-/

namespace DiophantineConsistency.FirstPellCarrierChecks

open FirstPellCarrier

example : (7 : ℤ) ∣ 449 - 1 ∧ (60 : ℤ) < 449 ∧
    ((60 : ℤ) = 2 ∨ (4 : ℤ) * (2 * (7 * 1) + 1) ≤ 60) := by
  exact first_norm_facts_int (E := 7) (Y := 1) (tau := 449) (k := 60)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : (0 : ℤ) < 449 ∧ ∃ h : ℤ, 0 < h ∧ 60 - h * 7 - 3 = 1 := by
  exact restore_quotient (n := 56) (Y := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : ∃ n : ℤ, 0 < n ∧ 449 = 7 * n + 60 - 3 := by
  exact restore_carrier (h := 8) (Y := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example (h : ℤ) (hh : 60 - h * 7 - 3 = 1) : h = 8 := by
  exact quotient_unique (by norm_num) hh (by norm_num)

example (n : ℤ) (hn : 449 = 7 * n + 60 - 3) : n = 56 := by
  exact carrier_unique (by norm_num) hn (by norm_num)

/-- With rank one the first positive Pell solution restores h=0, not h>0. -/
example : (15 : ℤ) ^ 2 - (7 * 1) * (7 * 1 + 1) * 2 ^ 2 = 1 ∧
    (15 : ℤ) = 7 * 2 + 2 - 1 ∧
    ¬ ∃ h : ℤ, 0 < h ∧ 2 - h * 7 - 1 = 1 := by
  norm_num
  omega

#print axioms first_norm_facts
#print axioms restore_quotient
#print axioms restore_carrier
#print axioms exists_carrier_iff_index

end DiophantineConsistency.FirstPellCarrierChecks
