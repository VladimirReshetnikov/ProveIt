import OAI.Combinatorics.Progressions.Polynomial.WeylStepScales

/-! This module keeps `two_pow_natDegree_le_eval_two`; the rest of the development,
with its description, is in `Proofs05WeylConstantBoundsSide`, outside the final
route. -/
set_option autoImplicit false
namespace LeanProofs.GowersSzemeredi

open Polynomial

/-- A nonzero natural polynomial is at least `2^natDegree` at `2`. -/
theorem two_pow_natDegree_le_eval_two (P : Polynomial ℕ) (hP : P ≠ 0) :
    2 ^ P.natDegree ≤ P.eval 2 := by
  rw [eval_eq_sum_range]
  have hlc : 1 ≤ P.coeff P.natDegree :=
    Nat.one_le_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hP)
  calc 2 ^ P.natDegree ≤ P.coeff P.natDegree * 2 ^ P.natDegree := Nat.le_mul_of_pos_left _ hlc
    _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * 2 ^ i :=
      Finset.single_le_sum (f := fun i => P.coeff i * 2 ^ i) (fun _ _ => Nat.zero_le _)
        (Finset.self_mem_range_succ _)

end LeanProofs.GowersSzemeredi
