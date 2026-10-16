import GowersSzemeredi.Proofs15DegenerateRange

/-!
# Degenerate higher-dimensional arrangements

This file proves Lemma 15.4 as the case `m = 1` of the range count
`degenerate_count_within_le` (`Proofs15DegenerateRange`): with coefficients
in `[−1, 1]` the dependences are exactly the ternary ones
(`isDegenerateWithin_one_iff`).
-/

set_option autoImplicit false

namespace LeanProofs.GowersSzemeredi

/-- Lemma 15.4: the corrected odd-prime bound for degenerate arrangements. -/
theorem lemma_15_4_holds : lemma_15_4 := by
  intro N k d _ hprime hodd hk hd
  have h := degenerate_count_within_le N 1 k d hprime hodd hk hd
  rwa [show degenerateGeneralArrangementCountWithin (N := N) (k := k) 1 d =
      degenerateGeneralArrangementCount (N := N) (k := k) d by
    simp only [degenerateGeneralArrangementCountWithin, degenerateGeneralArrangementCount,
      isDegenerateWithin_one_iff], show (2 * ((1 : Nat) : Real) + 1) = 3 by norm_num] at h

end LeanProofs.GowersSzemeredi
