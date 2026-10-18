import GowersSzemeredi.Proofs16CompressedCandidateBounds

/-! Declarations of `Proofs16CompressedCandidateBounds` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

theorem section16_compressed_budget_mono {r R : Nat} {b B : Real}
    (hr : r ≤ R) (hb : 0 ≤ b) (hbB : b ≤ B) :
    max b ((r.choose 2 : Real) * b * b) ≤ max B ((R.choose 2 : Real) * B * B) := by
  have hchoose : (r.choose 2 : Real) ≤ R.choose 2 := by exact_mod_cast Nat.choose_le_choose 2 hr
  have hB : 0 ≤ B := hb.trans hbB
  gcongr

/-- For two or more sample indices and a slice budget at least one, the
one-anchor fallback fits in the unordered-pair budget. -/
theorem section16_compressed_budget_eq {r : Nat} {b : Real} (hr : 2 ≤ r) (hb : 1 ≤ b) :
    max b ((r.choose 2 : Real) * b * b) = (r.choose 2 : Real) * b * b := by
  have hc : (1 : Real) ≤ r.choose 2 := by
    exact_mod_cast (show 1 ≤ r.choose 2 by simpa using Nat.choose_le_choose 2 hr)
  have hb0 := zero_le_one.trans hb
  apply max_eq_right
  calc
    b ≤ b * b := by nlinarith only [hb, hb0]
    _ ≤ (r.choose 2 : Real) * b * b := by nlinarith only [hc, sq_nonneg b]

/-- The new budget is strictly smaller than the former direct-plus-ordered-
pair budget whenever samples and slice lists are nonempty. -/
theorem section16_compressed_budget_lt_old {r : Nat} {b : Real} (hr : 0 < r) (hb : 1 ≤ b) :
    max b ((r.choose 2 : Real) * b * b) < (r : Real) * b + (r : Real) * r * b * b := by
  have hr1 : (1 : Real) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : Real) < r := by exact_mod_cast hr
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have hc : (r.choose 2 : Real) ≤ (r : Real) ^ 2 := by exact_mod_cast Nat.choose_le_pow r 2
  apply max_lt
  · have hprod : 0 < (r : Real) * r * b * b := by positivity
    have hfirst : b ≤ (r : Real) * b := le_mul_of_one_le_left hb0.le hr1
    linarith only [hprod, hfirst]
  · have hsecond := mul_le_mul_of_nonneg_right hc (sq_nonneg b)
    have hprod : 0 < (r : Real) * b := mul_pos hr0 hb0
    nlinarith only [hsecond, hprod]

end LeanProofs.GowersSzemeredi
