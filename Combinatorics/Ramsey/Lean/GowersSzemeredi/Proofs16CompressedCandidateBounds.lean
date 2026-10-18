import GowersSzemeredi.Proofs16CompressedInterpolation
import Mathlib.Data.Nat.Choose.Bounds

/-! Exact finite counts and quantitative savings for compressed interpolation.

`section16_compressed_budget_eq`, `section16_compressed_budget_lt_old` and
`section16_compressed_budget_mono` are in
`Proofs16CompressedCandidateBoundsSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16_compressed_candidate_mono {r p q : Nat} (hpq : p ≤ q) :
    section16CompressedCandidateCount r p ≤ section16CompressedCandidateCount r q := by
  unfold section16CompressedCandidateCount
  gcongr

theorem section16_compressed_candidate_bound {r p : Nat} {b : Real} (hp : (p : Real) ≤ b) :
    (section16CompressedCandidateCount r p : Real) ≤ max b ((r.choose 2 : Real) * b * b) := by
  have hb : 0 ≤ b := (Nat.cast_nonneg p).trans hp
  unfold section16CompressedCandidateCount
  push_cast
  gcongr

end LeanProofs.GowersSzemeredi
