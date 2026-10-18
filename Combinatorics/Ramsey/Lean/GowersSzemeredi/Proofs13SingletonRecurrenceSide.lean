import GowersSzemeredi.Proofs13SingletonRecurrence

/-! Declarations of `Proofs13SingletonRecurrence` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- The numerical cutoff used for the small case in the paper, including
its endpoint, implies the verified singleton-scale condition. -/
theorem lemma_13_5_printed_small_case {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (theta : Real)
    (h134 : IsStage134Data S theta D)
    (hscale : D.P.length ≤ 2 ^ (2 ^ (12 * D.q))) :
    ∃ E : Stage135Data N, IsStage135Data S D E := by
  apply lemma_13_5_singleton_scale S D theta h134
  have hR : (D.P.length : Real) ≤ (2 : Real) ^ (2 ^ (12 * D.q) : Nat) := by
    exact_mod_cast hscale
  have hroot := Real.rpow_le_rpow (Nat.cast_nonneg D.P.length) hR
    (show (0 : Real) ≤ (((2 ^ (12 * D.q) : Nat) : Real)⁻¹) by positivity)
  rw [Real.pow_rpow_inv_natCast (by norm_num) (by positivity)] at hroot
  simpa only [Nat.cast_pow, Nat.cast_ofNat, one_div] using hroot

end LeanProofs.GowersSzemeredi
