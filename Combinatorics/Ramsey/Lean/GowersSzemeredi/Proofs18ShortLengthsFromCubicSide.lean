import GowersSzemeredi.Proofs18ShortLengthsFromCubic
import GowersSzemeredi.Proofs18EnvelopeBoundsSide

/-! Declarations of `Proofs18ShortLengthsFromCubic` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- **Theorem 18.2 with `L + 3` at every length `L ≤ 5`**, from the explicit base. -/
theorem theorem_18_2_L3_le_five {k : Nat} (hk : k ≤ 5) : Theorem182AtSharp 3 k :=
  theorem_18_2_L3_le_five_of envBound_three hk

end LeanProofs.GowersSzemeredi
