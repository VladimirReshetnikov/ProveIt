import GowersSzemeredi.Proofs16WithLift
import GowersSzemeredi.Proofs16PolyBaseCase

/-! A concrete two-dimensional slice provider from Freiman families.

If each final-coordinate section is covered by `q` order-eight Freiman
graphs, all `r` sampled sections can be linearized simultaneously with the
polynomial base case. Padding the sample count to `max 1 r` handles the
empty sample without a separate cover convention. The graph count is
`3 * (max 1 r * q)` and is independent of the requested loss.

`section16_freiman_slice_provider_ranges`,
`section16_slice_provider_of_freiman_families` and
`section16_two_dimensional_cover_of_freiman_families` are in
`Proofs16FreimanSliceProviderSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-- The polynomial base exponent satisfies the range required by the lift. -/
theorem polyBaseExponent_le_one {q : Nat} {sigma : Real} (hq : 0 < q)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) : polyBaseExponent q sigma ≤ 1 := by
  have hη0 := polyBase_loss_pos hq hs
  have hη1 := polyBase_loss_le_one hq hs1
  have hq1 : (1 : Real) ≤ q := by exact_mod_cast hq
  have hinv : (q : Real)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq1
  have hpow : (sigma / q) ^ 2 ≤ (1 : Real) := by nlinarith
  have ha : polyBaseCorExponent q sigma ≤ 1 := by
    unfold polyBaseCorExponent
    calc
      (2 : Real) ^ (-(14 : Real)) * (sigma / q) ^ 2 * (q : Real)⁻¹
          ≤ 1 * 1 * 1 := by
            gcongr
            norm_num
      _ = 1 := by norm_num
  exact (polyBaseExponent_le_half hq hs hs1).trans (by linarith)

end LeanProofs.GowersSzemeredi
