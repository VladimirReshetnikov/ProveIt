import GowersSzemeredi.Proofs13EndpointAdditiveCorrection

/-! Correct arbitrary rows over ZMod to scalar multiplication. Large
failure rows are charged at their trivial error, giving a uniform factor
six without a smallness assumption on the averaged test error. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem endpoint_zmod_addHom_scalar {N : Nat} [NeZero N] (v : ZMod N →+ ZMod N) (h : ZMod N) :
    v h = v 1 * h := by
  calc
    _ = v (h.val • (1 : ZMod N)) := by simp [nsmul_eq_mul]
    _ = h.val • v 1 := v.map_nsmul _ _
    _ = _ := by simp [nsmul_eq_mul, mul_comm]

theorem endpoint_row_correction {N : Nat} [NeZero N] (u : ZMod N → ZMod N) :
    ∃ c : ZMod N, endpointError u (fun h => c * h) ≤ 6 * endpointAdditiveFailure u := by
  by_cases hs : endpointAdditiveFailure u < 1 / 6
  · obtain ⟨v, _, hv⟩ := endpoint_additive_correction u hs
    have he : (fun h => v 1 * h) = v := funext (fun h => (endpoint_zmod_addHom_scalar v h).symm)
    refine ⟨v 1, ?_⟩
    rw [he]
    have hpos : 0 ≤ endpointAdditiveFailure u := endpointError_nonneg _ _
    linarith only [hv, hpos]
  · refine ⟨0, ?_⟩
    have ht := endpointError_le_one u (fun h => (0 : ZMod N) * h)
    have hlarge := le_of_not_gt hs
    linarith only [ht, hlarge]

theorem endpoint_rows_correction {N : Nat} [NeZero N] (phi : ZMod N × ZMod N → ZMod N) (tau : Real)
    (hfailure : (𝔼 k : ZMod N, endpointAdditiveFailure (fun h => phi (h, k))) ≤ tau) :
    ∃ a : ZMod N → ZMod N, endpointError phi (fun p => a p.2 * p.1) ≤ 6 * tau := by
  choose a ha using fun k : ZMod N => endpoint_row_correction (fun h => phi (h, k))
  refine ⟨a, ?_⟩
  have he : endpointError phi (fun p => a p.2 * p.1) =
      𝔼 k : ZMod N, endpointError (fun h => phi (h, k)) (fun h => a k * h) := by
    unfold endpointError
    rw [endpoint_expect_prod, Finset.expect_comm]
  rw [he]
  calc
    _ ≤ 𝔼 k : ZMod N, 6 * endpointAdditiveFailure (fun h => phi (h, k)) :=
      Finset.expect_le_expect (fun k _ => ha k)
    _ = 6 * (𝔼 k : ZMod N, endpointAdditiveFailure (fun h => phi (h, k))) := (Finset.mul_expect _ _ _).symm
    _ ≤ 6 * tau := mul_le_mul_of_nonneg_left hfailure (by norm_num)

end LeanProofs.GowersSzemeredi
