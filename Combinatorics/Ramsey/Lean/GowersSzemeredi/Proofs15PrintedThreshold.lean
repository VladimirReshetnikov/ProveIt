import GowersSzemeredi.Proofs15Restriction
import GowersSzemeredi.Proofs15RestrictionSide

/-! The explicit largeness condition displayed in the corrected Lemma 15.5. -/

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- Lemma 15.5 with the displayed threshold, including the endpoint `eta = 1`.
The odd-prime convention is retained. -/
theorem lemma_15_5_printed_threshold
    (k N : Nat) [NeZero N] (alpha beta eta : Real)
    (hk : 1 ≤ k) (hprime : N.Prime) (hodd : Odd N)
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (heta : 0 < eta) (heta_one : eta ≤ 1)
    (hsize : (3 : Real) ^ (2 ^ (k + 4)) * k ≤
      (alpha * eta / 4) ^ arrangementSelectionExponent k * beta ^ 15 * N)
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (hcard : (B.card : Real) = beta * (N : Real) ^ (k + 1))
    (hrespected : alpha * beta ^ 15 * (N : Real) ^ (17 * k + 15) ≤
      respectedGeneralArrangementCount 8 B phi) :
    ∃ B' : Finset (Point N (k + 1)), B' ⊆ B ∧
      (alpha * eta / 4) ^ arrangementSelectionExponent k * beta ^ 15 *
        (N : Real) ^ (17 * k + 15) ≤ generalArrangementCount 8 B' ∧
      (1 - eta) * generalArrangementCount 8 B' ≤
        respectedGeneralArrangementCount 8 B' phi := by
  have hN3 : 3 ≤ N := by
    have hp := hprime.two_le
    have hn : N ≠ 2 := by
      intro h
      obtain ⟨j, hj⟩ := hodd
      omega
    omega
  have hthreshold : selectionSharpExplicitThreshold k alpha eta (beta ^ 15)
      ((3 : Real) ^ (16 * 2 ^ k) * k) ≤ (N : Real) := by
    unfold selectionSharpExplicitThreshold
    apply max_le
    · exact_mod_cast hN3
    · apply (div_le_iff₀ (by positivity)).mpr
      have hexp : 16 * 2 ^ k = 2 ^ (k + 4) := by
        rw [pow_add]
        ring
      rw [hexp]
      simpa only [mul_comm] using hsize
  exact selection_scale_estimate_sharp_explicit k alpha (beta ^ 15) eta hk
    halpha (pow_pos hbeta _) heta heta_one N hthreshold hprime hodd B phi
    (selection_arrangement_real_upper beta B hcard) hrespected

end LeanProofs.GowersSzemeredi
