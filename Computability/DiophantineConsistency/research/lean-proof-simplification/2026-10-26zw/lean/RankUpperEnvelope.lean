import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The reduced arithmetic box underlying NativePellBootstrap.source_window_bound.
This file has no project-source or cached-project-object dependency.
-/

namespace DiophantineProofIdeas.RankUpperEnvelope

def rankValue (q F alpha J MC MF : ℤ) : ℤ :=
  ((q - 1) * (q - F) + alpha) * (q ^ 2 - 1) + (MC + MF * q) * J

/-- The entire upper-bound argument is one nonnegative deficit. -/
theorem deficit_identity (q beta F alpha J MC MF : ℤ)
    (hq : q = 1 + J * beta) :
    q ^ 4 - q ^ 3 - q - 1 - rankValue q F alpha J MC MF =
      q * (q ^ 2 - 1) * (F - 1) +
      (q ^ 2 - 1) * (q - F - alpha - 1) +
      (q + 1) * (J - 1) +
      J * ((beta - MC - 1) + q * (2 * beta - MF - 1)) := by
  unfold rankValue
  rw [hq]
  ring

/-- The sharp upper envelope for this arithmetic box. The two mask ports
need not be nonnegative; their existing strict upper bounds suffice. -/
theorem upper_envelope {q beta F alpha J MC MF : ℤ}
    (hq : q = 1 + J * beta) (hC : 0 < q - F - alpha)
    (hF : 0 < F) (ha : 0 < alpha) (hJ : 0 < J)
    (hMC : MC < beta) (hMF : MF < 2 * beta) :
    rankValue q F alpha J MC MF ≤ q ^ 4 - q ^ 3 - q - 1 := by
  have hq3 : 3 ≤ q := by omega
  have hsq : 0 ≤ q ^ 2 - 1 := by nlinarith
  have hF1 : 0 ≤ F - 1 := by omega
  have hC1 : 0 ≤ q - F - alpha - 1 := by omega
  have hJ1 : 0 ≤ J - 1 := by omega
  have hM : 0 ≤ beta - MC - 1 := by omega
  have hH : 0 ≤ 2 * beta - MF - 1 := by omega
  have hdeficit : 0 ≤ q ^ 4 - q ^ 3 - q - 1 - rankValue q F alpha J MC MF := by
    rw [deficit_identity q beta F alpha J MC MF hq]
    exact add_nonneg (add_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg (by omega) hsq) hF1) (mul_nonneg hsq hC1))
      (mul_nonneg (by omega) hJ1))
      (mul_nonneg hJ.le (add_nonneg hM (mul_nonneg (by omega) hH)))
  omega

/-- The old strict window follows immediately once its existing E≥q⁴
scale inequality is available. -/
theorem strict_window {q beta F alpha J MC MF E : ℤ}
    (hq : q = 1 + J * beta) (hC : 0 < q - F - alpha)
    (hF : 0 < F) (ha : 0 < alpha) (hJ : 0 < J)
    (hMC : MC < beta) (hMF : MF < 2 * beta) (hE : q ^ 4 ≤ E) :
    rankValue q F alpha J MC MF + 1 < E := by
  have hu := upper_envelope hq hC hF ha hJ hMC hMF
  have hq3 : 3 ≤ q := by omega
  have hcube : 0 < q ^ 3 := pow_pos (by omega) _
  omega

/-- Sharpness refers to the reduced arithmetic box, not existence of a
solution to the complete Diophantine source system. -/
theorem sharp_value (q : ℤ) :
    rankValue q 1 (q - 2) 1 (q - 2) (2 * q - 3) =
      q ^ 4 - q ^ 3 - q - 1 := by
  unfold rankValue
  ring

theorem sharp_box (q : ℤ) (hq : 3 ≤ q) :
    q = 1 + 1 * (q - 1) ∧
    0 < q - 1 - (q - 2) ∧ 0 < (1 : ℤ) ∧ 0 < q - 2 ∧
    0 < (1 : ℤ) ∧ q - 2 < q - 1 ∧ 2 * q - 3 < 2 * (q - 1) := by
  omega

#print axioms deficit_identity
#print axioms upper_envelope
#print axioms strict_window
#print axioms sharp_value
#print axioms sharp_box

end DiophantineProofIdeas.RankUpperEnvelope
