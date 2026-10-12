import GowersSzemeredi.Sections14_15

/-! A sharp elementary margin for the dyadic choice in Lemma 15.5. -/

namespace LeanProofs.GowersSzemeredi

/-- Keeping the relation between the dyadic scale and its amplification gives
three times the target, rather than estimating the two factors separately. -/
theorem selection_dyadic_margin {a q b : Real} {E : Nat}
    (ha : 0 < a) (hqlo : a / 4 ≤ q) (hqhi : q ≤ a / 2)
    (hamp : 1 ≤ q * b) (hE : 2 ≤ E) :
    3 * (a / 4) ^ E ≤ q ^ E * (a * b - 1) := by
  let x : Real := a / 4
  have hx : 0 < x := by dsimp [x]; positivity
  have hqx : x ≤ q := hqlo
  have hq2x : q ≤ 2 * x := by dsimp [x]; linarith
  have hq : 0 ≤ q := hx.le.trans hqx
  have hquadratic : 3 * x ^ 2 ≤ q ^ 2 * (a * b - 1) := by
    have hshape : 0 ≤ (q - x) * (3 * x - q) :=
      mul_nonneg (sub_nonneg.mpr hqx) (by linarith)
    have hscaled := mul_le_mul_of_nonneg_left hamp (mul_nonneg ha.le hq)
    dsimp [x] at hshape ⊢
    nlinarith only [hshape, hscaled]
  have hpower : x ^ (E - 2) ≤ q ^ (E - 2) :=
    pow_le_pow_left₀ hx.le hqx _
  have hsplit : E = (E - 2) + 2 := by omega
  change 3 * x ^ E ≤ q ^ E * (a * b - 1)
  calc
    3 * x ^ E = x ^ (E - 2) * (3 * x ^ 2) := by
      conv_lhs => rw [hsplit, pow_add]
      ring
    _ ≤ q ^ (E - 2) * (3 * x ^ 2) :=
      mul_le_mul_of_nonneg_right hpower (by positivity)
    _ ≤ q ^ (E - 2) * (q ^ 2 * (a * b - 1)) :=
      mul_le_mul_of_nonneg_left hquadratic (pow_nonneg hq _)
    _ = q ^ E * (a * b - 1) := by
      rw [← mul_assoc, ← pow_add, ← hsplit]

end LeanProofs.GowersSzemeredi
