import DiophantineConsistency.MarginSeparation

/-! # The package-52 finalizer from its arithmetic register identities -/

namespace DiophantineConsistency.RatioMarginFinalizer

open MarginSeparation

/-- The literal package-52 finalizer is exact on the stated ratio-register
domain. Every bound used to separate the radicals is derived here from
positive register bounds and their polynomial identities. -/
theorem exists_value_zero_iff
    {P K A C D E F G H I k W J Q Y cap g m : ℤ}
    (hP : 0 < P) (hK : 2 ≤ K) (hA : 2 ≤ A) (hC : 1 ≤ C)
    (hE : 1 ≤ E) (hH : 1 ≤ H) (hk : 3 ≤ k) (hW : 0 < W) (hWC : W < C)
    (hJ : 0 < J) (hY : 2 ≤ Y) (hcap : 0 < cap) (hg : 0 ≤ g)
    (hPA : P < A ^ 2)
    (hDeq : D = (A ^ 2 - 1) * C ^ 2 + 1)
    (hEeq : E = k * D * C)
    (hFeq : F = (A ^ 2 - 1) * E ^ 2 + 1)
    (hGeq : G = A + F * (C * D + 1 - A))
    (hIeq : I = (G ^ 2 - 1) * H ^ 2 + 1)
    (hQeq : Q = 3 * W * C - 2 * (W ^ 2 - 1))
    (hmeq : m = (K ^ 2 - 4 * (C - K * Y) ^ 2) * cap - 8 * g * K ^ 2) :
    (∃ n : ℕ, MarginFinalizer.value ((P ^ 2 - 1) * K ^ 2 + 1) (D * F * I)
      (P * K) (k * (8 * D ^ 2 - 4 * D - 1) * G * H) J Q m n = 0) ↔
      IsSquare ((P ^ 2 - 1) * K ^ 2 + 1) ∧ IsSquare (D * F * I) ∧ J ∣ Q ∧ 0 < m := by
  obtain ⟨hCD, hAF, hAI⟩ := pell_register_bounds hA hC hE hH hDeq hFeq hGeq hIeq
  have hA0 : 0 < A := by omega
  have hD0 : 0 < D := by nlinarith only [hCD, sq_nonneg C]
  have hD1 : 1 ≤ D := by omega
  have hF0 : 0 < F := (sq_pos_of_pos hA0).trans_le hAF
  have hI0 : 0 < I := (sq_pos_of_pos hA0).trans_le hAI
  have hCDDA : A ^ 2 ≤ D := by
    rw [hDeq]
    have hAm : 0 ≤ A ^ 2 - 1 := by nlinarith only [hA]
    have hCm : 0 ≤ C ^ 2 - 1 := by nlinarith only [hC]
    nlinarith only [mul_nonneg hAm hCm]
  have hCDD : D ≤ C * D := by
    nlinarith only [mul_nonneg (show 0 ≤ C - 1 by omega) (le_of_lt hD0)]
  have hAG : A ≤ G := by
    rw [hGeq]
    exact le_add_of_nonneg_right (mul_nonneg (le_of_lt hF0) (by nlinarith only [hCDDA, hCDD, hA]))
  have hG1 : 1 ≤ G := by omega
  have hG0 : 0 < G := by omega
  have hk0 : 0 < k := by omega
  have hk2 : 9 ≤ k ^ 2 := by nlinarith only [hk]
  have hDF := NearSquareFinalizer.pell_product_identity A C D E F k hDeq hEeq hFeq
  obtain ⟨hV1, _, hbV⟩ := NearSquareFinalizer.full_majorant_bounds
    hk0 hk2 hD1 hF0 hG0 hH hDF hIeq
  obtain ⟨ha0, hV0, haV⟩ := first_majorant hP hK
  have hb0 : 0 < D * F * I := by positivity
  obtain ⟨hQ0, hQbound⟩ := Q_bounds hW hWC
  rw [← hQeq] at hQ0 hQbound
  have hQV1 := Q_lt_second_majorant hQbound hCD hD1 hk hG1 hH
  apply MarginFinalizer.exists_value_zero_iff (le_of_lt ha0) (le_of_lt hb0)
    hV0 hV1 haV (by simpa only [mul_assoc] using hbV) hJ hQ0 hQV1
  intro hm
  have hsmall := radicand_lt_of_margin_pos hP hK hA0 hY hcap hg hPA hCD hAF hAI
    (by simpa only [← hmeq] using hm)
  linarith only [hsmall, hb0]

end DiophantineConsistency.RatioMarginFinalizer
