import DiophantineConsistency.MarginFinalizer

/-! # Arithmetic separation supplied by the package-52 margin -/

namespace DiophantineConsistency.MarginSeparation

/-- The concrete ratio registers satisfy `P<A^2` unconditionally. -/
theorem ratio_P_lt_A_sq {M U : ℤ} (hM : 0 < M) :
    2 * M ^ 2 * U < (M * (U + 1)) ^ 2 := by
  have h := mul_pos (sq_pos_of_pos hM)
    (by nlinarith [sq_nonneg U] : 0 < U ^ 2 + 1)
  nlinarith

/-- The three later Pell registers give the unconditional bounds used in
the margin-first separation argument. -/
theorem pell_register_bounds {A C E H D F G I : ℤ}
    (hA : 2 ≤ A) (hC : 1 ≤ C) (hE : 1 ≤ E) (hH : 1 ≤ H)
    (hDeq : D = (A ^ 2 - 1) * C ^ 2 + 1)
    (hFeq : F = (A ^ 2 - 1) * E ^ 2 + 1)
    (hGeq : G = A + F * (C * D + 1 - A))
    (hIeq : I = (G ^ 2 - 1) * H ^ 2 + 1) :
    C ^ 2 < D ∧ A ^ 2 ≤ F ∧ A ^ 2 ≤ I := by
  have hAm : 0 ≤ A ^ 2 - 1 := by nlinarith
  have hCm : 0 ≤ C ^ 2 - 1 := by nlinarith
  have hEm : 0 ≤ E ^ 2 - 1 := by nlinarith
  have hHm : 0 ≤ H ^ 2 - 1 := by nlinarith
  have hAD : A ^ 2 ≤ D := by rw [hDeq]; nlinarith [mul_nonneg hAm hCm]
  have hCD : C ^ 2 < D := by
    rw [hDeq]
    nlinarith [mul_nonneg (show 0 ≤ A ^ 2 - 2 by nlinarith) (sq_nonneg C)]
  have hAF : A ^ 2 ≤ F := by rw [hFeq]; nlinarith [mul_nonneg hAm hEm]
  have hD0 : 0 ≤ D := (sq_nonneg A).trans hAD
  have hF0 : 0 ≤ F := (sq_nonneg A).trans hAF
  have hCDD : D ≤ C * D := by nlinarith [mul_nonneg (show 0 ≤ C - 1 by omega) hD0]
  have hAG : A ≤ G := by
    have hca : 0 ≤ C * D + 1 - A := by nlinarith
    rw [hGeq]
    exact le_add_of_nonneg_right (mul_nonneg hF0 hca)
  have hGm : 0 ≤ G ^ 2 - 1 := by nlinarith
  have hGI : G ^ 2 ≤ I := by rw [hIeq]; nlinarith [mul_nonneg hGm hHm]
  have hAGsq : A ^ 2 ≤ G ^ 2 := by
    have := mul_self_le_mul_self (show 0 ≤ A by omega) hAG
    nlinarith
  exact ⟨hCD, hAF, hAGsq.trans hGI⟩

/-- The concrete positive `Q` is bounded by `3*C^2`, not necessarily by J. -/
theorem Q_bounds {W C : ℤ} (hW : 0 < W) (hWC : W < C) :
    0 < 3 * W * C - 2 * (W ^ 2 - 1) ∧
      3 * W * C - 2 * (W ^ 2 - 1) < 3 * C ^ 2 := by
  have hC : 0 < C := by omega
  have hW2 : 1 ≤ W ^ 2 := by nlinarith
  have hlow := mul_lt_mul_of_pos_left hWC hW
  have hhigh := mul_lt_mul_of_pos_right hWC hC
  constructor <;> nlinarith [sq_nonneg W]

/-- The second majorant strictly exceeds the concrete divisibility register. -/
theorem Q_lt_second_majorant {Q C D k G H : ℤ}
    (hQ : Q < 3 * C ^ 2) (hD : C ^ 2 < D) (hD1 : 1 ≤ D)
    (hk : 3 ≤ k) (hG : 1 ≤ G) (hH : 1 ≤ H) :
    Q < k * (8 * D ^ 2 - 4 * D - 1) * G * H := by
  have hfac : D < 8 * D ^ 2 - 4 * D - 1 := by
    nlinarith [mul_nonneg (show 0 ≤ D - 1 by omega) (show 0 ≤ D by omega)]
  have hfac0 : 0 < 8 * D ^ 2 - 4 * D - 1 := by omega
  have hkfac := mul_le_mul_of_nonneg_right hk (le_of_lt hfac0)
  have hT : 3 * D < k * (8 * D ^ 2 - 4 * D - 1) := by nlinarith
  have hT0 : 0 ≤ k * (8 * D ^ 2 - 4 * D - 1) := by positivity
  have hTG := mul_le_mul_of_nonneg_right hG hT0
  have hTG0 : 0 ≤ k * (8 * D ^ 2 - 4 * D - 1) * G := by positivity
  have hTGH := mul_le_mul_of_nonneg_right hH hTG0
  nlinarith

/-- A positive margin forces `C>K` already when `Y>=2`. -/
theorem coordinate_gt_of_margin_pos {C K Y cap g : ℤ}
    (hK : 0 < K) (hY : 2 ≤ Y) (hcap : 0 < cap) (hg : 0 ≤ g)
    (hm : 0 < (K ^ 2 - 4 * (C - K * Y) ^ 2) * cap - 8 * g * K ^ 2) :
    K < C := by
  have hgap : 0 < K ^ 2 - 4 * (C - K * Y) ^ 2 := by
    by_contra h
    have hmul := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) (le_of_lt hcap)
    have htail : 0 ≤ 8 * g * K ^ 2 := by positivity
    linarith
  by_contra h
  have hC : C ≤ K := by omega
  have hKY : 2 * K ≤ K * Y := by
    have := mul_le_mul_of_nonneg_left hY (le_of_lt hK)
    nlinarith
  have hCK : K ≤ -(C - K * Y) := by nlinarith
  have hsq : K ^ 2 ≤ (C - K * Y) ^ 2 := by
    have := mul_self_le_mul_self (le_of_lt hK) hCK
    nlinarith
  nlinarith [sq_nonneg K]

/-- The first Pell radicand has the unconditional strict majorant `P*K`. -/
theorem first_majorant {P K : ℤ} (hP : 0 < P) (hK : 2 ≤ K) :
    0 < (P ^ 2 - 1) * K ^ 2 + 1 ∧
      0 < P * K ∧ (P ^ 2 - 1) * K ^ 2 + 1 < (P * K) ^ 2 := by
  have hP1 : 0 ≤ P ^ 2 - 1 := by nlinarith
  have hnonneg := mul_nonneg hP1 (sq_nonneg K)
  refine ⟨by omega, by positivity, ?_⟩
  nlinarith [sq_nonneg (K - 2)]

/-- The source ratio-register bounds separate its two radicands once `C>K`.
The conclusion is stronger than the weighted separation needed by the norm. -/
theorem radicand_lt_of_coordinate_gt {P K A C D F I : ℤ}
    (hP : 0 < P) (hK : 2 ≤ K) (hA : 0 < A) (hKC : K < C)
    (hPA : P < A ^ 2) (hD : C ^ 2 < D)
    (hF : A ^ 2 ≤ F) (hI : A ^ 2 ≤ I) :
    (P ^ 2 - 1) * K ^ 2 + 1 < D * F * I := by
  have hK0 : 0 < K := by omega
  have hC : 0 < C := by omega
  have hD0 : 0 < D := by nlinarith [sq_nonneg C]
  have hF0 : 0 ≤ F := (sq_nonneg A).trans hF
  have hFI : A ^ 2 * A ^ 2 ≤ F * I :=
    mul_le_mul hF hI (sq_nonneg A) hF0
  have hP2 : P ^ 2 < (A ^ 2) ^ 2 :=
    (sq_lt_sq₀ (le_of_lt hP) (sq_nonneg A)).mpr hPA
  have hK2 : K ^ 2 < C ^ 2 :=
    (sq_lt_sq₀ (le_of_lt hK0) (le_of_lt hC)).mpr hKC
  have hDFI : C ^ 2 * (A ^ 2 * A ^ 2) < D * (F * I) :=
    (mul_lt_mul_of_pos_right hD (by positivity)).trans_le
      (mul_le_mul_of_nonneg_left hFI (le_of_lt hD0))
  calc
    (P ^ 2 - 1) * K ^ 2 + 1 < P ^ 2 * K ^ 2 := by nlinarith
    _ < P ^ 2 * C ^ 2 := mul_lt_mul_of_pos_left hK2 (sq_pos_of_pos hP)
    _ < (A ^ 2) ^ 2 * C ^ 2 := mul_lt_mul_of_pos_right hP2 (sq_pos_of_pos hC)
    _ = C ^ 2 * (A ^ 2 * A ^ 2) := by ring
    _ < D * (F * I) := hDFI
    _ = D * F * I := by ring

/-- The exact arithmetic margin of package 52 supplies conditional radical
separation without any square or native-compiler hypothesis. -/
theorem radicand_lt_of_margin_pos {P K A C D F I Y cap g : ℤ}
    (hP : 0 < P) (hK : 2 ≤ K) (hA : 0 < A) (hY : 2 ≤ Y)
    (hcap : 0 < cap) (hg : 0 ≤ g) (hPA : P < A ^ 2)
    (hD : C ^ 2 < D) (hF : A ^ 2 ≤ F) (hI : A ^ 2 ≤ I)
    (hm : 0 < (K ^ 2 - 4 * (C - K * Y) ^ 2) * cap - 8 * g * K ^ 2) :
    (P ^ 2 - 1) * K ^ 2 + 1 < D * F * I :=
  radicand_lt_of_coordinate_gt hP hK hA
    (coordinate_gt_of_margin_pos (by omega) hY hcap hg hm) hPA hD hF hI

end DiophantineConsistency.MarginSeparation
