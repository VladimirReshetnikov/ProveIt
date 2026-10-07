import OAI.Combinatorics.Progressions.Estimates.RationalFormalStageGeometry

namespace OAI

section

namespace Erdos3

theorem formalGeometryHeight_ge_input (n r H : ℕ) : H ≤ formalGeometryHeight n r H :=
  (Nat.le_max_left H _).trans (Nat.le_max_left _ _)

theorem formalBracketMatrixHeight_le_exp (n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (formalBracketMatrixHeight n H : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
  have hh : (H : ℝ) * H * H ≤ Real.exp (3 * p) := by
    calc
      _ ≤ Real.exp p * Real.exp p * Real.exp p :=
        mul_le_mul (mul_le_mul hH hH (Nat.cast_nonneg _) (Real.exp_nonneg _)) hH
          (Nat.cast_nonneg _) (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hpow := pow_le_pow_left₀
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg H) (Nat.cast_nonneg H)) (Nat.cast_nonneg H)) hh (n ^ 2)
  rw [← Real.exp_nat_mul] at hpow
  have hinner : (((n ^ 2 + 1) * (H * H * H) ^ (n ^ 2)) * H : ℕ) ≤
      Real.exp ((n : ℝ) ^ 2 + n ^ 2 * (3 * p) + p) := by
    push_cast
    rw [Real.exp_add, Real.exp_add]
    apply mul_le_mul _ hH (Nat.cast_nonneg H) (by positivity)
    exact mul_le_mul (Real.add_one_le_exp ((n : ℝ) ^ 2))
      (by simpa only [Nat.cast_pow] using hpow) (by positivity) (Real.exp_nonneg _)
  have hout := pow_le_pow_left₀
    (Nat.cast_nonneg (((n ^ 2 + 1) * (H * H * H) ^ (n ^ 2)) * H)) hinner n
  rw [← Real.exp_nat_mul] at hout
  have htotal : (formalBracketMatrixHeight n H : ℝ) ≤
      Real.exp ((n : ℝ) + n * (n ^ 2 + n ^ 2 * (3 * p) + p)) := by
    unfold formalBracketMatrixHeight
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Real.exp_add]
    exact mul_le_mul (Real.add_one_le_exp n) hout (by positivity) (Real.exp_nonneg _)
  apply htotal.trans (Real.exp_le_exp.mpr ?_)
  calc
    (n : ℝ) + n * (n ^ 2 + n ^ 2 * (3 * p) + p) ≤
        p + p * (p ^ 2 + p ^ 2 * (3 * p) + p) := by gcongr
    _ ≤ (p + 2) ^ 5 := by
      have h : 0 ≤ p ^ 5 + 7 * p ^ 4 + 39 * p ^ 3 + 79 * p ^ 2 + 79 * p + 32 := by positivity
      nlinarith

theorem formalCurrentMatrixHeight_le_exp (n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (formalCurrentMatrixHeight n H : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
  have hh : (H : ℝ) * H ≤ Real.exp (2 * p) := by
    rw [show 2 * p = p + p by ring, Real.exp_add]
    exact mul_le_mul hH hH (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hpow := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg H) (Nat.cast_nonneg H)) hh n
  rw [← Real.exp_nat_mul] at hpow
  have htotal : (formalCurrentMatrixHeight n H : ℝ) ≤ Real.exp ((n : ℝ) + n * (2 * p)) := by
    unfold formalCurrentMatrixHeight
    push_cast
    rw [Real.exp_add]
    exact mul_le_mul (Real.add_one_le_exp n) hpow (by positivity) (Real.exp_nonneg _)
  apply htotal.trans (Real.exp_le_exp.mpr ?_)
  have hnp : (n : ℝ) * (2 * p) ≤ p * (2 * p) := mul_le_mul_of_nonneg_right hn (by positivity)
  have h : 0 ≤ p ^ 3 + 4 * p ^ 2 + 11 * p + 8 := by positivity
  nlinarith

theorem formalGeometryHeight_le_exp (n r H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hr : (r : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (formalGeometryHeight n r H : ℝ) ≤ Real.exp ((((p + 2) ^ 9) + 2) ^ 5) := by
  let q := (p + 2) ^ 9
  let M := max H (homogeneousIntersectionBasisHeight n r H)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := le_power_budget hp (by decide : 1 ≤ 9)
  have hMq : (M : ℝ) ≤ Real.exp q := by
    rw [Nat.cast_max]
    exact max_le (hH.trans (Real.exp_le_exp.mpr hpq)) (stepDrop_basis_height_budget n r H hp hn hr hH)
  have hq5 : q ≤ (q + 2) ^ 5 := le_power_budget hq (by decide : 1 ≤ 5)
  have h35 : (q + 2) ^ 3 ≤ (q + 2) ^ 5 :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ q + 2) (by decide : 3 ≤ 5)
  change ((max M (max (formalCurrentMatrixHeight n M) (formalBracketMatrixHeight n M)) : ℕ) : ℝ) ≤ _
  rw [Nat.cast_max M (max (formalCurrentMatrixHeight n M) (formalBracketMatrixHeight n M)),
    Nat.cast_max (formalCurrentMatrixHeight n M) (formalBracketMatrixHeight n M)]
  exact max_le (hMq.trans (Real.exp_le_exp.mpr hq5))
    (max_le ((formalCurrentMatrixHeight_le_exp n M hq (hn.trans hpq) hMq).trans
      (Real.exp_le_exp.mpr h35)) (formalBracketMatrixHeight_le_exp n M hq (hn.trans hpq) hMq))

theorem exists_formal_geometry_uniform_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (n r H : ℕ) (p : ℝ), 0 ≤ p →
      (n : ℝ) ≤ p → (r : ℝ) ≤ 5 * p → (H : ℝ) ≤ Real.exp p →
      (formalGeometryHeight n r H : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget
    (((((Polynomial.X + 2) ^ 3 + 2) ^ 9) + 2) ^ 5)
  refine ⟨C, hC, fun n r H p hp hn hr hH => ?_⟩
  let t := (p + 2) ^ 3
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_power_budget hp (by decide : 1 ≤ 3)
  have hrt : (r : ℝ) ≤ t := by
    have h : 0 ≤ p ^ 3 + 6 * p ^ 2 + 7 * p + 8 := by positivity
    dsimp [t]
    nlinarith
  have hcap : ((t + 2) ^ 9 + 2) ^ 5 ≤ (p + C) ^ C := by
    simpa [t, Polynomial.eval₂_pow] using hbound p hp
  exact (formalGeometryHeight_le_exp n r H ht (hn.trans hpt) hrt
    (hH.trans (Real.exp_le_exp.mpr hpt))).trans (Real.exp_le_exp.mpr hcap)

end Erdos3

end

end OAI
