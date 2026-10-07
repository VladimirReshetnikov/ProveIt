import OAI.Combinatorics.Progressions.Dynamics.PatchTopNetBudget

namespace OAI

section

namespace Erdos3

theorem exists_patch_top_net_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d : ℕ) (M L p : ℝ),
      0 ≤ p → 0 ≤ M → 0 ≤ L → (d : ℝ) ≤ p → M ≤ Real.exp p → L ≤ Real.exp p →
      ∃ N : ℕ, 0 < N ∧ ((N + 1 : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        (((N + 1) ^ (d * (d + 1) ^ s) : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        patchTopNetError d s N M < 1 / 4 ∧
        L * patchTopNetError d s N M ≤ Real.exp (-p) / 2 := by
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := Polynomial.C s + Polynomial.C s * X + X + 4 +
    Polynomial.C s * Polynomial.C s * X * (X + 1) + 2 * X + 6
  let I : Polynomial ℕ := X * (X + 1) ^ s
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget (Q + I * Q)
  refine ⟨C, hC, ?_⟩
  intro d M L p hp hM hL hd hMp hLp
  let q := patchTopNetNumeratorLog s p + 2 * p + 6
  have hq : 0 ≤ q := by
    have := patchTopNetNumeratorLog_nonneg s hp
    dsimp only [q]
    positivity
  have hcount : 0 ≤ p * (p + 1) ^ s := by positivity
  have ht : q + p * (p + 1) ^ s * q ≤ (p + 2) ^ C := by
    simpa [Q, I, X, q, patchTopNetNumeratorLog, Polynomial.eval₂_pow] using hbudget p hp
  have hqp : q ≤ (p + 2) ^ C := by nlinarith
  have hcp : p * (p + 1) ^ s * q ≤ (p + 2) ^ C := by linarith
  obtain ⟨N, hN, hNbound, hsmall, hloss⟩ := exists_small_patch_top_mesh d s hp hM hL hd hMp hLp
  refine ⟨N, hN, hNbound.trans (Real.exp_le_exp.mpr hqp), ?_, hsmall, hloss⟩
  have hdc : ((d * (d + 1) ^ s : ℕ) : ℝ) ≤ p * (p + 1) ^ s := by
    push_cast
    gcongr
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp q) ^ (d * (d + 1) ^ s) := pow_le_pow_left₀ (by positivity) hNbound _
    _ = Real.exp (((d * (d + 1) ^ s : ℕ) : ℝ) * q) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (p * (p + 1) ^ s * q) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hdc hq)
    _ ≤ _ := Real.exp_le_exp.mpr hcp

end Erdos3

end

end OAI
