import OAI.Combinatorics.Progressions.Lattices.ResidueIntervalFactors

namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

noncomputable def maskedIntervalApprox {S : Type*} [Fintype S] [DecidableEq S]
    (B r H : ℝ) (m : ℕ) [NeZero m]
    (F : (S → ℝ) → ℂ) (M : (S → ZMod m) → ℂ) (u : S → ℤ) : ℂ :=
  ∑ a : S → ZMod m, ∑ k : S → Fin (intervalSiteCount B r),
    (M a * F (fun i => intervalSiteCenter B r (k i))) *
      ((∏ i, residueIntervalSiteWeight B r H (a i) (k i) (u i) : ℝ) : ℂ)

theorem maskedIntervalApprox_eq {S : Type*} [Fintype S] [DecidableEq S]
    (B r H : ℝ) (m : ℕ) [NeZero m]
    (F : (S → ℝ) → ℂ) (M : (S → ZMod m) → ℂ) (u : S → ℤ) :
    maskedIntervalApprox B r H m F M u =
      M (fun i => (u i : ZMod m)) * intervalTensorApprox B r F (fun i => (u i : ℝ) / H) := by
  classical
  unfold maskedIntervalApprox
  simp_rw [prod_residueIntervalSiteWeight]
  rw [Finset.sum_eq_single (fun i => (u i : ZMod m))]
  · simp only [ite_true, one_mul]
    rw [intervalTensorApprox, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  · intro a _ ha
    simp only [Ne.symm ha, ite_false, zero_mul, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero]
  · simp

theorem maskedIntervalApprox_error {S : Type*} [Fintype S] [DecidableEq S]
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (H : ℝ) (m : ℕ) [NeZero m]
    (F : (S → ℝ) → ℂ) (M : (S → ZMod m) → ℂ) {K : ℝ≥0} {G : ℝ}
    (hF : LipschitzWith K F) (hG : 0 ≤ G) (hM : ∀ a, ‖M a‖ ≤ G)
    (u : S → ℤ) (hu : ∀ i, |(u i : ℝ) / H| ≤ B) :
    ‖M (fun i => (u i : ZMod m)) * F (fun i => (u i : ℝ) / H) -
      maskedIntervalApprox B r H m F M u‖ ≤ 2 * G * K * r := by
  rw [maskedIntervalApprox_eq, ← mul_sub, norm_mul]
  exact (mul_le_mul (hM _) (intervalTensorApprox_error hB hr F hF _ hu)
    (norm_nonneg _) hG).trans_eq (by ring)

theorem maskedIntervalApprox_coefficient_sum {S : Type*} [Fintype S] [DecidableEq S]
    (B r : ℝ) (m : ℕ) [NeZero m] (F : (S → ℝ) → ℂ) (M : (S → ZMod m) → ℂ)
    {G A : ℝ} (hG : 0 ≤ G) (hM : ∀ a, ‖M a‖ ≤ G) (hF : ∀ x, ‖F x‖ ≤ A) :
    (∑ a : S → ZMod m, ∑ k : S → Fin (intervalSiteCount B r),
      ‖M a * F (fun i => intervalSiteCenter B r (k i))‖) ≤
      (m : ℝ)^Fintype.card S * (intervalSiteCount B r : ℝ)^Fintype.card S * (G * A) := by
  calc
    _ ≤ ∑ _a : S → ZMod m, ∑ _k : S → Fin (intervalSiteCount B r), G * A := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul (hM a) (hF _) (norm_nonneg _) hG
    _ = _ := by simp [mul_assoc]

end Erdos3

end

end OAI
