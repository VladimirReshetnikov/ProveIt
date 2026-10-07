import Mathlib.Analysis.Real.Pi.Bounds
import OAI.Combinatorics.Progressions.Dynamics.ModeThresholdLogBudget

namespace OAI

section

namespace Erdos3

def slowPolynomialSliceSlope (d n : ℕ) (M : ℝ) : ℝ :=
  (d + 1 : ℝ) * (n + 1 : ℝ) ^ d * M * n * d

noncomputable def slowPolynomialSliceRadius (d n : ℕ) (M : ℝ) : ℝ :=
  min 1 ((1 / (20 * Real.pi)) / (slowPolynomialSliceSlope d n M + 1))

theorem slowPolynomialSliceSlope_nonneg (d n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ slowPolynomialSliceSlope d n M := by
  unfold slowPolynomialSliceSlope
  positivity

theorem slowPolynomialSliceRadius_eq (d n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    slowPolynomialSliceRadius d n M =
      (1 / (20 * Real.pi)) / (slowPolynomialSliceSlope d n M + 1) := by
  apply min_eq_right
  have hK := slowPolynomialSliceSlope_nonneg d n hM
  have hδ : 1 / (20 * Real.pi) ≤ (1 : ℝ) := by
    apply (div_le_one (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  exact (div_le_one (by linarith)).mpr (by linarith)

theorem slowPolynomialSliceRadius_pos (d n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 < slowPolynomialSliceRadius d n M := by
  rw [slowPolynomialSliceRadius_eq d n hM]
  have := slowPolynomialSliceSlope_nonneg d n hM
  positivity

theorem slowPolynomialSliceSlope_le_exp (d n : ℕ) {M p : ℝ}
    (_hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) (hM : 0 ≤ M)
    (hMexp : M ≤ Real.exp p) :
    slowPolynomialSliceSlope d n M ≤
      Real.exp (((d : ℝ) + 2) * p + 3 * d + 1) := by
  have hd1 : (d : ℝ) + 1 ≤ Real.exp ((d : ℝ) + 1) := by
    linarith [Real.add_one_le_exp ((d : ℝ) + 1)]
  have hn1 : (n : ℝ) + 1 ≤ Real.exp (p + 1) := by
    linarith [Real.add_one_le_exp (p + 1)]
  have hnp : (n : ℝ) ≤ Real.exp p := by
    linarith [Real.add_one_le_exp p]
  have hd : (d : ℝ) ≤ Real.exp (d : ℝ) := by
    linarith [Real.add_one_le_exp (d : ℝ)]
  unfold slowPolynomialSliceSlope
  calc
    _ ≤ Real.exp ((d : ℝ) + 1) * (Real.exp (p + 1)) ^ d *
        Real.exp p * Real.exp p * Real.exp (d : ℝ) := by
      gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1
      ring

theorem slowPolynomialSlice_log_cost (d n : ℕ) {M p q : ℝ}
    (hp : 1 ≤ p) (hn : (n : ℝ) ≤ p) (hM : 0 ≤ M)
    (hMexp : M ≤ Real.exp p) (hq : 0 < q) (hqexp : q ≤ Real.exp p) :
    Real.log (4 * q / slowPolynomialSliceRadius d n M) ≤
      (p + (d + 400 : ℕ)) ^ (d + 400) := by
  let A : ℝ := ((d : ℝ) + 2) * p + 3 * d + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK := slowPolynomialSliceSlope_nonneg d n hM
  have hKexp := slowPolynomialSliceSlope_le_exp d n (by linarith : 0 ≤ p) hn hM hMexp
  have hK1 : slowPolynomialSliceSlope d n M + 1 ≤ Real.exp (A + 1) := by
    simpa only [add_zero] using add_le_exp_add_one hA (le_refl (0 : ℝ))
      hKexp (by simp : (1 : ℝ) ≤ Real.exp 0)
  have hπ : 80 * Real.pi ≤ Real.exp 320 := by
    linarith [Real.pi_lt_four, Real.add_one_le_exp (320 : ℝ)]
  have hradius := slowPolynomialSliceRadius_pos d n hM
  have hratio : 4 * q / slowPolynomialSliceRadius d n M =
      (80 * Real.pi) * q * (slowPolynomialSliceSlope d n M + 1) := by
    rw [slowPolynomialSliceRadius_eq d n hM]
    field_simp
    ring
  have hexp : 4 * q / slowPolynomialSliceRadius d n M ≤
      Real.exp (320 + p + (A + 1)) := by
    rw [hratio]
    calc
      _ ≤ Real.exp 320 * Real.exp p * Real.exp (A + 1) := by
        gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  have hcost : 320 + p + (A + 1) ≤ (p + (d + 400 : ℕ)) ^ (d + 400) := by
    let t : ℝ := p + (d + 400 : ℕ)
    have hdt : (d : ℝ) + 400 ≤ t := by dsimp [t]; push_cast; linarith
    have hpt : p + 3 ≤ t := by dsimp [t]; push_cast; linarith
    have ht : 1 ≤ t := by dsimp [t]; push_cast; linarith
    calc
      _ ≤ ((d : ℝ) + 400) * (p + 3) := by dsimp [A]; nlinarith
      _ ≤ t * t := mul_le_mul hdt hpt (by linarith) (by linarith)
      _ = t ^ 2 := by ring
      _ ≤ t ^ (d + 400) := pow_le_pow_right₀ ht (by omega)
      _ = _ := rfl
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  exact hexp.trans (Real.exp_le_exp.mpr hcost)

theorem exists_slowPolynomialSlice_log_cost (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (n : ℕ) (M p q : ℝ),
      1 ≤ p → (n : ℝ) ≤ p → 0 ≤ M → M ≤ Real.exp p →
      0 < q → q ≤ Real.exp p →
      Real.log (4 * q / slowPolynomialSliceRadius d n M) ≤ (p + C) ^ C := by
  exact ⟨d + 400, by omega, fun n M p q hp hn hM hMexp hq hqexp =>
    slowPolynomialSlice_log_cost d n hp hn hM hMexp hq hqexp⟩

end Erdos3

end

end OAI
