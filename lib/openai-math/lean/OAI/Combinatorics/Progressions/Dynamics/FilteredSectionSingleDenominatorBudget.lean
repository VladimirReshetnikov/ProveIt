import OAI.Combinatorics.Progressions.Linear.RationalTaggedSpanProjection

namespace OAI

section

namespace Erdos3

theorem filtered_section_coefficient_loss_le_exp (n m H a : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    Real.exp ((p + 2) ^ a) +
      (((m : ℝ) + 1) * ((rationalKernelHeight m H : ℝ) + 1)) *
        ((((n : ℝ) + 1) * ((H : ℝ) + 1)) * Real.exp ((p + 2) ^ a) +
          Real.exp ((p + 2) ^ a)) ≤ Real.exp ((p + 2) ^ (a + 12)) := by
  let q := (p + 2) ^ (a + 9)
  let E := Real.exp q
  have hbase : (1 : ℝ) ≤ p + 2 := by linarith
  have hq : 1 ≤ q := one_le_pow₀ hbase
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (by dsimp [q]; positivity)
  have hE0 : 0 ≤ E := Real.exp_nonneg _
  have hpow (b : ℕ) (hb : b ≤ a + 9) : (p + 2) ^ b ≤ q := pow_le_pow_right₀ hbase hb
  have hA : Real.exp ((p + 2) ^ a) ≤ E := Real.exp_le_exp.mpr (hpow a (by omega))
  have hD : ((n : ℝ) + 1) * ((H : ℝ) + 1) ≤ E := by
    calc
      _ ≤ ((n : ℝ) + 1) * (Real.exp ((p + 2) ^ 1) + 1) := by
        gcongr
        exact hH.trans (Real.exp_le_exp.mpr (le_power_budget hp (by decide)))
      _ ≤ Real.exp ((p + 2) ^ 3) := matrix_weighted_factor_le_exp_power n hp hn 1 (by decide)
      _ ≤ E := Real.exp_le_exp.mpr (hpow 3 (by omega))
  have hS : ((m : ℝ) + 1) * ((rationalKernelHeight m H : ℝ) + 1) ≤ E := by
    calc
      _ ≤ ((m : ℝ) + 1) * (Real.exp ((p + 2) ^ 7) + 1) := by
        gcongr
        exact rationalKernelHeight_le_budget m H hp hm hH
      _ ≤ Real.exp ((p + 2) ^ 9) := matrix_weighted_factor_le_exp_power m hp hm 7 (by decide)
      _ ≤ E := Real.exp_le_exp.mpr (hpow 9 (by omega))
  have hE2 : E ≤ E * E := by nlinarith
  have hE3 : E * E ≤ E * E * E := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hE (mul_nonneg hE0 hE0)
  calc
    _ ≤ E + E * (E * E + E) := by gcongr
    _ ≤ 3 * E ^ 3 := by nlinarith
    _ ≤ Real.exp 2 * (Real.exp q) ^ 3 := by
      change 3 * (Real.exp q) ^ 3 ≤ _
      exact mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (2 : ℝ)]) (by positivity)
    _ = Real.exp (2 + 3 * q) := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    _ ≤ Real.exp ((p + 2) ^ (a + 12)) := by
      apply Real.exp_le_exp.mpr
      have hcube : (8 : ℝ) ≤ (p + 2) ^ 3 := by
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (2 : ℝ) ≤ p + 2) 3
        norm_num at h ⊢
        exact h
      calc
        2 + 3 * q ≤ 8 * q := by linarith
        _ ≤ (p + 2) ^ 3 * q := mul_le_mul_of_nonneg_right hcube (by linarith)
        _ = (p + 2) ^ (a + 12) := by
          dsimp [q]
          rw [← pow_add]
          congr 1
          omega

theorem filtered_section_pair_denominator_le_exp {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D : Matrix κ ι ℚ) (S : Matrix ι κ ℚ) (l : ℕ) {H : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p)
    (hD : ∀ i j, RationalHeightLE (D i j) H)
    (hS : ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card κ) H))
    (hl : (l : ℝ) ≤ Real.exp p) :
    ((matrixDenominator S * matrixDenominator D * l : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 11) := by
  have hH7 := hH.trans (Real.exp_le_exp.mpr (le_power_budget hp (by decide : 1 ≤ 7)))
  have hK := rationalKernelHeight_le_budget (Fintype.card κ) H hp hκ hH
  have h := matrix_pair_denominator_le_exp_power D S l hp 7 (by decide) hι hκ
    (fun i j => (Nat.cast_le.mpr (hD i j).2).trans hH7)
    (fun i j => (Nat.cast_le.mpr (hS i j).2).trans hK) hl
  simpa only [Nat.mul_comm (matrixDenominator S) (matrixDenominator D)] using h

end Erdos3

end

section

namespace Erdos3

theorem filtered_section_single_denominator_le_exp {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (D : Matrix κ ι ℚ) (S : Matrix ι κ ℚ) (l : ℕ) {H : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p)
    (hD : ∀ i j, RationalHeightLE (D i j) H)
    (hS : ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card κ) H))
    (hl : (l : ℝ) ≤ Real.exp p) :
    ((matrixDenominator S * l : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 11) := by
  have hqD : 1 ≤ matrixDenominator D := matrixDenominator_pos D
  have hnat := Nat.mul_le_mul_right l (Nat.mul_le_mul_left (matrixDenominator S) hqD)
  simp only [Nat.mul_one] at hnat
  exact (Nat.cast_le.mpr hnat).trans
    (filtered_section_pair_denominator_le_exp D S l hp hι hκ hH hD hS hl)

theorem filtered_section_entry_exp_and_logHeight_le {ι κ : Type*}
    [Fintype ι] [Fintype κ] (S : Matrix ι κ ℚ) {H : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (hS : ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card κ) H)) :
    ∀ i j, |(S i j : ℝ)| ≤ Real.exp ((p + 2) ^ 7) ∧
      rationalLogHeight (S i j) ≤ (p + 2) ^ 7 := by
  have hb := rationalKernelHeight_le_budget (Fintype.card κ) H hp hκ hH
  intro i j
  exact ⟨(hS i j).abs_real_le.trans hb, rationalLogHeight_le_of_height (hS i j) hb⟩

theorem filtered_section_single_denominator_budget {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (D : Matrix κ ι ℚ) (S : Matrix ι κ ℚ) (l : ℕ) {H : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p)
    (hD : ∀ i j, RationalHeightLE (D i j) H)
    (hS : ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card κ) H))
    (hl : (l : ℝ) ≤ Real.exp p) :
    0 < matrixDenominator S ∧
      ((matrixDenominator S * l : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 11) ∧
      ∀ i j, |(S i j : ℝ)| ≤ Real.exp ((p + 2) ^ 7) ∧
        rationalLogHeight (S i j) ≤ (p + 2) ^ 7 :=
  ⟨matrixDenominator_pos S,
    filtered_section_single_denominator_le_exp D S l hp hι hκ hH hD hS hl,
    filtered_section_entry_exp_and_logHeight_le S hp hκ hH hS⟩

end Erdos3

end

end OAI
