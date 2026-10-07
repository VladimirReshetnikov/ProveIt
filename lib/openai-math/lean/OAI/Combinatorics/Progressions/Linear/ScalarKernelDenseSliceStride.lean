import OAI.Combinatorics.Progressions.Estimates.DenseProgressionInnerFamily

namespace OAI

section

namespace Erdos3

theorem scalarKernelCutoff_dense_slice_stride (s : ℕ) (G : Type*) [Fintype G]
    {p η : ℝ} (hη : 0 < η) {S step H : ℕ} (c : ℤ)
    (hcutoff : scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊ η ≤ S)
    (hstep : 0 < step)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (S : ℤ))
    (hdense : Real.exp (-(p + 1)) * S ≤ (H : ℝ)) :
    2 ≤ H ∧ (step : ℝ) ≤ 4 * Real.exp (p + 1) := by
  have hD : 0 < ⌈Real.exp (p + 1)⌉₊ := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hc := ((scalarKernelCutoff_bounds (Fin (s + 1)) G (by norm_num : 0 < (1 : ℕ)) hD hη).2.2.1).trans hcutoff
  have hcR : (⌈Real.exp (p + 1)⌉₊ : ℝ) * ((s : ℝ) + 2) ≤ S := by
    simpa only [Fintype.card_fin, mul_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      add_assoc, one_add_one_eq_two, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ).mpr hc)
  have hS : 2 * Real.exp (p + 1) ≤ S := by
    have hceil := Nat.le_ceil (Real.exp (p + 1))
    have hnonneg : 0 ≤ (⌈Real.exp (p + 1)⌉₊ : ℝ) * (s : ℝ) := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    nlinarith only [hcR, hceil, hnonneg]
  have hSpos : 0 < S := by
    have h := (mul_pos (by norm_num : (0 : ℝ) < 2) (Real.exp_pos (p + 1))).trans_le hS
    exact_mod_cast h
  have hH : 2 ≤ H := by
    have hmul := (mul_le_mul_of_nonneg_left hS (Real.exp_pos (-(p + 1))).le).trans hdense
    have he : Real.exp (-(p + 1)) * (2 * Real.exp (p + 1)) = 2 := by
      rw [mul_left_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    rw [he] at hmul
    exact_mod_cast hmul
  refine ⟨hH, ?_⟩
  have h := progression_slice_step_le_inverse_density c hSpos hstep hH (Real.exp_pos (-(p + 1)))
    hsubset (by simpa only [card_integerProgressionSupport c step H hstep] using hdense)
  simpa only [div_eq_mul_inv, ← Real.exp_neg, neg_neg] using h

end Erdos3

end

end OAI
