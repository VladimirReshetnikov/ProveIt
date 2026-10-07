import OAI.Combinatorics.Progressions.Lattices.ResidueSliceNormalizedCell

namespace OAI

section

namespace Erdos3

namespace ResidueBoxSlice

theorem exists_affine_normalized_cell_of_width {ι : Type*} {N : ι → ℕ} {q Q : ℕ}
    (A : ResidueBoxSlice N q)
    (origin : ι → ℝ) (step : ℝ) (hstep : 0 ≤ step)
    (T : ι → ℝ) (hT : ∀ i, 0 < T i) (hQ : 0 < Q)
    (hparent : ∀ i n, n < N i → |origin i + step * n| ≤ T i)
    (hwidth : ∀ i, step * q * A.length i ≤ 2 * T i / Q) :
    ∃ z : ι → Fin (Q + 1), ∀ j : ∀ i, Fin (A.length i), ∀ i,
      |origin i + step * (A.point j i).val - normalizedRealBoxGrid T Q z i| ≤
        T i * (2 / Q) := by
  classical
  by_cases hlen : ∀ i, 0 < A.length i
  · exact A.exists_affine_normalized_cell hlen origin step hstep T hT hQ hparent hwidth
  · push Not at hlen
    obtain ⟨i, hi⟩ := hlen
    refine ⟨fun _ => ⟨0, Nat.succ_pos _⟩, ?_⟩
    intro j
    have hj := (j i).isLt
    omega

end ResidueBoxSlice

theorem normalized_residue_block_cell {ι : Type*} (N : ι → ℕ) (q Q : ℕ)
    (H : ι → ℕ) (hq : 0 < q) (hQ : 0 < Q) (hH : ∀ i, 0 < H i)
    (hwidth : ∀ i, (q : ℝ) * H i ≤ (N i : ℝ) / Q)
    (origin : ι → ℝ) (step : ℝ) (hstep : 0 ≤ step)
    (T : ι → ℝ) (hT : ∀ i, 0 < T i)
    (hparent : ∀ i n, n < N i → |origin i + step * n| ≤ T i)
    (hparentwidth : ∀ i, step * N i ≤ 2 * T i)
    (a : ∀ i, (FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)).Label) :
    ∃ z : ι → Fin (Q + 1),
      ∀ j : ∀ i, Fin ((ResidueBoxSlice.ofBlocks H hq hH a).length i), ∀ i,
      |origin i + step * ((ResidueBoxSlice.ofBlocks H hq hH a).point j i).val -
        normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q) := by
  apply ResidueBoxSlice.exists_affine_normalized_cell_of_width _ origin step hstep T hT hQ hparent
  intro i
  have hlen : ((ResidueBoxSlice.ofBlocks H hq hH a).length i : ℝ) ≤ H i := by
    exact_mod_cast truncatedProgressionLength_le (N i) (progressionBlockStart (a i)) q (H i)
  calc
    _ ≤ step * q * H i := mul_le_mul_of_nonneg_left hlen (by positivity)
    _ = step * ((q : ℝ) * H i) := by ring
    _ ≤ step * ((N i : ℝ) / Q) := mul_le_mul_of_nonneg_left (hwidth i) hstep
    _ = (step * N i) / Q := by ring
    _ ≤ 2 * T i / Q := div_le_div_of_nonneg_right (hparentwidth i) (Nat.cast_nonneg _)

theorem exists_normalized_residue_block_cells {ι : Type*} (N : ι → ℕ) (q Q : ℕ)
    (hq : 0 < q) (hQ : 0 < Q)
    (origin : ι → ℝ) (step : ℝ) (hstep : 0 ≤ step)
    (T : ι → ℝ) (hT : ∀ i, 0 < T i)
    (hparent : ∀ i n, n < N i → |origin i + step * n| ≤ T i)
    (hparentwidth : ∀ i, step * N i ≤ 2 * T i)
    (hlarge : ∀ i, 2 * (q : ℝ) ≤ (1 / (Q : ℝ)) * N i) :
    ∃ (H : ι → ℕ) (hH : ∀ i, 0 < H i),
      (∀ i, q * H i ≤ N i) ∧
      (∀ i, (q : ℝ) * H i ≤ (N i : ℝ) / Q) ∧
      (∀ i, (N i : ℝ) / (2 * q * Q) ≤ H i) ∧
      ∀ a : ∀ i, (FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)).Label,
        ∃ z : ι → Fin (Q + 1),
          ∀ j : ∀ i, Fin ((ResidueBoxSlice.ofBlocks H hq hH a).length i), ∀ i,
          |origin i + step * ((ResidueBoxSlice.ofBlocks H hq hH a).point j i).val -
            normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q) := by
  have hQr : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hρ : (0 : ℝ) < 1 / Q := by positivity
  have hρ1 : (1 : ℝ) / Q ≤ 1 := (div_le_one hQr).mpr (by exact_mod_cast hQ)
  obtain ⟨H, hH, hfit, hwidth, hlower⟩ := exists_box_block_mesh N q hq hρ hρ1 hlarge
  have hwidth' (i) : (q : ℝ) * H i ≤ (N i : ℝ) / Q := by
    calc
      _ ≤ (1 / (Q : ℝ)) * N i := hwidth i
      _ = _ := by ring
  refine ⟨H, hH, hfit, hwidth', ?_, ?_⟩
  · intro i
    have he : (1 / (Q : ℝ)) * N i / (2 * q) = (N i : ℝ) / (2 * q * Q) := by ring
    rw [← he]
    exact hlower i
  · exact normalized_residue_block_cell N q Q H hq hQ hH hwidth'
      origin step hstep T hT hparent hparentwidth

end Erdos3

end

end OAI
