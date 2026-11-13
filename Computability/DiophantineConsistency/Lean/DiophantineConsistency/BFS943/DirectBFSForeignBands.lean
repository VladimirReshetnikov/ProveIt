import DiophantineConsistency.BFS943.DirectBFSRawColumn
import DiophantineConsistency.Compact44.ForeignBandsZero

/-! Foreign and bare columns vanish at the two direct-BFS origin targets.

Reconstructed in the tree (the research source was never committed): a port of
`ForeignBandsZero.foreign_and_bare` to `DirectBFSRawColumn.columnBand`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectBFSForeignBands
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
open CompactPartialBandRotation CompactSymbolicKernel CleanGeometry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem foreign_and_bare (N C : V) (hN : 0<N) (hC : C<Exp.exp (67*(8807*N)))
    (hzero : ∀ j<8807*N, ¬Bad (j%8807) → dig 67 C j=0) :
    DirectBFSRawColumn.columnBand position 5495 (8807*N) C 4393=0 ∧
    DirectBFSRawColumn.columnBand position 4393 (8807*N) C 5495=0 ∧
    RawColumnBands.bareColumn (8807*N) C 4393=0 ∧
    RawColumnBands.bareColumn (8807*N) C 5495=0 := by
  let n : V := 8807*N
  have hn : 0<n := mul_pos (by norm_num) hN
  have hnge : (8807:V)≤n := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8807)
    simpa only [n,mul_one] using h
  have ht₁ : (4393:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have ht₂ : (5495:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have hs₁ (j : Fin 943) : dig 67 (rot 67 n C (selectorOffset 5495 j%n)) 4393=0 := by
    rw [dig_rot 67 n C _ _ (mod_lt _ hn) ht₁ hC,cyc_mod n _ _ hn]
    exact ForeignBandsZero.source_zero N C 4393 (selectorOffset 5495 j) hN (by norm_num) hzero
      (ForeignPhaseModel.foreign j.val (Or.inl j.isLt)).1
  have hs₂ (j : Fin 943) : dig 67 (rot 67 n C (selectorOffset 4393 j%n)) 5495=0 := by
    rw [dig_rot 67 n C _ _ (mod_lt _ hn) ht₂ hC,cyc_mod n _ _ hn]
    exact ForeignBandsZero.source_zero N C 5495 (selectorOffset 4393 j) hN (by norm_num) hzero
      (ForeignPhaseModel.foreign j.val (Or.inl j.isLt)).2
  have hc₁ (j : Fin 41) : dig 67 (rot 67 n C (copyOffset position 5495 j%n)) 4393=0 := by
    rw [dig_rot 67 n C _ _ (mod_lt _ hn) ht₁ hC,cyc_mod n _ _ hn]
    exact ForeignBandsZero.source_zero N C 4393 (copyOffset position 5495 j) hN (by norm_num) hzero
      (ForeignPhaseModel.foreign (position j) (ForeignBandGeometry.copy_allowed j)).1
  have hc₂ (j : Fin 41) : dig 67 (rot 67 n C (copyOffset position 4393 j%n)) 5495=0 := by
    rw [dig_rot 67 n C _ _ (mod_lt _ hn) ht₂ hC,cyc_mod n _ _ hn]
    exact ForeignBandsZero.source_zero N C 5495 (copyOffset position 4393 j) hN (by norm_num) hzero
      (ForeignPhaseModel.foreign (position j) (ForeignBandGeometry.copy_allowed j)).2
  have hb₁ (j : Fin 5) : dig 67 (rot 67 n C (TwoBand.bareOffset j%n)) 4393=0 := by
    rw [dig_rot 67 n C _ _ (mod_lt _ hn) ht₁ hC,cyc_mod n _ _ hn]
    exact ForeignBandsZero.source_zero N C 4393 (TwoBand.bareOffset j) hN (by norm_num) hzero
      (ForeignPhaseModel.bare j).1
  have hb₂ (j : Fin 5) : dig 67 (rot 67 n C (TwoBand.bareOffset j%n)) 5495=0 := by
    rw [dig_rot 67 n C _ _ (mod_lt _ hn) ht₂ hC,cyc_mod n _ _ hn]
    exact ForeignBandsZero.source_zero N C 5495 (TwoBand.bareOffset j) hN (by norm_num) hzero
      (ForeignPhaseModel.bare j).2
  refine ⟨?_,?_,?_,?_⟩
  · change DirectBFSRawColumn.columnBand position 5495 n C 4393=0
    simp only [DirectBFSRawColumn.columnBand,hs₁,hc₁,mul_zero,Finset.sum_const_zero,add_zero]
  · change DirectBFSRawColumn.columnBand position 4393 n C 5495=0
    simp only [DirectBFSRawColumn.columnBand,hs₂,hc₂,mul_zero,Finset.sum_const_zero,add_zero]
  · change RawColumnBands.bareColumn n C 4393=0
    simp only [RawColumnBands.bareColumn,hb₁,Finset.sum_const_zero]
  · change RawColumnBands.bareColumn n C 5495=0
    simp only [RawColumnBands.bareColumn,hb₂,Finset.sum_const_zero]
#print axioms DirectBFSForeignBands.foreign_and_bare
end DirectBFSForeignBands
