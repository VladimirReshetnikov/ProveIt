import DiophantineConsistency.ForeignPhaseModel
import DiophantineConsistency.RawColumnBands
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ForeignBandsZero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
open CompactPartialBandRotation CompactSymbolicKernel CleanGeometry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem source_zero (N C target offset : V) (hN : 0<N) (ht : target<8807)
    (hzero : ∀ j<8807*N, ¬Bad (j%8807) → dig 67 C j=0)
    (hphase : ¬Bad (cyc 8807 target offset)) :
    dig 67 C (cyc (8807*N) target offset)=0 := by
  have hn : 0<(8807:V)*N := mul_pos (by norm_num) hN
  apply hzero _ (cyc_lt hn _ _)
  rw [CyclicAnyPhase.cyc_period 8807 N target offset (by norm_num) hN,mod_eq_self_of_lt ht]
  exact hphase

theorem foreign_and_bare (N C : V) (hN : 0<N) (hC : C<Exp.exp (67*(8807*N)))
    (hzero : ∀ j<8807*N, ¬Bad (j%8807) → dig 67 C j=0) :
    columnBand position 5495 (8807*N) C 4393=0 ∧
    columnBand position 4393 (8807*N) C 5495=0 ∧
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
    exact source_zero N C 4393 (selectorOffset 5495 j) hN (by norm_num) hzero
      (ForeignPhaseModel.foreign j.val (Or.inl j.isLt)).1
  have hs₂ (j : Fin 943) : dig 67 (rot 67 n C (selectorOffset 4393 j%n)) 5495=0 := by
    rw [dig_rot 67 n C _ _ (mod_lt _ hn) ht₂ hC,cyc_mod n _ _ hn]
    exact source_zero N C 5495 (selectorOffset 4393 j) hN (by norm_num) hzero
      (ForeignPhaseModel.foreign j.val (Or.inl j.isLt)).2
  have hc₁ (j : Fin 41) : dig 67 (rot 67 n C (copyOffset position 5495 j%n)) 4393=0 := by
    rw [dig_rot 67 n C _ _ (mod_lt _ hn) ht₁ hC,cyc_mod n _ _ hn]
    exact source_zero N C 4393 (copyOffset position 5495 j) hN (by norm_num) hzero
      (ForeignPhaseModel.foreign (position j) (ForeignBandGeometry.copy_allowed j)).1
  have hc₂ (j : Fin 41) : dig 67 (rot 67 n C (copyOffset position 4393 j%n)) 5495=0 := by
    rw [dig_rot 67 n C _ _ (mod_lt _ hn) ht₂ hC,cyc_mod n _ _ hn]
    exact source_zero N C 5495 (copyOffset position 4393 j) hN (by norm_num) hzero
      (ForeignPhaseModel.foreign (position j) (ForeignBandGeometry.copy_allowed j)).2
  have hb₁ (j : Fin 5) : dig 67 (rot 67 n C (TwoBand.bareOffset j%n)) 4393=0 := by
    rw [dig_rot 67 n C _ _ (mod_lt _ hn) ht₁ hC,cyc_mod n _ _ hn]
    exact source_zero N C 4393 (TwoBand.bareOffset j) hN (by norm_num) hzero (ForeignPhaseModel.bare j).1
  have hb₂ (j : Fin 5) : dig 67 (rot 67 n C (TwoBand.bareOffset j%n)) 5495=0 := by
    rw [dig_rot 67 n C _ _ (mod_lt _ hn) ht₂ hC,cyc_mod n _ _ hn]
    exact source_zero N C 5495 (TwoBand.bareOffset j) hN (by norm_num) hzero (ForeignPhaseModel.bare j).2
  refine ⟨?_,?_,?_,?_⟩
  · simp only [columnBand,hs₁,hc₁,mul_zero,Finset.sum_const_zero,add_zero]
  · simp only [columnBand,hs₂,hc₂,mul_zero,Finset.sum_const_zero,add_zero]
  · simp only [RawColumnBands.bareColumn,hb₁,Finset.sum_const_zero]
  · simp only [RawColumnBands.bareColumn,hb₂,Finset.sum_const_zero]
#print axioms ForeignBandsZero.source_zero
#print axioms ForeignBandsZero.foreign_and_bare
end ForeignBandsZero
