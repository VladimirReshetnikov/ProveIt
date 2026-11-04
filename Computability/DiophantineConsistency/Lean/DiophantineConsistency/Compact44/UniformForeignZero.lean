import DiophantineConsistency.Compact44.FixedGraphUniformReset
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace UniformForeignZero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
open CompactPartialBandRotation CompactSymbolicKernel CleanGeometry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem at4393 (N C k : V) (hN : 0<N) (hk : k<8807*N)
    (hC : C<Exp.exp (67*(8807*N)))
    (hzero : ∀ j<8807*N, ¬Bad (j%8807) → dig 67 C j=0)
    (hp : k%8807=4393) :
    columnBand position 5495 (8807*N) C k=0 ∧ RawColumnBands.bareColumn (8807*N) C k=0 := by
  have hn : 0<(8807:V)*N := mul_pos (by norm_num) hN
  have hs (j : Fin 943) : dig 67 (rot 67 (8807*N) C (selectorOffset 5495 j%(8807*N))) k=0 := by
    rw [dig_rot 67 (8807*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
    apply UniformPhaseSupport.source_zero N C k (selectorOffset 5495 j) hN hzero
    rw [hp]
    exact (ForeignPhaseModel.foreign j.val (Or.inl j.isLt)).1
  have hc (j : Fin 41) : dig 67 (rot 67 (8807*N) C (copyOffset position 5495 j%(8807*N))) k=0 := by
    rw [dig_rot 67 (8807*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
    apply UniformPhaseSupport.source_zero N C k (copyOffset position 5495 j) hN hzero
    rw [hp]
    exact (ForeignPhaseModel.foreign (position j) (ForeignBandGeometry.copy_allowed j)).1
  have hb (j : Fin 5) : dig 67 (rot 67 (8807*N) C (TwoBand.bareOffset j%(8807*N))) k=0 := by
    rw [dig_rot 67 (8807*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
    apply UniformPhaseSupport.source_zero N C k (TwoBand.bareOffset j) hN hzero
    rw [hp]
    exact (ForeignPhaseModel.bare j).1
  constructor
  · simp only [columnBand,hs,hc,mul_zero,Finset.sum_const_zero,add_zero]
  · simp only [RawColumnBands.bareColumn,hb,Finset.sum_const_zero]

theorem at5495 (N C k : V) (hN : 0<N) (hk : k<8807*N)
    (hC : C<Exp.exp (67*(8807*N)))
    (hzero : ∀ j<8807*N, ¬Bad (j%8807) → dig 67 C j=0)
    (hp : k%8807=5495) :
    columnBand position 4393 (8807*N) C k=0 ∧ RawColumnBands.bareColumn (8807*N) C k=0 := by
  have hn : 0<(8807:V)*N := mul_pos (by norm_num) hN
  have hs (j : Fin 943) : dig 67 (rot 67 (8807*N) C (selectorOffset 4393 j%(8807*N))) k=0 := by
    rw [dig_rot 67 (8807*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
    apply UniformPhaseSupport.source_zero N C k (selectorOffset 4393 j) hN hzero
    rw [hp]
    exact (ForeignPhaseModel.foreign j.val (Or.inl j.isLt)).2
  have hc (j : Fin 41) : dig 67 (rot 67 (8807*N) C (copyOffset position 4393 j%(8807*N))) k=0 := by
    rw [dig_rot 67 (8807*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
    apply UniformPhaseSupport.source_zero N C k (copyOffset position 4393 j) hN hzero
    rw [hp]
    exact (ForeignPhaseModel.foreign (position j) (ForeignBandGeometry.copy_allowed j)).2
  have hb (j : Fin 5) : dig 67 (rot 67 (8807*N) C (TwoBand.bareOffset j%(8807*N))) k=0 := by
    rw [dig_rot 67 (8807*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
    apply UniformPhaseSupport.source_zero N C k (TwoBand.bareOffset j) hN hzero
    rw [hp]
    exact (ForeignPhaseModel.bare j).2
  constructor
  · simp only [columnBand,hs,hc,mul_zero,Finset.sum_const_zero,add_zero]
  · simp only [RawColumnBands.bareColumn,hb,Finset.sum_const_zero]
#print axioms UniformForeignZero.at4393
#print axioms UniformForeignZero.at5495
end UniformForeignZero
