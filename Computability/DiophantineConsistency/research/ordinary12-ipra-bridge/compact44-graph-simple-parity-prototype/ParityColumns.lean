import DiophantineConsistency.ParityPhaseModel
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ParityColumns
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord CompactPartialBand
open CleanGeometry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem at2195 (N C k : V) (hN : 0<N) (hk : k<8807*N)
    (hC : C<Exp.exp (67*(8807*N)))
    (hzero : ∀ j<8807*N, ¬Bad (j%8807) → dig 67 C j=0)
    (hp : k%8807=2195) :
    RawParityBands.selectorsAt (8807*N) C k 4393=0 ∧
    RawParityBands.selectorsAt (8807*N) C k 5495=0 ∧
    RawColumnBands.bareColumn (8807*N) C k=dig 67 C (cyc (8807*N) k 1100) := by
  have hn : 0<(8807:V)*N := mul_pos (by norm_num) hN
  refine ⟨?_,?_,?_⟩
  · unfold RawParityBands.selectorsAt
    apply Finset.sum_eq_zero
    intro j _
    unfold selectorDigit
    apply UniformPhaseSupport.source_zero N C k (((4393-j.val):ℕ):V) hN hzero
    rw [hp]
    exact (ParityPhaseModel.selectors j.val j.isLt).1
  · unfold RawParityBands.selectorsAt
    apply Finset.sum_eq_zero
    intro j _
    unfold selectorDigit
    apply UniformPhaseSupport.source_zero N C k (((5495-j.val):ℕ):V) hN hzero
    rw [hp]
    exact (ParityPhaseModel.selectors j.val j.isLt).2.1
  · unfold RawColumnBands.bareColumn
    rw [Finset.sum_eq_single ⟨2, by decide⟩]
    · rw [dig_rot 67 (8807*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
      simp [TwoBand.bareOffset]
    · intro j _ hj
      rw [dig_rot 67 (8807*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
      apply UniformPhaseSupport.source_zero N C k (TwoBand.bareOffset j) hN hzero
      rw [hp]
      exact ParityPhaseModel.bare2195 j hj
    · intro hh; exact (hh (Finset.mem_univ _)).elim

theorem at3296 (N C k : V) (hN : 0<N) (hk : k<8807*N)
    (hC : C<Exp.exp (67*(8807*N)))
    (hzero : ∀ j<8807*N, ¬Bad (j%8807) → dig 67 C j=0)
    (hp : k%8807=3296) :
    RawParityBands.selectorsAt (8807*N) C k 4393=0 ∧
    RawParityBands.selectorsAt (8807*N) C k 5495=0 ∧
    RawColumnBands.bareColumn (8807*N) C k=dig 67 C (cyc (8807*N) k 2201) := by
  have hn : 0<(8807:V)*N := mul_pos (by norm_num) hN
  refine ⟨?_,?_,?_⟩
  · unfold RawParityBands.selectorsAt
    apply Finset.sum_eq_zero
    intro j _
    unfold selectorDigit
    apply UniformPhaseSupport.source_zero N C k (((4393-j.val):ℕ):V) hN hzero
    rw [hp]
    exact (ParityPhaseModel.selectors j.val j.isLt).2.2.1
  · unfold RawParityBands.selectorsAt
    apply Finset.sum_eq_zero
    intro j _
    unfold selectorDigit
    apply UniformPhaseSupport.source_zero N C k (((5495-j.val):ℕ):V) hN hzero
    rw [hp]
    exact (ParityPhaseModel.selectors j.val j.isLt).2.2.2
  · unfold RawColumnBands.bareColumn
    rw [Finset.sum_eq_single ⟨3, by decide⟩]
    · rw [dig_rot 67 (8807*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
      simp [TwoBand.bareOffset]
    · intro j _ hj
      rw [dig_rot 67 (8807*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
      apply UniformPhaseSupport.source_zero N C k (TwoBand.bareOffset j) hN hzero
      rw [hp]
      exact ParityPhaseModel.bare3296 j hj
    · intro hh; exact (hh (Finset.mem_univ _)).elim
#print axioms ParityColumns.at2195
#print axioms ParityColumns.at3296
end ParityColumns
