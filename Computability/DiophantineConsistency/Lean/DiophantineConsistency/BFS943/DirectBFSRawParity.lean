import DiophantineConsistency.BFS943.DirectBFSRawColumn
import DiophantineConsistency.Compact44.RawCarryParity

/-! Direct-BFS selector-independent parity of the raw carry column. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectBFSRawParity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactTwoBandFlatten CompactPartialBand DirectBFSModelMass
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem raw_mod_two (pos : Fin 41→ℕ) (n C T k : V)
    (hn : 0<n) (hk : k<n) (hC : C<Exp.exp (67*n)) :
    raw 67 (GenericBandCarryFamily.coefficient (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V)))
      (GenericBandCarryFamily.word n C (bandOffsets pos) T) k%2 =
      (RawParityBands.selectorsAt n C k 4393+RawParityBands.selectorsAt n C k 5495+
        RawColumnBands.bareColumn n C k+dig 67 T k)%2 := by
  rw [DirectBFSRawColumn.decoder_bands pos n C T k hn hk hC]
  dsimp only [RawParityBands.selectorsAt]
  have he : Exp.exp (10:V)=Exp.exp 9*2 := by
    rw [show (10:V)=9+1 by norm_num,exp_succ]
    ring
  rw [he]
  have heq (a b c d e f g h : V) :
      ((a+(Exp.exp 9*2)*(b+c))+(d+(Exp.exp 9*2)*(e+f))+g+h)%2 =
      (a+d+g+h)%2 := by
    have hr : (a+(Exp.exp 9*2)*(b+c))+(d+(Exp.exp 9*2)*(e+f))+g+h =
        (a+d+g+h)+(Exp.exp 9*(b+c+e+f))*2 := by ring
    rw [hr,mod_add_mul _ _ (by norm_num : (0:V)<2)]
  apply heq

theorem expand (pos : Fin 41→ℕ) (n C T k c : V)
    (hn : 0<n) (hk : k<n) (hC : C<Exp.exp (67*n))
    (hpar : (raw 67 (GenericBandCarryFamily.coefficient (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V)))
      (GenericBandCarryFamily.word n C (bandOffsets pos) T) k+c)%2=0) :
    (RawParityBands.selectorsAt n C k 4393+RawParityBands.selectorsAt n C k 5495+
      RawColumnBands.bareColumn n C k+dig 67 T k+c)%2=0 := by
  have h := raw_mod_two pos n C T k hn hk hC
  rw [mod_add (by norm_num : (0:V)<2),h,←mod_add (by norm_num : (0:V)<2)] at hpar
  exact hpar

#print axioms DirectBFSRawParity.raw_mod_two
#print axioms DirectBFSRawParity.expand
end DirectBFSRawParity
