import DirectBFSUniformForeign
import DirectBFSCarryRoom
import DiophantineConsistency.UniformBandInputs
import DiophantineConsistency.TemporalCarryExact

/-! Uniform clean-column and selector decoding for the direct-BFS family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSUniformDecoder
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticBinaryCarry CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactTwoBandFlatten CompactPartialBandRotation CompactPartialBand CompactSymbolicKernel
open DirectBFSModelMass CleanGeometry
attribute [local irreducible] DirectBFSSymbolicKernel.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def copyWord (n C k : V) (T : ℕ) : V := ∑ j : Fin 41,(2:V)^j.val*copyDigit position n C k T j
def decoderBand (n C k : V) (T : ℕ) : V :=
  (∑ j,selectorDigit n C k T j)+Exp.exp 10*
    ((∑ j,(Exp.exp 41-DirectBFSDecoder.tileValue (V:=V) j)*selectorDigit n C k T j)+copyWord n C k T)
def Conclusion (n C k : V) (T : ℕ) : Prop :=
  ((∀ j : Fin 943,selectorDigit n C k T j=0) ∧ copyWord n C k T=0) ∨
  ∃ j : Fin 943,CompactSelectorSum.Selected (selectorDigit n C k T) j ∧ copyWord n C k T=DirectBFSDecoder.tileValue (V:=V) j

theorem decode (n C k : V) (T : ℕ) (hin : UniformBandInputs.Inputs n C k T)
    (hnc : NoCarry (decoderBand n C k T) (Exp.exp 51-2)) : Conclusion n C k T := by
  obtain ⟨hs,_hc,hw⟩ := hin
  exact (DirectBFSDecoder.decode_iff (selectorDigit n C k T) (copyWord n C k T) hs hw).mp hnc

theorem at4393 (N C T F k : V) (hN : 0<N) (hk : k<8807*N)
    (hC : C<Exp.exp (67*(8807*N)))
    (hzero : ∀ j<8807*N,¬Bad (j%8807) → dig 67 C j=0) (hp : k%8807=4393)
    (h : CarryInput 67 (8807*N) F 1 (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41)))
      (GenericBandCarryFamily.coefficient (fun j => (alignedCoeff selectors copies j:V)))
      (GenericBandCarryFamily.word (8807*N) C (bandOffsets position) T))
    (hT : dig 67 T k=0) (hpred : dig 67 T (cyc (8807*N) k 1)=0) :
    dig 67 F k=decoderBand (8807*N) C k 4393 := by
  have hn : 0<(8807:V)*N := mul_pos (by norm_num) hN
  have hexact := (TemporalCarryExact.clean_exact (8807*N) C T F
    (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V))
    (bandOffsets position) h k hk DirectBFSCarryRoom.aligned_room hT (by rw [hpred]; simp)).2
  have hflat := DirectBFSRawColumn.flatten position (8807*N) C T k
  obtain ⟨hforeign,hbare⟩ := DirectBFSUniformForeign.at4393 N C k hN hk hC hzero hp
  rw [hforeign,hbare,hT] at hflat
  simp only [add_zero] at hflat
  have hband := DirectBFSRawColumn.band_column position 4393 (8807*N) C k hn hk hC
  change DirectBFSRawColumn.columnBand position 4393 (8807*N) C k=decoderBand (8807*N) C k 4393 at hband
  exact hexact.trans (hflat.trans hband)

theorem at5495 (N C T F k : V) (hN : 0<N) (hk : k<8807*N)
    (hC : C<Exp.exp (67*(8807*N)))
    (hzero : ∀ j<8807*N,¬Bad (j%8807) → dig 67 C j=0) (hp : k%8807=5495)
    (h : CarryInput 67 (8807*N) F 1 (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41)))
      (GenericBandCarryFamily.coefficient (fun j => (alignedCoeff selectors copies j:V)))
      (GenericBandCarryFamily.word (8807*N) C (bandOffsets position) T))
    (hT : dig 67 T k=0) (hpred : dig 67 T (cyc (8807*N) k 1)=0) :
    dig 67 F k=decoderBand (8807*N) C k 5495 := by
  have hn : 0<(8807:V)*N := mul_pos (by norm_num) hN
  have hexact := (TemporalCarryExact.clean_exact (8807*N) C T F
    (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V))
    (bandOffsets position) h k hk DirectBFSCarryRoom.aligned_room hT (by rw [hpred]; simp)).2
  have hflat := DirectBFSRawColumn.flatten position (8807*N) C T k
  obtain ⟨hforeign,hbare⟩ := DirectBFSUniformForeign.at5495 N C k hN hk hC hzero hp
  rw [hforeign,hbare,hT] at hflat
  simp only [zero_add,add_zero] at hflat
  have hband := DirectBFSRawColumn.band_column position 5495 (8807*N) C k hn hk hC
  change DirectBFSRawColumn.columnBand position 5495 (8807*N) C k=decoderBand (8807*N) C k 5495 at hband
  exact hexact.trans (hflat.trans hband)

#print axioms DirectBFSUniformDecoder.decode
#print axioms DirectBFSUniformDecoder.at4393
#print axioms DirectBFSUniformDecoder.at5495
end DirectBFSUniformDecoder
