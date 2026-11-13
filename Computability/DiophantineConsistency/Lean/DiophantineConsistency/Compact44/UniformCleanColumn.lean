import DiophantineConsistency.Compact44.UniformBandDecoder
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace UniformCleanColumn
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten CompactPartialBandRotation CompactSymbolicKernel
open CleanGeometry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem at4393 (N C T F k : V) (hN : 0<N) (hk : k<8807*N)
    (hC : C<Exp.exp (67*(8807*N)))
    (hzero : ∀ j<8807*N, ¬Bad (j%8807) → dig 67 C j=0)
    (hp : k%8807=4393)
    (h : CarryInput 67 (8807*N) F 1 (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41)))
      (GenericBandCarryFamily.coefficient (fun j => (alignedCoeff selectors copies j:V)))
      (GenericBandCarryFamily.word (8807*N) C (bandOffsets position) T))
    (hT : dig 67 T k=0) (hpred : dig 67 T (cyc (8807*N) k 1)=0) :
    dig 67 F k=FixedGraphRawBands.decoderBand position 4393 (8807*N) C k := by
  have hn : 0<(8807:V)*N := mul_pos (by norm_num) hN
  have hexact := (TemporalCarryExact.clean_exact (8807*N) C T F
    (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V))
    (bandOffsets position) h k hk ConcreteCarryRoom.aligned_room hT (by rw [hpred]; simp)).2
  have hflat := RawColumnBands.flatten position (8807*N) C T k
  obtain ⟨hforeign,hbare⟩ := UniformForeignZero.at4393 N C k hN hk hC hzero hp
  rw [hforeign,hbare,hT] at hflat
  simp only [add_zero] at hflat
  have hband := band_column position 4393 (8807*N) C k hn hk hC
  change columnBand position 4393 (8807*N) C k=FixedGraphRawBands.decoderBand position 4393 (8807*N) C k at hband
  exact hexact.trans (hflat.trans hband)

theorem at5495 (N C T F k : V) (hN : 0<N) (hk : k<8807*N)
    (hC : C<Exp.exp (67*(8807*N)))
    (hzero : ∀ j<8807*N, ¬Bad (j%8807) → dig 67 C j=0)
    (hp : k%8807=5495)
    (h : CarryInput 67 (8807*N) F 1 (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41)))
      (GenericBandCarryFamily.coefficient (fun j => (alignedCoeff selectors copies j:V)))
      (GenericBandCarryFamily.word (8807*N) C (bandOffsets position) T))
    (hT : dig 67 T k=0) (hpred : dig 67 T (cyc (8807*N) k 1)=0) :
    dig 67 F k=FixedGraphRawBands.decoderBand position 5495 (8807*N) C k := by
  have hn : 0<(8807:V)*N := mul_pos (by norm_num) hN
  have hexact := (TemporalCarryExact.clean_exact (8807*N) C T F
    (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V))
    (bandOffsets position) h k hk ConcreteCarryRoom.aligned_room hT (by rw [hpred]; simp)).2
  have hflat := RawColumnBands.flatten position (8807*N) C T k
  obtain ⟨hforeign,hbare⟩ := UniformForeignZero.at5495 N C k hN hk hC hzero hp
  rw [hforeign,hbare,hT] at hflat
  simp only [zero_add,add_zero] at hflat
  have hband := band_column position 5495 (8807*N) C k hn hk hC
  change columnBand position 5495 (8807*N) C k=FixedGraphRawBands.decoderBand position 5495 (8807*N) C k at hband
  exact hexact.trans (hflat.trans hband)
#print axioms UniformCleanColumn.at4393
#print axioms UniformCleanColumn.at5495
end UniformCleanColumn
