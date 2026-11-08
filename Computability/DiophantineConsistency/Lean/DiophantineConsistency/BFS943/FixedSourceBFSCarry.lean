import DiophantineConsistency.BFS943.FixedSourceSlots
import DiophantineConsistency.BFS943.DirectBFSBandCarry
import DiophantineConsistency.Compact44.ActualTemporalBand

/-! FixedSource copy of `Trace75BFSCarry`: the same proof with the 75 graph zero replaced by `BFS943FixedSource.FixedSource p v`.
Direct-BFS indexed carry from the actual trace75 graph zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FixedSourceBFSCarry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open CompactFixedBeta CompactSymbolicPorts ArithmeticRepunit ArithmeticWindowDigits
open CompactPartialBandRotation CompactBitRotation CompactSymbolicKernel
open CompactGenericAlignedMass CompactTwoBandFlatten CompactHeterogeneousCarry
open Trace75Factors Trace75Rank Trace75NaturalTransport
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
attribute [local irreducible] DirectBFSModelMass.selectors DirectBFSModelMass.copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_indexed_carry (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho) (hp2 : p 2=lowNat)
    (hp3 : p 3=betaNat+highNat) (hv : ∀j,0<v j)
    (hz : BFS943FixedSource.FixedSource p v) :
    ∃ N : V, 0<N ∧ v 0=rep (67*8807) N ∧ q p v=Exp.exp ((67*8807)*N) ∧
      (67*8807)*N≤rankNat p v ∧ v 5=Exp.exp (rankNat p v-(67*8807)*N) ∧
      CarryInput 67 (8807*N) (v 1) 1
        (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41)))
        (GenericBandCarryFamily.coefficient (fun x => (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies x : V)))
        (GenericBandCarryFamily.word (8807*N) (Cnat p v) (bandOffsets position)
          (temporalWord (8807*N) (rankNat p v-67*(8807*N)) (Cnat p v))) := by
  obtain ⟨N,hN,hJ,hq,hle,hw,hpos,hF,hcongr,_hzero,hcap⟩ :=
    FixedSourceSlots.graph_fixed_congruence p v hp0 hp2 hp3 hv hz
  let n : V := 8807*N
  let T := temporalWord n (rankNat p v-67*n) (Cnat p v)
  have hn : 0<n := mul_pos (by norm_num) hN
  have hqexp : q p v=Exp.exp (67*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hmod : Exp.exp (67*n)-1=b p v := by rw [←hqexp]; dsimp [q]; rw [add_tsub_cancel_right]
  have hM : 0<Exp.exp (67*n)-1 := by rw [hmod]; exact hpos
  have hF' : v 1<Exp.exp (67*n)-1 := by rw [hmod]; exact hF
  have hK : (p 1:V)=DirectBFSBandCarry.kernelBand position 4393+
      DirectBFSBandCarry.kernelBand position 5495+TwoBand.bareKernel := by
    rw [hp1]
    exact DirectBFSBandCarry.symbolic_kernel_band_cast
  have hc : (((p 1:V)+v 5)*Cnat p v)%(Exp.exp (67*n)-1)=v 1 := by rw [hmod]; exact hcongr
  have hbands := DirectBFSBandCarry.combined_congr position (p 1:V) n (Cnat p v) (v 5) (v 1) hn hM hK hc
  have hwexp : v 5=Exp.exp (rankNat p v-67*n) := by dsimp [n]; rw [←mul_assoc]; exact hw
  have ht := ActualTemporalBand.graph_temporal_word n (q p v) (v 1) (v 2)
    (Cnat p v) (rankNat p v) (v 5)
    (DirectBFSBandCarry.rotatedBand position 4393 n (Cnat p v)+
      DirectBFSBandCarry.rotatedBand position 5495 n (Cnat p v)+TwoBand.bareRotated n (Cnat p v)) (v 1)
    hn hM hqexp (hv 1) rfl hwexp hbands
  have hC : Cnat p v<Exp.exp (67*n) := by
    dsimp [Cnat]
    exact BandCarryInputs.source_word_bound (q p v) n (v 1) (v 2) hqexp (hv 1)
  refine ⟨N,hN,hJ,hq,hle,hw,?_⟩
  exact DirectBFSBandCarry.carry_input position n (Cnat p v) T (v 1) hn hM hC hcap ht.2.1
    (fun k _ => ht.2.2 k) hF' ht.1

#print axioms FixedSourceBFSCarry.graph_indexed_carry
end FixedSourceBFSCarry
