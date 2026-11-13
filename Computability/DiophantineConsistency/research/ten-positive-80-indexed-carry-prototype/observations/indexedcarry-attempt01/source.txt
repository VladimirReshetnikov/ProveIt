import Direct80BandTemporal
import DiophantineConsistency.CompactTwoBandCarry
import DiophantineConsistency.SymbolicKBandDraft

/-! Indexed carry input for the 80 graph with the compact symbolic kernel. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Direct80IndexedCarry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency AdaptiveEquationSyntax2011
open CompactFixedBeta CompactSymbolicPorts ArithmeticRepunit ArithmeticWindowDigits
open CompactPartialBandRotation CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten CompactHeterogeneousCarry
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank TenPositive80NaturalTransport
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_indexed_carry (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp1 : p 1=paramKernel rho) (hp2 : p 2=lowNat)
    (hp3 : p 3=betaNat+highNat) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    ∃ N : V, 0<N ∧ v 0=rep (67*8807) N ∧ q p v=Exp.exp ((67*8807)*N) ∧
      (67*8807)*N≤rankNat p v ∧ v 5=Exp.exp (rankNat p v-(67*8807)*N) ∧
      CarryInput 67 (8807*N) (v 1) 1
        (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41)))
        (GenericBandCarryFamily.coefficient (fun x => (alignedCoeff selectors copies x : V)))
        (GenericBandCarryFamily.word (8807*N) (Cnat p v) (bandOffsets position)
          (temporalWord (8807*N) (rankNat p v-67*(8807*N)) (Cnat p v))) := by
  have hK : (p 1:V)=kernelBand position 4393+kernelBand position 5495+TwoBand.bareKernel := by
    rw [hp1]
    exact SymbolicKBandDraft.symbolic_kernel_band_cast (V:=V)
  obtain ⟨N,hN,hJ,hq,hle,hw,hpos,hF,hgraph,hT,hTcap,_hzero,hcap⟩ :=
    Direct80BandTemporal.graph_band_temporal p v position hp0 hp2 hp3 hv hz hK
  let n : V := 8807*N
  let T := temporalWord n (rankNat p v-67*n) (Cnat p v)
  have hn : 0<n := mul_pos (by norm_num) hN
  have hqexp : q p v=Exp.exp (67*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hmod : Exp.exp (67*n)-1=b p v := by rw [←hqexp]; dsimp [q]; rw [add_tsub_cancel_right]
  have hM : 0<Exp.exp (67*n)-1 := by rw [hmod]; exact hpos
  have hF' : v 1<Exp.exp (67*n)-1 := by rw [hmod]; exact hF
  have hC : Cnat p v<Exp.exp (67*n) := by
    dsimp [Cnat]
    exact BandCarryInputs.source_word_bound (q p v) n (v 1) (v 2) hqexp (hv 1)
  refine ⟨N,hN,hJ,hq,hle,hw,?_⟩
  exact CompactTwoBandCarry.carry_input position n (Cnat p v) T (v 1) hn hM hC hcap hT
    (fun k _ => hTcap k) hF' hgraph

#print axioms Direct80IndexedCarry.graph_indexed_carry
end Direct80IndexedCarry
