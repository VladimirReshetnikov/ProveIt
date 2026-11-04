import DiophantineConsistency.Compact44.RawCarryParity
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FixedGraphBandParity
open DiophantineConsistency CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_band_parity (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    let a := GenericBandCarryFamily.coefficient (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V))
    ∃ N w : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      (67*8807)*N≤R ∧ w=Exp.exp (R-(67*8807)*N) ∧ v 5=q*w ∧
      let T := temporalWord (8807*N) (R-67*(8807*N)) C
      let X := GenericBandCarryFamily.word (8807*N) C (bandOffsets position) T
      CarryInput 67 (8807*N) (v 1) 1 (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41))) a X ∧
      (∀ t<8807*N, 0<t → (t%8807=2195 ∨ t%8807=3296) →
        carry 67 (8807*N) a X (cyc (8807*N) t 1)≤1 ∧
        (RawParityBands.selectorsAt (8807*N) C t 4393 + RawParityBands.selectorsAt (8807*N) C t 5495 +
          RawColumnBands.bareColumn (8807*N) C t + dig 67 T t +
          carry 67 (8807*N) a X (cyc (8807*N) t 1))%2=0) := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,hpar⟩ := FixedGraphCarryParity.graph_parity v hv hz
  dsimp only at *
  let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
  let q : V := 1+v 0*(p 0:V)
  let C : V := q-v 1-v 2
  let n : V := 8807*N
  have hn : 0<n := mul_pos (by norm_num) hN
  have hqexp : q=Exp.exp (67*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : C<Exp.exp (67*n) := by
    dsimp [C]
    exact BandCarryInputs.source_word_bound q n (v 1) (v 2) hqexp (hv 1)
  refine ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,?_⟩
  intro t ht ht0 hphase
  obtain ⟨hbound,hraw⟩ := hpar t ht ht0 hphase
  refine ⟨hbound,?_⟩
  exact RawCarryParity.expand position n C _ t _ hn ht hC hraw
#print axioms FixedGraphBandParity.graph_band_parity
end FixedGraphBandParity
