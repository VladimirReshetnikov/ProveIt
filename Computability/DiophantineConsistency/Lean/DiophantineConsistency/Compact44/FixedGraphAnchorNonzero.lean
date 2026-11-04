import DiophantineConsistency.Compact44.FixedGraphAnchorParity
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FixedGraphAnchorNonzero
open DiophantineConsistency CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem not_both_zero (x y : V) (h : (1+x+y)%2=0) : ¬(x=0 ∧ y=0) := by
  rintro ⟨rfl,rfl⟩
  norm_num at h

theorem graph_anchor_nonzero (v : Fin 12 → V)
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
      ¬(dig 67 T 2195=0 ∧ carry 67 (8807*N) a X (cyc (8807*N) 2195 1)=0) ∧
      ¬(dig 67 T 3296=0 ∧ carry 67 (8807*N) a X (cyc (8807*N) 3296 1)=0) := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,h1095,h1,h2⟩ :=
    FixedGraphAnchorParity.graph_anchor_parity v hv hz
  exact ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,not_both_zero _ _ h1,not_both_zero _ _ h2⟩
#print axioms FixedGraphAnchorNonzero.not_both_zero
#print axioms FixedGraphAnchorNonzero.graph_anchor_nonzero
end FixedGraphAnchorNonzero
