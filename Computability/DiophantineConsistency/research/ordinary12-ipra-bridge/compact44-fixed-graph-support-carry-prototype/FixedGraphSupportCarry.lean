import DiophantineConsistency.FixedGraphIndexedCarry
import DiophantineConsistency.CompactPositionGraph
import DiophantineConsistency.CleanModelSupport
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FixedGraphSupportCarry
open DiophantineConsistency CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten CleanGeometry
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_support_carry (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      (67*8807)*N≤R ∧ w=Exp.exp (R-(67*8807)*N) ∧ v 5=q*w ∧
      CarryInput 67 (8807*N) (v 1) 1
        (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41)))
        (GenericBandCarryFamily.coefficient (fun x => (alignedCoeff selectors copies x : V)))
        (GenericBandCarryFamily.word (8807*N) C (bandOffsets position)
          (temporalWord (8807*N) (R-67*(8807*N)) C)) ∧
      dig 67 C 0=1 ∧
      (∀ k<8807*N, ¬Bad (k%8807) → dig 67 C k=0) ∧
      (∀ k<8807*N, k%8807≠1063 → dig 67 C k≤1) := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry⟩ := FixedGraphIndexedCarry.graph_carry v hv hz
  obtain ⟨N',w',hN',hq',hJ',hv5',hcongr',h0,hslots,hhigh⟩ :=
    CompactPositionCarry.fixed_position_noCarry (paramKernel rho) v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  refine ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,h0,?_,?_⟩
  · exact CleanModelSupport.zero_outside _ _ hslots
  · apply CleanModelSupport.boolean_away_special _ _ ?_ hslots
    rw [h0]
#print axioms FixedGraphSupportCarry.graph_support_carry
end FixedGraphSupportCarry
