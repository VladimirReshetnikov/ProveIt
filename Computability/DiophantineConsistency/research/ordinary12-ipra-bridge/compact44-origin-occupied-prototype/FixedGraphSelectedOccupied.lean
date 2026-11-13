import DiophantineConsistency.FixedGraphSelectedDecoder
import DiophantineConsistency.SelectedOriginOccupied
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FixedGraphSelectedOccupied
open DiophantineConsistency CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten FixedGraphSelectedInputs CompactPartialBand
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def Occupied (C : V) : Prop :=
  ∀ j : Fin 41, 34≤j.val → dig 67 C (position j:V)=1

theorem graph_selected_occupied (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    let a := GenericBandCarryFamily.coefficient (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V))
    ∃ N w t : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      (67*8807)*N≤R ∧ w=Exp.exp (R-(67*8807)*N) ∧ v 5=q*w ∧
      let T := temporalWord (8807*N) (R-67*(8807*N)) C
      let X := GenericBandCarryFamily.word (8807*N) C (bandOffsets position) T
      CarryInput 67 (8807*N) (v 1) 1 (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41))) a X ∧
      dig 67 T t=0 ∧ dig 67 T (cyc (8807*N) t 1)≤Exp.exp 66 ∧
      carry 67 (8807*N) a X (cyc (8807*N) t 1)=0 ∧
      ((t=4393 ∧ Occupied C) ∨ (t=5495 ∧ Occupied C)) := by
  obtain ⟨N,w,t,hN,hq,hJ,hle,hw,hv5,hcarry,hTzero,hTpred,hc,hband⟩ :=
    FixedGraphSelectedDecoder.graph_selected_decoder v hv hz
  obtain ⟨N',w',hN',hq',hJ',hv5',hcongr',h0,hslots,hhigh⟩ :=
    CompactPositionCarry.fixed_position_noCarry (paramKernel rho) v hv hz
  dsimp only at *
  let n : V := 8807*N
  have hnge : (8807:V)≤n := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8807)
    simpa only [n,mul_one] using h
  have ht₁ : (4393:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have ht₂ : (5495:V)<n := lt_of_lt_of_le (by norm_num) hnge
  refine ⟨N,w,t,hN,hq,hJ,hle,hw,hv5,hcarry,hTzero,hTpred,hc,?_⟩
  rcases hband with ⟨ht,hb,hin,hnc,hdecode⟩ | ⟨ht,hb,hin,hnc,hdecode⟩
  · exact Or.inl ⟨ht,SelectedOriginOccupied.selected_origin_occupied n _ 4393 ht₁ (by norm_num) h0 hin hdecode⟩
  · exact Or.inr ⟨ht,SelectedOriginOccupied.selected_origin_occupied n _ 5495 ht₂ (by norm_num) h0 hin hdecode⟩
#print axioms FixedGraphSelectedOccupied.graph_selected_occupied
end FixedGraphSelectedOccupied
