import DiophantineConsistency.FixedGraphSimpleParity
import DiophantineConsistency.OccupiedNamedSlots
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FixedGraphAnchorParity
open DiophantineConsistency CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_anchor_parity (v : Fin 12 → V)
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
      dig 67 C 1095=1 ∧
      (1 + dig 67 T 2195 + carry 67 (8807*N) a X (cyc (8807*N) 2195 1))%2=0 ∧
      (1 + dig 67 T 3296 + carry 67 (8807*N) a X (cyc (8807*N) 3296 1))%2=0 := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,hpar⟩ := FixedGraphSimpleParity.graph_simple_parity v hv hz
  obtain ⟨N',w',t',hN',hq',hJ',hle',hw',hv5',hcarry',ht0',htpred',hc',hocc⟩ :=
    FixedGraphSelectedOccupied.graph_selected_occupied v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
  let q : V := 1+v 0*(p 0:V)
  let C : V := q-v 1-v 2
  have hocc' : FixedGraphSelectedOccupied.Occupied C := by
    rcases hocc with ⟨_,h⟩ | ⟨_,h⟩ <;> exact h
  have h1095 := (OccupiedNamedSlots.named_slots C hocc').1
  let n : V := 8807*N
  have hnge : (8807:V)≤n := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8807)
    simpa only [n,mul_one] using h
  have ht1 : (2195:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have ht2 : (3296:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have hp1 : (2195:V)%8807=2195 := mod_eq_self_of_lt (by norm_num)
  have hp2 : (3296:V)%8807=3296 := mod_eq_self_of_lt (by norm_num)
  have hc1 : cyc n 2195 1100=1095 := by
    rw [cyc_of_le ht1 (lt_trans (by norm_num : (1100:V)<2195) ht1) (by norm_num)]
    exact (eq_tsub_of_add_eq (show (1095:V)+1100=2195 by norm_num)).symm
  have hc2 : cyc n 3296 2201=1095 := by
    rw [cyc_of_le ht2 (lt_trans (by norm_num : (2201:V)<3296) ht2) (by norm_num)]
    exact (eq_tsub_of_add_eq (show (1095:V)+2201=3296 by norm_num)).symm
  have hs1 := (hpar 2195 ht1 (by norm_num) (Or.inl hp1)).2.1 hp1
  have hs2 := (hpar 3296 ht2 (by norm_num) (Or.inr hp2)).2.2 hp2
  rw [hc1,h1095] at hs1
  rw [hc2,h1095] at hs2
  exact ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,h1095,hs1,hs2⟩
#print axioms FixedGraphAnchorParity.graph_anchor_parity
end FixedGraphAnchorParity
