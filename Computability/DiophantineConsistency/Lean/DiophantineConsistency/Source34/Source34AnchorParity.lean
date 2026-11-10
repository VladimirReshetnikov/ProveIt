import DiophantineConsistency.Source34.Source34Parity

/-! # Anchor parity at the source34 ports

`Mixed121AnchorParity` at the source34 tuple; only the chain link is
tuple-specific, so `graph_anchor_parity` is re-declared over
`Source34Parity.graph_simple_parity` and `Source34Occupied`.

The geometry is unchanged: at cell `2195` the surviving bare source is
`2195 − 1100 = 1095`, and at cell `3296` it is `3296 − 2200 = 1096`. Both are
occupied anchors (`Source34Occupied.anchors_occupied`), so
`1 + T_2195 + carry` and `1 + T_3296 + carry` are even. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Source34AnchorParity
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord
open CompactHeterogeneousCarry CompactGenericAlignedMass Source34Rotation Source34Flatten
open Mixed121Rotation (coefficient word cap)
open Mixed121Flatten (selectors copies)
attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_anchor_parity (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    let p := Source34Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    let a := coefficient (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V))
    ∃ N w : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      (121*8801)*N≤R ∧ w=Exp.exp (R-(121*8801)*N) ∧ v 5=q*w ∧
      let T := Mixed121Temporal.temporalWord (8801*N) (R-121*(8801*N)) C
      let X := word 121 (8801*N) C bandOffsets T
      CarryInput 121 (8801*N) (v 1) 1 (cap (ι:=Aligned (Fin 943) (Fin 44)) 121) a X ∧
      dig 121 C 1095=1 ∧ dig 121 C 1096=1 ∧
      (1 + dig 121 T 2195 + carry 121 (8801*N) a X (cyc (8801*N) 2195 1))%2=0 ∧
      (1 + dig 121 T 3296 + carry 121 (8801*N) a X (cyc (8801*N) 3296 1))%2=0 := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,hpar⟩ := Source34Parity.graph_simple_parity v hv hz
  obtain ⟨N',hN',hq',hJ',hocc⟩ := Source34Occupied.graph_selected_occupied v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  obtain ⟨h1095, h1096, _, _⟩ := Source34Occupied.anchors_occupied _ hocc
  let n : V := 8801*N
  have hnge : (8801:V)≤n := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8801)
    simpa only [n,mul_one] using h
  have ht1 : (2195:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have ht2 : (3296:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have hp1 : (2195:V)%8801=2195 := mod_eq_self_of_lt (by norm_num)
  have hp2 : (3296:V)%8801=3296 := mod_eq_self_of_lt (by norm_num)
  have hc1 : cyc n 2195 1100=1095 := by
    rw [cyc_of_le ht1 (lt_trans (by norm_num : (1100:V)<2195) ht1) (by norm_num)]
    exact (eq_tsub_of_add_eq (show (1095:V)+1100=2195 by norm_num)).symm
  have hc2 : cyc n 3296 2200=1096 := by
    rw [cyc_of_le ht2 (lt_trans (by norm_num : (2200:V)<3296) ht2) (by norm_num)]
    exact (eq_tsub_of_add_eq (show (1096:V)+2200=3296 by norm_num)).symm
  have hs1 := (hpar 2195 ht1 (by norm_num) (Or.inl hp1)).2.1 hp1
  have hs2 := (hpar 3296 ht2 (by norm_num) (Or.inr hp2)).2.2 hp2
  rw [hc1,h1095] at hs1
  rw [hc2,h1096] at hs2
  exact ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,h1095,h1096,hs1,hs2⟩
end Source34AnchorParity
#print axioms Source34AnchorParity.graph_anchor_parity
