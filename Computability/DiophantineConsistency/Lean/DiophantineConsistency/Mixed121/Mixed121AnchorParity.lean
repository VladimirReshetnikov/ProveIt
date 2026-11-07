import DiophantineConsistency.Mixed121.Mixed121Parity

/-! # Anchor parity at the 121x8801 ports

This is the 121x8801 counterpart of Compact44's
`FixedGraphAnchorParity.graph_anchor_parity_facts`.

At cell `2195` the surviving source is `2195 − 1100 = 1095`, and at cell `3296`
it is `3296 − 2200 = 1096`. These are the two occupied anchors of
`Mixed121Occupied`, both `1`. So `1 + T_2195 + carry` and `1 + T_3296 + carry`
are even, where `T` is the temporal word and `carry` the incoming carry. In
Compact44 both cells read the single anchor `1095`. Here they read the two
anchors. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Mixed121AnchorParity
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord
open CompactHeterogeneousCarry CompactGenericAlignedMass Mixed121Rotation Mixed121Flatten
attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Mixed121Ports.betaNat Mixed121Ports.lowNat Mixed121Ports.highNat
  Mixed121Kernel.paramKernel Mixed121Kernel.rho
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_anchor_parity (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Mixed121Ports.ports v) :
    let p := Mixed121Ports.ports
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
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,hpar⟩ := Mixed121Parity.graph_simple_parity v hv hz
  obtain ⟨N',hN',hq',hJ',hocc⟩ := Mixed121Occupied.graph_selected_occupied v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  obtain ⟨h1095, h1096, _, _⟩ := Mixed121Occupied.anchors_occupied _ hocc
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
end Mixed121AnchorParity
#print axioms Mixed121AnchorParity.graph_anchor_parity
