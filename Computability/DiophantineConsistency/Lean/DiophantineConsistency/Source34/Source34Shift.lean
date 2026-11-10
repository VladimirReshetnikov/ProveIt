import DiophantineConsistency.Source34.Source34AnchorParity
import DiophantineConsistency.Mixed121.Mixed121Shift

/-! # The temporal rotation is a whole number of native periods, at source34

`Mixed121Shift` at the source34 tuple. The finite phase facts
(`Mixed121Shift.nat_choice`, `nat_zero`, `previous_ordinary`,
`choose_two_ordinary`, `model_zero`) depend only on the hull `Bad` and the
dummies `1063, 1064`, and the width-121 temporal lemmas (`conflict`,
`aligned_digit`, `anchor_nonzero`) are generic over the carry family; all are
used directly. Only the two chain links are re-declared at the source34 ports:

* `graph_aligned_shift`: the bit rotation `E = R − 121·8801N` is a multiple of
  `121` (a fractional rotation contradicts the anchor parity at `2195` or
  `3296`);
* `graph_cell_shift`: the cell rotation `E/121` is a multiple of `8801`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Source34Shift
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord
open CompactHeterogeneousCarry CompactGenericAlignedMass Source34Rotation Source34Flatten
open Mixed121Rotation (coefficient word cap)
open Mixed121Flatten (selectors copies aligned_room)
open Mixed121Clean (Bad)
open Mixed121Shift (choose_two_ordinary previous_ordinary model_zero conflict anchor_nonzero)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho

theorem graph_aligned_shift (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    let p := Source34Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    let a := coefficient (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V))
    ∃ N w : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      (121*8801)*N≤R ∧ w=Exp.exp (R-(121*8801)*N) ∧ v 5=q*w ∧
      let E := R-121*(8801*N)
      let T := Mixed121Temporal.temporalWord (8801*N) E C
      let X := word 121 (8801*N) C bandOffsets T
      CarryInput 121 (8801*N) (v 1) 1 (cap (ι:=Aligned (Fin 943) (Fin 44)) 121) a X ∧
      E%121=0 := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,h1095,h1096,hpar1,hpar2⟩ :=
    Source34AnchorParity.graph_anchor_parity v hv hz
  obtain ⟨N',w',hN',hq',hJ',hle',hw',hv5',hcarry',h0',hzero,hbool⟩ :=
    Source34Clean.graph_support_carry v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  let p := Source34Ports.ports
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let C : V := q-v 1-v 2
  let n : V := 8801*N
  let E : V := R-121*n
  have hn : 0<n := mul_pos (by norm_num) hN
  have hnge : (8801:V)≤n := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8801)
    simpa only [n,mul_one] using h
  have ht1 : (2195:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have ht2 : (3296:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have hp1 : cyc n 2195 1=2194 := by
    rw [cyc_of_le ht1 (lt_trans (by norm_num : (1:V)<2195) ht1) (by norm_num)]
    exact (eq_tsub_of_add_eq (show (2194:V)+1=2195 by norm_num)).symm
  have hp2 : cyc n 3296 1=3295 := by
    rw [cyc_of_le ht2 (lt_trans (by norm_num : (1:V)<3296) ht2) (by norm_num)]
    exact (eq_tsub_of_add_eq (show (3295:V)+1=3296 by norm_num)).symm
  have hqexp : q=Exp.exp (121*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : C<Exp.exp (121*n) := by
    dsimp [C]
    exact Mixed121Temporal.source_word_bound q n (v 1) (v 2) hqexp (hv 1)
  refine ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,?_⟩
  by_contra hr
  have hr0 : 0<E%121 := pos_iff_ne_zero.mpr hr
  have hchoose := choose_two_ordinary N ((E/121)%n) hN
  change ((cyc n 2194 ((E/121)%n))%8801≠1063 ∧ (cyc n 2194 ((E/121)%n))%8801≠1064) ∨
    ((cyc n 3295 ((E/121)%n))%8801≠1063 ∧ (cyc n 3295 ((E/121)%n))%8801≠1064) at hchoose
  rw [←hp1,←hp2] at hchoose
  rcases hchoose with hp | hp
  · let j := cyc n (cyc n 2195 1) ((E/121)%n)
    have hb : dig 121 C j≤1 := hbool j (cyc_lt hn _ _) hp.1
    have hp' : (cyc n j 1)%8801≠1063 := previous_ordinary N j hN hp.2
    have hbprev : dig 121 C (cyc n j 1)≤1 := hbool _ (cyc_lt hn _ _) hp'
    exact conflict n C E (v 1)
      (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V))
      bandOffsets hn hC hcarry 2195 ht1 aligned_room hr0 hpar1 hb hbprev
  · let j := cyc n (cyc n 3296 1) ((E/121)%n)
    have hb : dig 121 C j≤1 := hbool j (cyc_lt hn _ _) hp.1
    have hp' : (cyc n j 1)%8801≠1063 := previous_ordinary N j hN hp.2
    have hbprev : dig 121 C (cyc n j 1)≤1 := hbool _ (cyc_lt hn _ _) hp'
    exact conflict n C E (v 1)
      (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V))
      bandOffsets hn hC hcarry 3296 ht2 aligned_room hr0 hpar2 hb hbprev

theorem graph_cell_shift (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    let p := Source34Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    let a := coefficient (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V))
    ∃ N w s : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      (121*8801)*N≤R ∧ w=Exp.exp (R-(121*8801)*N) ∧ v 5=q*w ∧
      let E := R-121*(8801*N)
      let T := Mixed121Temporal.temporalWord (8801*N) E C
      let X := word 121 (8801*N) C bandOffsets T
      CarryInput 121 (8801*N) (v 1) 1 (cap (ι:=Aligned (Fin 943) (Fin 44)) 121) a X ∧
      E%121=0 ∧ s<N ∧ (E/121)%(8801*N)=8801*s := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,haligned⟩ := graph_aligned_shift v hv hz
  obtain ⟨N',w',hN',hq',hJ',hle',hw',hv5',hcarry',h1095,h1096,hpar1,hpar2⟩ :=
    Source34AnchorParity.graph_anchor_parity v hv hz
  obtain ⟨N'',w'',hN'',hq'',hJ'',hle'',hw'',hv5'',hcarry'',h0'',hzero,hbool⟩ :=
    Source34Clean.graph_support_carry v hv hz
  obtain ⟨N''',w''',hN''',hq''',hJ''',hle''',hw''',hv5''',hpos''',hbound''',hband''',hTlt''',
    hTcap''',h0''',hcap⟩ := Source34Temporal.graph_temporal v hv hz
  dsimp only at *
  have hNN1 : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  have hNN2 : N''=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq''.symm.trans hq)
  subst N''
  have hNN3 : N'''=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq'''.symm.trans hq)
  subst N'''
  let p := Source34Ports.ports
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let C : V := q-v 1-v 2
  let n : V := 8801*N
  let E : V := R-121*n
  let D : V := (E/121)%n
  have hn : 0<n := mul_pos (by norm_num) hN
  have hnge : (8801:V)≤n := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8801)
    simpa only [n,mul_one] using h
  have ht1 : (2195:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have ht2 : (3296:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have hqexp : q=Exp.exp (121*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : C<Exp.exp (121*n) := by
    dsimp [C]
    exact Mixed121Temporal.source_word_bound q n (v 1) (v 2) hqexp (hv 1)
  have hnz1 := anchor_nonzero n C E (v 1)
    (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V))
    bandOffsets hn hC hcap hcarry 2195 ht1 aligned_room haligned hpar1
  have hnz2 := anchor_nonzero n C E (v 1)
    (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V))
    bandOffsets hn hC hcap hcarry 3296 ht2 aligned_room haligned hpar2
  have hb1 : Bad ((cyc n 2195 D)%8801) := by
    by_contra hb
    exact hnz1 (hzero _ (cyc_lt hn _ _) hb)
  have hb2 : Bad ((cyc n 3296 D)%8801) := by
    by_contra hb
    exact hnz2 (hzero _ (cyc_lt hn _ _) hb)
  have hp1 := CyclicAnyPhase.cyc_period 8801 N 2195 D (by norm_num) hN
  have hp2 := CyclicAnyPhase.cyc_period 8801 N 3296 D (by norm_num) hN
  rw [mod_eq_self_of_lt (by norm_num : (2195:V)<8801)] at hp1
  rw [mod_eq_self_of_lt (by norm_num : (3296:V)<8801)] at hp2
  rw [hp1] at hb1
  rw [hp2] at hb2
  have hd0 : D%8801=0 := model_zero D hb1 hb2
  have hdlt : D<n := mod_lt _ hn
  have hslt : D/8801<N := by
    apply div_lt_of_lt_mul
    simpa only [n,mul_comm] using hdlt
  have hD : D=8801*(D/8801) := by
    have h := div_add_mod D 8801
    rw [hd0,add_zero] at h
    exact h.symm
  exact ⟨N,w,D/8801,hN,hq,hJ,hle,hw,hv5,hcarry,haligned,hslt,hD⟩
end Source34Shift
#print axioms Source34Shift.graph_aligned_shift
#print axioms Source34Shift.graph_cell_shift
