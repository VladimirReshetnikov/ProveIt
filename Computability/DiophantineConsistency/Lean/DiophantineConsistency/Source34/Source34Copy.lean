import DiophantineConsistency.Source34.Source34Field
import DiophantineConsistency.Mixed121.Mixed121Copy

/-! # Anchor copies between temporal blocks, at the source34 ports

`Mixed121Copy` at the source34 tuple. The block-index arithmetic
(`Mixed121Copy.index`, `reflected`, `shift`) is generic and used directly. The
two chain links are re-declared over the source34 parity and field layers:

* `graph_parity_copy`: at phase `2195` the anchor `1095` (bare offset `1100`)
  equals the temporal source, and at phase `3296` the anchor `1096` (offset
  `2200`) does. The bare geometry at the anchor phases is the same as for
  121x8801 (`Source34Parity`);
* `graph_block_copy`: block `h`'s anchors `1095`, `1096` equal the cells
  `2195`, `3296` of block `h − s`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Source34Copy
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord
open CompactHeterogeneousCarry CompactGenericAlignedMass Source34Rotation Source34Flatten
open Mixed121Rotation (coefficient word cap)
open Mixed121Flatten (selectors copies)
open Mixed121Copy (index reflected shift)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho

theorem graph_parity_copy (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    let p := Source34Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N s : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      let E := R-121*(8801*N)
      E%121=0 ∧ s<N ∧ (E/121)%(8801*N)=8801*s ∧
      (∀ k<8801*N, k%8801=2195 →
        dig 121 C (cyc (8801*N) k 1100)=dig 121 C (cyc (8801*N) k ((E/121)%(8801*N)))) ∧
      (∀ k<8801*N, k%8801=3296 →
        dig 121 C (cyc (8801*N) k 2200)=dig 121 C (cyc (8801*N) k ((E/121)%(8801*N)))) := by
  obtain ⟨N,w,s,hN,hq,hJ,hle,hw,hv5,hcarry,haligned,hs,hshift⟩ :=
    Source34Shift.graph_cell_shift v hv hz
  obtain ⟨N',w',hN',hq',hJ',hle',hw',hv5',hcarry',hpar⟩ :=
    Source34Parity.graph_simple_parity v hv hz
  obtain ⟨N'',w'',hN'',hq'',hJ'',hle'',hw'',hv5'',hcarry'',h0'',hzero,hbool⟩ :=
    Source34Clean.graph_support_carry v hv hz
  dsimp only at *
  have hNN1 : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  have hNN2 : N''=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq''.symm.trans hq)
  subst N''
  let p := Source34Ports.ports
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let C : V := q-v 1-v 2
  let n : V := 8801*N
  let E : V := R-121*n
  let D : V := (E/121)%n
  have hn : 0<n := mul_pos (by norm_num) hN
  have hqexp : q=Exp.exp (121*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : C<Exp.exp (121*n) := by
    dsimp [C]
    exact Mixed121Temporal.source_word_bound q n (v 1) (v 2) hqexp (hv 1)
  have hD : D%8801=0 := by rw [show D=8801*s from hshift,mod_mul_self_right]
  refine ⟨N,s,hN,hq,hJ,haligned,hs,hshift,?_,?_⟩
  · intro k hk hp
    have hk0 : 0<k := by
      by_contra hh
      have hz0 : k=0 := nonpos_iff_eq_zero.mp (not_lt.mp hh)
      subst k
      norm_num at hp
    have hphase : (cyc n k 1100)%8801=1095 := by
      have h := Mixed121Uniform.source_phase N k 2195 1095 hN (by norm_num) (by norm_num)
        (by simpa using hp)
      simpa only [show (2195-1095:ℕ)=1100 by decide,Nat.cast_ofNat] using h
    have hx : dig 121 C (cyc n k 1100)≤1 := by
      apply hbool _ (cyc_lt hn _ _)
      rw [hphase]
      norm_num
    have hphaseD : (cyc n k D)%8801=2195 := by
      rw [Mixed121Uniform.shift_phase N k D hN hD,hp]
    have hy : dig 121 C (cyc n k D)≤1 := by
      apply hbool _ (cyc_lt hn _ _)
      rw [hphaseD]
      norm_num
    have hc0 := Source34Field.reset N C E (v 1) k 2195 hN hk hC haligned hD (by norm_num)
      (by norm_num) (by norm_num) (by simpa using hp) hbool hcarry
    have hp' := (hpar k hk hk0 (Or.inl hp)).2.1 hp
    rw [hc0,add_zero,Mixed121Shift.aligned_digit C n E k hn hk hC haligned] at hp'
    exact Mixed121Field.eq_of_even _ _ hx hy hp'
  · intro k hk hp
    have hk0 : 0<k := by
      by_contra hh
      have hz0 : k=0 := nonpos_iff_eq_zero.mp (not_lt.mp hh)
      subst k
      norm_num at hp
    have hphase : (cyc n k 2200)%8801=1096 := by
      have h := Mixed121Uniform.source_phase N k 3296 1096 hN (by norm_num) (by norm_num)
        (by simpa using hp)
      simpa only [show (3296-1096:ℕ)=2200 by decide,Nat.cast_ofNat] using h
    have hx : dig 121 C (cyc n k 2200)≤1 := by
      apply hbool _ (cyc_lt hn _ _)
      rw [hphase]
      norm_num
    have hphaseD : (cyc n k D)%8801=3296 := by
      rw [Mixed121Uniform.shift_phase N k D hN hD,hp]
    have hy : dig 121 C (cyc n k D)≤1 := by
      apply hbool _ (cyc_lt hn _ _)
      rw [hphaseD]
      norm_num
    have hc0 := Source34Field.reset N C E (v 1) k 3296 hN hk hC haligned hD (by norm_num)
      (by norm_num) (by norm_num) (by simpa using hp) hbool hcarry
    have hp' := (hpar k hk hk0 (Or.inr hp)).2.2 hp
    rw [hc0,add_zero,Mixed121Shift.aligned_digit C n E k hn hk hC haligned] at hp'
    exact Mixed121Field.eq_of_even _ _ hx hy hp'

theorem graph_block_copy (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    let p := Source34Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N s : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧ s<N ∧
      ∀ h<N,
        dig 121 C (8801*h+1095)=dig 121 C (8801*(cyc N h s)+2195) ∧
        dig 121 C (8801*h+1096)=dig 121 C (8801*(cyc N h s)+3296) := by
  obtain ⟨N,s,hN,hq,hJ,haligned,hs,hshift,hpar1,hpar2⟩ := graph_parity_copy v hv hz
  dsimp only at *
  refine ⟨N,s,hN,hq,hJ,hs,?_⟩
  intro h hh
  have hidx1 := index N h 2195 hh (by norm_num)
  have hidx2 := index N h 3296 hh (by norm_num)
  have href1 : cyc (8801*N) (8801*h+2195) 1100=8801*h+1095 := by
    rw [reflected N h 2195 1100 hh (by norm_num) (by norm_num)]
    congr 1
    exact (eq_tsub_of_add_eq (show (1095:V)+1100=2195 by norm_num)).symm
  have href2 : cyc (8801*N) (8801*h+3296) 2200=8801*h+1096 := by
    rw [reflected N h 3296 2200 hh (by norm_num) (by norm_num)]
    congr 1
    exact (eq_tsub_of_add_eq (show (1096:V)+2200=3296 by norm_num)).symm
  have heq1 := hpar1 (8801*h+2195) hidx1.1 hidx1.2
  have heq2 := hpar2 (8801*h+3296) hidx2.1 hidx2.2
  rw [href1,hshift,shift N h s 2195 hh hs (by norm_num)] at heq1
  rw [href2,hshift,shift N h s 3296 hh hs (by norm_num)] at heq2
  exact ⟨heq1,heq2⟩
end Source34Copy
#print axioms Source34Copy.graph_parity_copy
#print axioms Source34Copy.graph_block_copy
