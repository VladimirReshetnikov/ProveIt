import DirectMainWindow
import DiophantineConsistency.ArithmeticAdaptiveIndexComparison2011

/-! Order the Pell indices for a bounded-port direct graph zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectMainComparison
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJDirectMainGraph
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticPellRecurrence
open ArithmeticPellCongruences ArithmeticAdaptiveIndexComparison2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem comparison (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (DirectMainFirst.integerPorts p)).output v) :
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    let X : V := q*v 5
    let Y : V := (q*(q*q))*v 6
    let k : V := v 8+v 9
    let c : V := v 8+Y*k
    let a : V := X*Y+Y
    let Q : V := (X*Y)*Y
    let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
    ∃ first main n m : V, 0<first ∧ 0<main ∧ 13≤n ∧ n<m ∧ 14≤m ∧ 2*R<c ∧ n≤k ∧ m≤c ∧
      xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧
      xcoord m a=main ∧ ycoord m a=c ∧ (2*n)%(q^4)=R+1 ∧ R+1≤2*n ∧ R+1≤k := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let E : V := X*Y
  let Q : V := E*Y
  let B : V := 2*(Q-1)+1
  let k : V := v 8+v 9
  let c : V := v 8+Y*k
  let a : V := E+Y
  let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
  have hq : 1<q := lt_add_of_pos_right _ (mul_pos (hv 0) hb)
  have hqpos : 0<q := lt_trans (by simp : (0:V)<1) hq
  have hX : 0<X := mul_pos hqpos (hv 5)
  have hYpos : 0<Y := mul_pos (mul_pos hqpos (mul_pos hqpos hqpos)) (hv 6)
  have hY : 2≤Y := two_le_of_positive_cube_quotient hq ⟨v 6,hv 6,rfl⟩
  have hE : 0<E := mul_pos hX hYpos
  have hk : 0<k := add_pos (hv 8) (hv 9)
  have hQ1 : Q-1+1=Q := tsub_add_cancel_of_le (pos_iff_one_le.mp (mul_pos hE hYpos))
  have hB : B+2=2*Q+1 := by
    dsimp [B]
    calc
      2*(Q-1)+1+2=2*(Q-1+1)+1 := by ring
      _=2*Q+1 := by rw [hQ1]
  have hab : a≤B := by
    have hEsub : E-1+1=E := tsub_add_cancel_of_le (pos_iff_one_le.mp hE)
    have hYsub : Y-2+2=Y := tsub_add_cancel_of_le hY
    have heq : a+2+(E-1)*(2*(Y-2)+3)+(Y-2)=B+2 := by
      rw [hB]
      calc
        a+2+(E-1)*(2*(Y-2)+3)+(Y-2)=
          (E-1+1)+(Y-2+2)+2+(E-1)*(2*(Y-2)+3)+(Y-2) := by rw [hEsub,hYsub]
        _=2*((E-1+1)*(Y-2+2))+1 := by ring
        _=2*Q+1 := by rw [hEsub,hYsub]
    have heq' : a+2≤B+2 := by rw [←heq]; simp
    exact (add_le_add_iff_right (2:V)).mp heq'
  obtain ⟨first,main,n,m,hfirst,hmain,hn13,hm,hnk,hmc,hnx,hny,hmx,hmy,hnmod,hnlow,hRk⟩ :=
    DirectMainWindow.graph_early p v hb hl hh hv hz
  change 2*ycoord n B=k at hny
  change ycoord m a=c at hmy
  have hkc : k<c := calc
    k≤k*Y := le_mul_of_one_le_right (by simp) (le_trans (by simp : (1:V)≤2) hY)
    _<k*Y+v 8 := lt_add_of_pos_right _ (hv 8)
    _=c := by dsimp [c]; ring
  have hnm : n<m := by
    by_contra hn
    have hm' : m≤n := le_of_not_gt hn
    have hc : c≤k := calc
      c=ycoord m a := hmy.symm
      _≤ycoord n a := (y_strictMono a).monotone hm'
      _≤ycoord n B := (base_mono a B hab n).2
      _≤2*ycoord n B := le_mul_of_one_le_left (by simp) (by simp)
      _=k := hny
    exact (not_le_of_gt hkc) hc
  have hm14 : 14≤m := by
    have h := le_trans (_root_.add_le_add hn13 (le_refl (1:V))) (lt_iff_succ_le.mp hnm)
    simpa only [show (13:V)+1=14 by ring] using h
  have hhalf : 2*R<c := calc
    2*R<2*(R+1) := mul_lt_mul_of_pos_left (lt_add_one R) (by simp)
    _≤2*k := mul_le_mul_of_nonneg_left hRk (by simp)
    _≤k*Y := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hY (Arithmetic.zero_le k)
    _<k*Y+v 8 := lt_add_of_pos_right _ (hv 8)
    _=c := by dsimp [c]; ring
  exact ⟨first,main,n,m,hfirst,hmain,hn13,hnm,hm14,hhalf,hnk,hmc,hnx,hny,hmx,hmy,hnmod,hnlow,hRk⟩

#print axioms DirectMainComparison.comparison
end DirectMainComparison
