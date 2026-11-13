import DirectMainOriented
import DirectMainPell

/-! Graph-specific positive Pell indices; alignment is not asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectMainIndices
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJDirectMainGraph
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticPellRecurrence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_indices (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (DirectMainFirst.integerPorts p)).output v) :
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    let X : V := q*v 5
    let Y : V := (q*(q*q))*v 6
    let U : V := Y*(q*q)
    let k : V := v 8+v 9
    let c : V := v 8+Y*k
    let a : V := X*Y+Y
    let H : V := 3+4*a
    let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
    let P : V := U*(X+a*c)+H*(U*v 11+R+1)
    let N : V := H*k
    let Q : V := (X*Y)*Y
    ∃ first main n m : V, 0<first ∧ 0<main ∧ P=N+U*main ∧
      0<n ∧ 0<m ∧ n≤k ∧ m≤c ∧
      xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧
      xcoord m a=main ∧ ycoord m a=c := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let U : V := Y*(q*q)
  let k : V := v 8+v 9
  let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
  have hb0 : 0<b := mul_pos (hv 0) hb
  have hb1 : 1≤b := pos_iff_one_le.mp hb0
  have hq2 : 2≤q := by
    dsimp [q]
    calc
      (2:V) = 1+1 := by norm_num
      _ ≤ 1+b := by simpa only [add_comm] using add_le_add_left hb1 1
  have hq : 0<q := lt_of_lt_of_le (by simp : (0:V)<2) hq2
  have hs : 1≤v 6 := pos_iff_one_le.mp (hv 6)
  have hq2sq : 4≤q*q := by
    have h := mul_le_mul hq2 hq2 (by simp : (0:V)≤2) (by simp : (0:V)≤q)
    norm_num at h ⊢
    exact h
  have hq3 : 8≤q*(q*q) := by
    have h := mul_le_mul hq2 hq2sq (by simp : (0:V)≤4) (by simp : (0:V)≤q)
    norm_num at h ⊢
    exact h
  have hY : 8≤Y := le_trans hq3 (le_mul_of_one_le_right (by simp) hs)
  have hX : 0<X := mul_pos hq (hv 5)
  have hU : 0<U := mul_pos (lt_of_lt_of_le (by simp : (0:V)<8) hY) (mul_pos hq hq)
  have hk : 0<k := add_pos (hv 8) (hv 9)
  obtain ⟨first,hfirstpos,_,hfirst⟩ := DirectMainFirstQuotient.first_root p v hz hb0
  have hmain := DirectMainOriented.direct_norm p v hb hv hz
  obtain ⟨main,n,m,hm,hbalance,hn,hm',hnk,hmc,hnx,hny,hmx,hmy⟩ :=
    DirectMainPell.direct_indices U X Y k (v 8) (v 11) R first hU hX hY hk (hv 8) hfirst hmain
  exact ⟨first,main,n,m,hfirstpos,hm,hbalance,hn,hm',hnk,hmc,hnx,hny,hmx,hmy⟩

#print axioms DirectMainIndices.graph_indices
end DirectMainIndices
