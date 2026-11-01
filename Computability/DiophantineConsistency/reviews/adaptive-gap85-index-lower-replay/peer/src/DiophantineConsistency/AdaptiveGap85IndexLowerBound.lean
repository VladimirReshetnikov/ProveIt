import DiophantineConsistency.AdaptiveGap85NoThirdMain
import DiophantineConsistency.AdaptiveGap85IndexOrder
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85IndexLowerBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticPellRecurrence ArithmeticPellCongruences
open AdaptiveGap85Literal AdaptiveGap85IndexOrder AdaptiveGap85NoThirdMain
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Actual positive 85 zeros have first Pell index at least two and main
Pell index at least four. This does not rule out zeros at larger indices. -/
theorem actual_zero_index_lower_bounds (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀ j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    let Q : V := (v 6*v 7)*v 7
    let k : V := v 9+v 10
    let c : V := v 9+v 7*k
    let a : V := v 6*v 7+v 7
    ∃ first main n m : V, 2≤n ∧ 4≤m ∧ n<m ∧
      xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧
      xcoord m a=main ∧ ycoord m a=c := by
  let Q : V := (v 6*v 7)*v 7
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let a : V := v 6*v 7+v 7
  let b : V := 2*(Q-1)+1
  obtain ⟨first,main,n,m,hnpos,hnm,hnx,hny,hmx,hmy⟩ := expressionAt_index_order85 p v hb hv hz
  change 2*ycoord n b=k at hny
  change ycoord m a=c at hmy
  have hn1 : 1≤n := pos_iff_one_le.mp hnpos
  have hm2 : 2≤m := by
    have h := le_trans (add_le_add hn1 (le_refl (1:V))) (lt_iff_succ_le.mp hnm)
    simpa only [show (1:V)+1=2 by ring] using h
  have hnne : n≠1 := by
    intro he
    have hy1 : ycoord 1 b=1 := by simpa using y_succ (0:V) b
    have hk2 : k=2 := by rw [he,hy1,mul_one] at hny; exact hny.symm
    have hz1 : 1≤v 10 := pos_iff_one_le.mp (hv 10)
    have heta1 : v 9≤1 := by
      apply (add_le_add_iff_right (1:V)).mp
      calc
        _ ≤ v 9+v 10 := add_le_add (le_refl _) hz1
        _ = 2 := hk2
        _ = 1+1 := by ring
    have hcsmall : c≤1+2*v 7 := by
      dsimp [c]
      rw [hk2]
      have h := add_le_add heta1 (le_refl (v 7*2))
      calc
        _ ≤ 1+v 7*2 := h
        _ = _ := by ring
    have hy2 : ycoord 2 a=2*(a+2) := by
      have hy1' : ycoord 1 a=1 := by simpa using y_succ (0:V) a
      have hx1 : xcoord 1 a=a+2 := by simpa using x_succ (0:V) a
      have h := y_succ (1:V) a
      rw [hy1',hx1] at h
      simpa only [one_add_one_eq_two] using h.trans (by ring)
    have ha : v 7≤a := by dsimp [a]; simp
    have hle : 2*v 7≤2*a := Arithmetic.mul_le_mul_left ha
    have hlt : 1+2*v 7<2*(a+2) := by
      have hh := add_lt_add_of_lt_of_le (show (1:V)<4 by norm_num) hle
      calc
        _ < 4+2*a := hh
        _ = _ := by ring
    have hm : ycoord 2 a≤c := by rw [←hmy]; exact (y_strictMono a).monotone hm2
    rw [hy2] at hm
    exact (not_le_of_gt (lt_of_le_of_lt hcsmall hlt)) hm
  have hn2 : 2≤n := by
    have h := lt_iff_succ_le.mp (lt_of_le_of_ne hn1 (Ne.symm hnne))
    simpa only [show (1:V)+1=2 by ring] using h
  have hm3 : 3≤m := by
    have h := le_trans (add_le_add hn2 (le_refl (1:V))) (lt_iff_succ_le.mp hnm)
    simpa only [show (2:V)+1=3 by ring] using h
  have hmne : m≠3 := by
    intro he
    have hh : c=ycoord 3 a := by rw [←hmy,he]
    exact actual_zero_not_third_main p v hb hv hz hh
  have hm4 : 4≤m := by
    have h := lt_iff_succ_le.mp (lt_of_le_of_ne hm3 (Ne.symm hmne))
    simpa only [show (3:V)+1=4 by ring] using h
  exact ⟨first,main,n,m,hn2,hm4,hnm,hnx,hny,hmx,hmy⟩

/-- A quantitative consequence of the actual first-index lower bound. -/
theorem actual_zero_first_index_size (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀ j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    8*((v 6*v 7)*v 7)+4≤v 9+v 10 := by
  let Q : V := (v 6*v 7)*v 7
  let k : V := v 9+v 10
  let b : V := 2*(Q-1)+1
  obtain ⟨_,_,n,_,hn2,_,_,_,hny,_,_⟩ := actual_zero_index_lower_bounds p v hb hv hz
  change 2*ycoord n b=k at hny
  have hQpos : 0<Q := mul_pos (mul_pos (hv 6) (hv 7)) (hv 7)
  have hQ1 : Q-1+1=Q := tsub_add_cancel_of_le (pos_iff_one_le.mp hQpos)
  have hb2 : b+2=2*Q+1 := by
    dsimp [b]
    calc
      _ = 2*(Q-1+1)+1 := by ring
      _ = 2*Q+1 := by rw [hQ1]
  have hy2 : ycoord 2 b=2*(b+2) := by
    have hy1 : ycoord 1 b=1 := by simpa using y_succ (0:V) b
    have hx1 : xcoord 1 b=b+2 := by simpa using x_succ (0:V) b
    have h := y_succ (1:V) b
    rw [hy1,hx1] at h
    simpa only [one_add_one_eq_two] using h.trans (by ring)
  have hmono := (y_strictMono b).monotone hn2
  have hdouble := add_le_add hmono hmono
  change 8*Q+4≤k
  calc
    _ = ycoord 2 b+ycoord 2 b := by rw [hy2,hb2]; ring
    _ ≤ ycoord n b+ycoord n b := hdouble
    _ = k := by rw [←hny]; ring
end DiophantineConsistency.AdaptiveGap85IndexLowerBound
