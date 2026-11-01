import DiophantineConsistency.AdaptiveGap85IndexLowerBound
import DiophantineConsistency.AdaptiveGap85FourthMainSyntax
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85FirstIndexThree
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticPellRecurrence ArithmeticPellCongruences
open AdaptiveGap85Literal AdaptiveGap85IndexLowerBound AdaptiveGap85FourthMainSyntax AdaptiveGap85FourthRootCongruence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Actual positive 85 zeros have first index at least three and main index
at least four. This is a necessary condition, not a no-zero theorem. -/
theorem actual_zero_first_index_at_least_three (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀ j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    let Q : V := (v 6*v 7)*v 7
    let k : V := v 9+v 10
    let c : V := v 9+v 7*k
    let a : V := v 6*v 7+v 7
    ∃ first main n m : V, 3≤n ∧ 4≤m ∧ n<m ∧
      xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧
      xcoord m a=main ∧ ycoord m a=c := by
  let X : V := v 6
  let Y : V := v 7
  let Q : V := (v 6*v 7)*v 7
  let k : V := v 9+v 10
  let c : V := v 9+Y*k
  let a : V := X*Y+Y
  let b : V := 2*(Q-1)+1
  obtain ⟨first,main,n,m,hn2,hm4,hnm,hnx,hny,hmx,hmy⟩ := actual_zero_index_lower_bounds p v hb hv hz
  change 2*ycoord n b=k at hny
  change ycoord m a=c at hmy
  have hQpos : 0<Q := mul_pos (mul_pos (hv 6) (hv 7)) (hv 7)
  have hQ1 : Q-1+1=Q := tsub_add_cancel_of_le (pos_iff_one_le.mp hQpos)
  have hb2 : b+2=2*Q+1 := by
    dsimp [b]
    calc
      _ = 2*(Q-1+1)+1 := by ring
      _ = _ := by rw [hQ1]
  have hy2 : ycoord 2 b=2*(b+2) := by
    have hy1 : ycoord 1 b=1 := by simpa using y_succ (0:V) b
    have hx1 : xcoord 1 b=b+2 := by simpa using x_succ (0:V) b
    have hh := y_succ (1:V) b
    rw [hy1,hx1] at hh
    simpa only [one_add_one_eq_two] using hh.trans (by ring)
  have hnne : n≠2 := by
    intro he
    have hk2 : k=8*X*Y*Y+4 := by
      rw [he,hy2,hb2] at hny
      calc
        k = 2*(2*(2*Q+1)) := hny.symm
        _ = _ := by dsimp [Q,X,Y]; ring
    have hmono : fourthC a≤c := by
      rw [←(fourth_coordinates a).1,←hmy]
      exact (y_strictMono a).monotone hm4
    have hket : v 9<k := lt_add_of_pos_right _ (hv 10)
    have hcupper : c<(Y+1)*k := by
      dsimp [c]
      have hh := _root_.add_lt_add_right hket (Y*k)
      calc
        _ < k+Y*k := by simpa only [add_comm] using hh
        _ = _ := by ring
    let gap := 8*Y*Y*Y*(X*X*X+3*X*X+2*X+1)+Y*Y*(48*X*X+88*X+48)+Y*(92*X+88)+52
    have hgap : 0<gap := by dsimp [gap]; simp
    have hcert : (Y+1)*k+gap=fourthC a := by
      rw [hk2]
      dsimp [gap,a,fourthC]
      ring
    have hbig : (Y+1)*k<fourthC a := by
      have hh := lt_add_of_pos_right ((Y+1)*k) hgap
      rwa [hcert] at hh
    exact (lt_asymm (lt_of_lt_of_le hbig hmono) hcupper).elim
  have hn3 : 3≤n := by
    have hh := lt_iff_succ_le.mp (lt_of_le_of_ne hn2 (Ne.symm hnne))
    simpa only [show (2:V)+1=3 by ring] using hh
  exact ⟨first,main,n,m,hn3,hm4,hnm,hnx,hny,hmx,hmy⟩

/-- Quantitative first-index consequence for an actual positive 85-zero. -/
theorem actual_zero_first_index_three_size (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀ j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    let Q : V := (v 6*v 7)*v 7
    32*Q*Q+32*Q+6≤v 9+v 10 := by
  let Q : V := (v 6*v 7)*v 7
  let k : V := v 9+v 10
  let b : V := 2*(Q-1)+1
  obtain ⟨_,_,n,_,hn3,_,_,_,hny,_,_⟩ := actual_zero_first_index_at_least_three p v hb hv hz
  change 2*ycoord n b=k at hny
  have hQpos : 0<Q := mul_pos (mul_pos (hv 6) (hv 7)) (hv 7)
  have hQ1 : Q-1+1=Q := tsub_add_cancel_of_le (pos_iff_one_le.mp hQpos)
  have hb1 : b+1=2*Q := by
    dsimp [b]
    calc
      _ = 2*(Q-1+1) := by ring
      _ = _ := by rw [hQ1]
  have hb3 : b+3=2*Q+2 := by
    calc
      _ = (b+1)+2 := by ring
      _ = _ := by rw [hb1]
  have hd : delta b=4*Q*Q+4*Q := by unfold delta; rw [hb1,hb3]; ring
  have hy3 : ycoord 3 b=16*Q*Q+16*Q+3 := by
    have hh := (AdaptiveGap85ThirdMainSyntax.third_coordinates b).1
    have he : b*b+4*b+3=delta b := by unfold delta; ring
    rw [he,hd] at hh
    calc
      _ = 4*(4*Q*Q+4*Q)+3 := hh
      _ = _ := by ring
  have hmono := (y_strictMono b).monotone hn3
  have hdouble := add_le_add hmono hmono
  change 32*Q*Q+32*Q+6≤k
  calc
    _ = ycoord 3 b+ycoord 3 b := by rw [hy3]; ring
    _ ≤ ycoord n b+ycoord n b := hdouble
    _ = k := by rw [←hny]; ring
end DiophantineConsistency.AdaptiveGap85FirstIndexThree
