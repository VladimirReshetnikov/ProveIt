import DiophantineConsistency.AdaptiveGap85ActualFourthLargeQ
import DiophantineConsistency.AdaptiveGap85IndexLowerBound
import DiophantineConsistency.AdaptiveGap85FourthX16Bounds
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85NoFourthLargeQ
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticPellRecurrence ArithmeticPellCongruences
open AdaptiveGap85Literal AdaptiveGap85IndexLowerBound AdaptiveGap85FirstDivisibility
open AdaptiveGap85ThirdMainSyntax AdaptiveGap85FourthMainSyntax AdaptiveGap85FourthRootCongruence
open AdaptiveGap85ActualFourthLargeQ AdaptiveGap85FourthX16Bounds
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- For an actual positive 85-zero, a first port large enough to make q≥5
excludes the fourth main Pell ordinate. This does not exclude higher indices. -/
theorem actual_zero_not_fourth_main_of_large_q (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀ j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v)
    (hq : 5≤1+v 0*(p 0:V)) :
    v 9+v 7*(v 9+v 10) ≠ ycoord 4 (v 6*v 7+v 7) := by
  intro h4
  let q : V := 1+v 0*(p 0:V)
  let Y : V := v 7
  let Q : V := (v 6*v 7)*v 7
  let k : V := v 9+v 10
  let c : V := v 9+Y*k
  let a : V := v 6*v 7+v 7
  let b : V := 2*(Q-1)+1
  have hX16 : v 6=16 := actual_fourth_main_X16_of_large_q p v hb hv hz h4 hq
  obtain ⟨s,_,hs⟩ := expressionAt_Y_quotient85 p v hb hv hz
  have hq3 : q*q*q∣Y := by
    refine ⟨s,?_⟩
    change Y=(q*(q*q))*s at hs
    calc
      _ = (q*(q*q))*s := hs
      _ = (q*q*q)*s := by ring
  have hq2 : 2≤q := le_trans (by norm_num : (2:V)≤5) hq
  have h8 : (8:V)≤q*q*q := by
    have h4' : (4:V)≤q*q := by
      have hh := mul_le_mul hq2 hq2 (by simp) (by simp)
      calc
        _ = 2*2 := by ring
        _ ≤ _ := hh
    have hh := mul_le_mul h4' hq2 (by simp) (by simp)
    calc
      _ = 4*2 := by ring
      _ ≤ _ := hh
  have hY8 : 8≤Y := le_trans h8 (Arithmetic.le_of_dvd (hv 7) hq3)
  obtain ⟨first,main,n,m,hn2,hm4,hnm,hnx,hny,hmx,hmy⟩ := actual_zero_index_lower_bounds p v hb hv hz
  change 2*ycoord n b=k at hny
  change ycoord m a=c at hmy
  have hm4eq : m=4 := (y_strictMono a).injective (hmy.trans h4)
  have hnlt4 : n<4 := by rw [←hm4eq]; exact hnm
  have hncases : n=2 ∨ n=3 := by
    by_cases he : n=2
    · exact Or.inl he
    · right
      have hn3 : 3≤n := by
        simpa only [show (2:V)+1=3 by ring] using lt_iff_succ_le.mp (lt_of_le_of_ne hn2 (Ne.symm he))
      have hnle3 : n≤3 := by
        apply (add_le_add_iff_right (1:V)).mp
        simpa only [show (3:V)+1=4 by ring] using lt_iff_succ_le.mp hnlt4
      exact le_antisymm hnle3 hn3
  have hQpos : 0<Q := mul_pos (mul_pos (hv 6) (hv 7)) (hv 7)
  have hQ1 : Q-1+1=Q := tsub_add_cancel_of_le (pos_iff_one_le.mp hQpos)
  have hQ : Q=16*Y*Y := by dsimp [Q,Y]; rw [hX16]
  have hb1 : b+1=2*Q := by
    dsimp [b]
    calc
      _ = 2*(Q-1+1) := by ring
      _ = _ := by rw [hQ1]
  have hb2 : b+2=2*Q+1 := by
    calc
      _ = (b+1)+1 := by ring
      _ = _ := by rw [hb1]
  have hb3 : b+3=2*Q+2 := by
    calc
      _ = (b+1)+2 := by ring
      _ = _ := by rw [hb1]
  have hy2 : ycoord 2 b=2*(b+2) := by
    have hy1 : ycoord 1 b=1 := by simpa using y_succ (0:V) b
    have hx1 : xcoord 1 b=b+2 := by simpa using x_succ (0:V) b
    have hh := y_succ (1:V) b
    rw [hy1,hx1] at hh
    simpa only [one_add_one_eq_two] using hh.trans (by ring)
  have hd : delta b=4*Q*Q+4*Q := by unfold delta; rw [hb1,hb3]; ring
  have hy3 : ycoord 3 b=16*Q*Q+16*Q+3 := by
    have hh := (third_coordinates b).1
    have he : b*b+4*b+3=delta b := by unfold delta; ring
    rw [he,hd] at hh
    calc
      _ = 4*(4*Q*Q+4*Q)+3 := hh
      _ = _ := by ring
  have ha : a=17*Y := by dsimp [a,Y]; rw [hX16]; ring
  have hc : c=fourthC (17*Y) := by
    have hh : c=ycoord 4 a := h4
    rw [(fourth_coordinates a).1,ha] at hh
    exact hh
  rcases hncases with hn2eq | hn3eq
  · have hk2 : k=128*Y*Y+4 := by
      rw [hn2eq,hy2,hb2] at hny
      calc
        k = 2*(2*(2*Q+1)) := hny.symm
        _ = _ := by rw [hQ]; ring
    apply first_index_two_impossible Y (v 9) (v 10) hY8 (hv 10)
    · rw [←hk2]
    · rw [←hk2]
      exact hc
  · have hk3 : k=8192*Y*Y*Y*Y+512*Y*Y+6 := by
      rw [hn3eq,hy3] at hny
      calc
        k = 2*(16*Q*Q+16*Q+3) := hny.symm
        _ = _ := by rw [hQ]; ring
    apply first_index_three_impossible Y (v 9) hY8 (hv 9)
    rw [←hk3]
    exact hc
end DiophantineConsistency.AdaptiveGap85NoFourthLargeQ
