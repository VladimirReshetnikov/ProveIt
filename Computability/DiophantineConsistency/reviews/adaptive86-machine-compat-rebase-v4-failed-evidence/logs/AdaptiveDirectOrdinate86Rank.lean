import DiophantineConsistency.AdaptiveDirectOrdinate86Indices
import DiophantineConsistency.ArithmeticAdaptiveRankCongruence2011
import DiophantineConsistency.ArithmeticAdaptiveRankWindow2011

/-! Actual 86-zero rank window and signed rank congruence. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86Rank
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveFirstDivisibility2011
open ArithmeticAdaptiveTransport2011 ArithmeticAdaptiveMainOrientation2011
open ArithmeticAdaptiveMainCongruence2011 ArithmeticAdaptiveFactorThree2011
open ArithmeticAdaptiveRankCongruence2011 ArithmeticAdaptiveRankWindow2011
open AdaptiveDirectOrdinate86Literal AdaptiveDirectOrdinate86MainOrientation AdaptiveDirectOrdinate86Transport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem expressionAt_main_congruence86 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt86 (fun j => (p j:ℤ))) v) : MainCongruence p v := by
  exact main_congruence_of_facts p v (expressionAt_transport_positive86 p v hb hv hz)
    (expressionAt_Y_quotient86 p v hb hv hz) (expressionAt_main_oriented86 p v hb hv hz)

private theorem congruence_divides_difference {x y m : V} (hm : 0<m)
    (hyx : y≤x) (h : x%m=y%m) : m∣x-y := by
  apply mod_eq_zero_iff_dvd.mp
  have he : x-y+y=x := tsub_add_cancel_of_le hyx
  have hh : ((x-y)+y)%m=(0+y)%m := by
    rw [he,zero_add]
    exact h
  have hc := mod_cancel hm hh
  simpa only [zero_mod] using hc

private theorem dvd_magnitude_of_mod {m x y : V} (hm : 0<m) (h : x%m=y%m) :
    m∣magnitude (x,y) := by
  rcases le_total y x with hle | hle
  · have he : x=y+(x-y) := by rw [add_comm,tsub_add_cancel_of_le hle]
    have hg : magnitude (x,y)=x-y := magnitude_of_add he
    rw [hg]
    exact congruence_divides_difference hm hle h
  · have he : y=x+(y-x) := by rw [add_comm,tsub_add_cancel_of_le hle]
    have hg : magnitude (x,y)=y-x := by
      have h' := magnitude_of_add he
      change magnitude (swap (x,y))=y-x at h'
      simpa only [magnitude_swap] using h'
    rw [hg]
    exact congruence_divides_difference hm hle h.symm
theorem expressionAt_rank_congruence86 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt86 (fun j => (p j:ℤ))) v) : RankCongruence p v := by
  let q : V := 1+v 0*(p 0:V)
  let E : V := v 6*v 7
  let k : V := v 9+v 10
  let a : V := E+v 7
  let H : V := 3+4*a
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let T : V := E*q+R+1
  have hq : 0<q := lt_trans (by simp : (0:V)<1) (scaled_parameters_positive p v hb hv).1
  have hm5 : 0<q^5 := pow_pos hq _
  have hm4 : 0<q^4 := pow_pos hq _
  obtain ⟨s,main,_,_,hy,he⟩ := expressionAt_main_congruence86 p v hb hv hz
  have hemod : (H*T)%(q^5)=(H*k)%(q^5) := by
    have h := congrArg (fun z : V => z%(q^5)) he
    rw [mod_add_mul' _ _ hm5,mod_add_mul' _ _ hm5] at h
    exact h
  have hdiv : q^5∣H*magnitude (T,k) := by
    have h := dvd_magnitude_of_mod hm5 hemod
    have heq : magnitude (H*T,H*k)=H*magnitude (T,k) := by
      dsimp [magnitude]
      rw [mul_add H (T-k) (k-T),mul_tsub H T k,mul_tsub H k T]
    rwa [heq] at h
  have hcoef : H=3+4*v 7*(v 6+1) := by dsimp [H,a,E]; ring
  rw [hcoef] at hdiv
  have hY : q^3∣v 7 := ⟨s,hy⟩
  have hT : q^4∣magnitude (T,k) := cancel_factor_three q (v 7) (v 6) _ hq hY hdiv
  have hTmod := magnitude_mod (T,k) (q^4) hm4 hT
  have hEq : q^4∣E*q := by
    refine ⟨v 6*s,?_⟩
    dsimp [E]; rw [hy]; ring
  have hTR : T=E*q+(R+1) := by dsimp [T]; ring
  rw [hTR,mod_add_remove_left_of_dvd hEq hm4] at hTmod
  exact dvd_magnitude_of_mod hm4 hTmod

theorem expressionAt_rank_window86 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (expressionAt86 (fun j => (p j:ℤ))) v) :
    RankWindow p v := by
  have hg := (expressionAt_transport_positive86 p v hb hv hz).2
  have hgap : v 1+v 2<1+v 0*(p 0:V) := tsub_pos_iff_lt.mp hg
  exact scalar_rank_window _ _ _ _ _ _ _ hb (hv 0) (hv 1) (hv 2) hl hh (by ring) hgap

end DiophantineConsistency.AdaptiveDirectOrdinate86Rank
