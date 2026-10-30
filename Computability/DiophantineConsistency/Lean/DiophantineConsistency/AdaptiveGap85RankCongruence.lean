import DiophantineConsistency.AdaptiveGap85SignedCongruence
import DiophantineConsistency.ArithmeticAdaptiveFactorThree2011

/-! Signed rank congruence with no rank or root orientation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85RankCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveScaledNorms2011
open ArithmeticAdaptiveFactorThree2011 AdaptiveGap85Literal AdaptiveGap85FirstDivisibility
open AdaptiveGap85SignedCongruence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

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

/-- A positive actual 85 zero implies divisibility of the signed rank difference by q⁴. -/
theorem expressionAt_rank_congruence85 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀ j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    let q : V := 1+v 0*(p 0:V)
    let q2 : V := q*q
    let k : V := v 9+v 10
    let neg : V := q*v 1+v 2
    let rp : V := q2*q2+neg+v 0*((p 2:V)+(p 3:V)*q)
    let rn : V := q2+neg*q2
    q^4∣magnitude (rp+1,rn+k) := by
  let q : V := 1+v 0*(p 0:V)
  let q2 : V := q*q
  let E : V := v 6*v 7
  let k : V := v 9+v 10
  let a : V := E+v 7
  let H : V := 3+4*a
  let neg : V := q*v 1+v 2
  let rp : V := q2*q2+neg+v 0*((p 2:V)+(p 3:V)*q)
  let rn : V := q2+neg*q2
  let T : V := E*q+rp+1
  let N : V := k+rn
  have hq : 0<q := by dsimp [q]; simp
  have hm5 : 0<q^5 := pow_pos hq _
  have hm4 : 0<q^4 := pow_pos hq _
  obtain ⟨s,_,hy⟩ := expressionAt_Y_quotient85 p v hb hv hz
  have hemod := expressionAt_signed_congruence85 p v hb hv hz
  change (H*T)%(q^5)=(H*N)%(q^5) at hemod
  have hdiv : q^5∣H*magnitude (T,N) := by
    have h := dvd_magnitude_of_mod hm5 hemod
    have heq : magnitude (H*T,H*N)=H*magnitude (T,N) := by
      dsimp [magnitude]
      rw [mul_add H (T-N) (N-T),mul_tsub H T N,mul_tsub H N T]
    rwa [heq] at h
  have hcoef : H=3+4*v 7*(v 6+1) := by dsimp [H,a,E]; ring
  rw [hcoef] at hdiv
  have hY : q^3∣v 7 := by
    refine ⟨s,?_⟩
    calc
      v 7=(1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V)))*s := hy
      _=q^3*s := by dsimp [q]; ring
  have hT : q^4∣magnitude (T,N) := cancel_factor_three q (v 7) (v 6) _ hq hY hdiv
  have hTmod := magnitude_mod (T,N) (q^4) hm4 hT
  have hEq : q^4∣E*q := by
    refine ⟨v 6*s,?_⟩
    dsimp [E]; rw [hy]; ring
  have hTR : T=E*q+(rp+1) := by dsimp [T]; ring
  rw [hTR,mod_add_remove_left_of_dvd hEq hm4] at hTmod
  change q^4∣magnitude (rp+1,rn+k)
  apply dvd_magnitude_of_mod hm4
  simpa only [N,add_comm] using hTmod
end DiophantineConsistency.AdaptiveGap85RankCongruence
