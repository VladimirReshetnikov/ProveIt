import DiophantineConsistency.ArithmeticAdaptiveFactorThree2011

/-! Exact q^4 signed rank congruence from the actual adaptive zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveRankCongruence2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveMainCongruence2011
open ArithmeticAdaptiveFactorThree2011 ArithmeticAdaptiveFirstDivisibility2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
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

def RankCongruence (p : Fin 4 → ℕ) (v : Fin 13 → V) : Prop :=
  let q : V := 1+v 0*(p 0:V)
  let k : V := v 9+v 10
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  q^4∣magnitude (R+1,k)

theorem expressionAt_rank_congruence (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt (fun j => (p j:ℤ))) v) : RankCongruence p v := by
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
  obtain ⟨s,main,_,_,hy,he⟩ := expressionAt_main_congruence p v hb hv hz
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

private theorem beta_positive_nat : 0<CurrentMasks2011.beta := by
  have hr : 1<CurrentMasks2011.radix := by unfold CurrentMasks2011.radix; norm_num
  have hp : 1<CurrentMasks2011.radix^2011 := one_lt_pow₀ hr (by decide)
  unfold CurrentMasks2011.beta
  omega

theorem current_rank_congruence (v : Fin 13 → V) (hv : ∀j,0<v j)
    (hz : InternalZero expression v) : RankCongruence currentPorts v := by
  have hb : 0<(CurrentMasks2011.beta:V) := by exact_mod_cast beta_positive_nat
  have hp : 0<(currentPorts 0:V) := by simpa only [currentPorts,Matrix.cons_val_zero] using hb
  apply expressionAt_rank_congruence currentPorts v hp hv
  rw [currentPorts_cast]; exact hz

theorem current_natural_rank_congruence (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    RankCongruence currentPorts (fun j => v j+1) :=
  current_rank_congruence _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)
end DiophantineConsistency.ArithmeticAdaptiveRankCongruence2011
