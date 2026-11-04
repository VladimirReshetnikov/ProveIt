import Trace74PositiveCarrier

/-! One explicit odd shift makes both trace and carrier coordinates positive. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74CoupledCarrierShift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticPellHalfIndex ModelDifferenceRing
open Trace74AuxQuotientGrowth Trace74CoupledPellTJoin Trace74PositiveCarrier
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_T_and_carrier (a t j I c N M C G P S B tau phi y : V)
    (ht : 0<t) (hI : 2≤I) (hc : 0<c) (hB : 1≤B)
    (hnorm : I*I+delta a=delta a*(xcoord (2*t) a)*(xcoord (2*t) a))
    (hcI : c∣I) (hct : c∣t) (hcy : c=ycoord (4*j+1) a)
    (hN : N%c=(4*j+1)%c) (hfc : xcoord (2*t) a%c=(1:V)%c)
    (hdiv : ι C-ι G=ι M*(ι P-ι S)) :
    let f := xcoord (2*t) a
    let s := f*(N+c)+P+1
    let Q := oddQuotient (2*(j+t*(2*s+1))) (I-2)
    ∃ T v7 : V, 0<T ∧ 0<v7 ∧ Q+c=f*(c*T+N) ∧
      ι M*(ι v7-ι Q*ι Q*ι B)+(ι C-ι G)=ι M*(ι tau*ι phi*ι y) := by
  let f := xcoord (2*t) a
  let s := f*(N+c)+P+1
  let h := j+t*(2*s+1)
  let Q := oddQuotient (2*h) (I-2)
  have ht1 : 1≤t := pos_iff_one_le.mp ht
  have hs2 : s≤2*s+1 := by
    calc
      s≤s+s := le_add_of_nonneg_right (by simp)
      _≤s+s+1 := le_add_of_nonneg_right (by simp)
      _=2*s+1 := by ring
  have hst : s≤t*(2*s+1) := le_trans hs2 (le_mul_of_one_le_left (by simp) ht1)
  have hsh : s≤h := le_trans hst (by dsimp [h]; exact le_add_of_nonneg_left (by simp))
  have hhQ : h≤Q := by
    have hu := index_le_odd_quotient (2*h) (I-2)
    have hh : h≤2*(2*h)+1 := by
      calc
        h≤h+h := le_add_of_nonneg_right (by simp)
        _≤(h+h)+(h+h)+1 := by simp
        _=2*(2*h)+1 := by ring
    exact le_trans hh hu
  have hQ : s≤Q := le_trans hsh hhQ
  have hlarge : f*(N+c)≤Q+c := by
    have hs : f*(N+c)≤s := by
      dsimp [s]
      exact le_trans (le_add_of_nonneg_right (by simp)) (le_add_of_nonneg_right (by simp))
    exact le_trans hs (le_trans hQ (le_add_of_nonneg_right (by simp)))
  obtain ⟨T,hT,hTeq⟩ := positive_T_from_coupled_pell a t j s I c N hI hc hnorm hcI hct hcy hN hfc hlarge
  have hPQ : P<Q := by
    have hs : P<s := by
      dsimp [s]
      exact lt_of_le_of_lt (le_add_of_nonneg_left (by simp)) (lt_add_one _)
    exact lt_of_lt_of_le hs hQ
  have hQ1 : 1≤Q := pos_iff_one_le.mp (lt_of_le_of_lt (by simp) hPQ)
  have hQB : Q≤Q*Q*B :=
    le_trans (le_mul_of_one_le_right (by simp) hQ1) (le_mul_of_one_le_right (by simp) hB)
  have hsize : P<Q*Q*B+S+tau*phi*y :=
    lt_of_lt_of_le hPQ (le_trans hQB
      (le_trans (le_add_of_nonneg_right (by simp)) (le_add_of_nonneg_right (by simp))))
  obtain ⟨v7,hv,hveq⟩ := exists_positive_carrier M C G P S Q B tau phi y hdiv hsize
  exact ⟨T,v7,hT,hv,hTeq,hveq⟩

#print axioms Trace74CoupledCarrierShift.positive_T_and_carrier
end Trace74CoupledCarrierShift
