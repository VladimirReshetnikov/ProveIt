import DiophantineConsistency.AdaptiveGap85PellTrichotomy
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85PellTemplateConditional
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveGap85PellTrichotomy
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem second_index_of_template_bounds (Q x k Y eta zeta c : V)
    (hQ : 0<Q) (hkpos : 0<k) (heta : 0<eta) (hzeta : 0<zeta)
    (hn : x*x=1+Q*(Q+1)*k*k) (hk : k=eta+zeta)
    (hc : eta+Y*k=c)
    (hsmall : 2*(Y+1)<c)
    (hlarge : c<Y*(32*Q*Q+32*Q+6)) : k=8*Q+4 := by
  have he : eta<k := by rw [hk]; exact lt_add_of_pos_right eta hzeta
  rcases positive_parameter_trichotomy Q x k hQ hkpos hn with h1 | h2 | h3
  · have he2 : eta<2 := by simpa only [h1] using he
    have hcsmall : c<2*(Y+1) := by
      rw [←hc,h1]
      calc
        eta+Y*2 < 2+Y*2 := by simpa only [add_comm] using _root_.add_lt_add_right he2 (Y*2)
        _ = 2*(Y+1) := by ring
    exact (lt_asymm hcsmall hsmall).elim
  · exact h2
  · have hmul : Y*(32*Q*Q+32*Q+6) ≤ Y*k := Arithmetic.mul_le_mul_left h3
    have hcge : Y*(32*Q*Q+32*Q+6) < c := by
      calc
        Y*(32*Q*Q+32*Q+6) ≤ Y*k := hmul
        _ < eta+Y*k := by simpa only [add_comm] using lt_add_of_pos_right (Y*k) heta
        _ = c := hc
    exact (lt_asymm hcge hlarge).elim
end DiophantineConsistency.AdaptiveGap85PellTemplateConditional
