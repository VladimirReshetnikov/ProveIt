import Trace74CoupledExactSigns
import DiophantineConsistency.ArithmeticModularCancellation

/-! Positive trace coordinate from exact auxiliary residues. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74CoupledPositiveT
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticModularCancellation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Given the exact residues and a sufficient size bound, construct the
positive coordinate for a negative rank represented as `−N`. -/
theorem positive_T_of_residues (Q c f N : V) (hf : 0<f) (hc : 0<c)
    (hqf : (Q+c)%f=0) (hqc : Q%c=N%c) (hfc : f%c=(1:V)%c)
    (hlarge : f*(N+c)≤Q+c) :
    ∃ T : V, 0<T ∧ Q+c=f*(c*T+N) := by
  obtain ⟨z,hz⟩ := mod_eq_zero_iff_dvd.mp hqf
  have hzlo : N+c≤z := by
    apply (mul_le_mul_iff_of_pos_left hf).mp
    simpa only [hz] using hlarge
  have hle : N≤z := le_trans (by simp) hzlo
  have hprod : (f*z)%c=z%c := by
    calc
      (f*z)%c=(f%c*(z%c))%c := mod_mul hc
      _=((1:V)%c*(z%c))%c := by rw [hfc]
      _=((1:V)*z)%c := (mod_mul hc).symm
      _=z%c := by simp
  have hzmod : z%c=N%c := by
    have hQ : (Q+c)%c=Q%c := by
      simpa only [mul_one] using mod_add_mul' Q (1:V) hc
    rw [hz,hprod,hqc] at hQ
    exact hQ
  have hsub : N+(z-N)=z := add_tsub_cancel_of_le hle
  have hcancel : ((z-N)+N)%c=(0+N)%c := by
    rw [add_comm,hsub,zero_add]
    exact hzmod
  have hzero : (z-N)%c=0 := by
    have hh := ArithmeticModularCancellation.add_cancel hc hcancel
    simpa using hh
  obtain ⟨T,hT⟩ := mod_eq_zero_iff_dvd.mp hzero
  have hTpos : 0<T := by
    by_contra hn
    have hTzero : T=0 := le_antisymm (le_of_not_gt hn) (by simp)
    rw [hTzero,mul_zero] at hT
    have hzN : z=N := by rw [←hsub,hT,add_zero]
    have hlt : N<N+c := lt_add_of_pos_right _ hc
    rw [hzN] at hzlo
    exact (not_le_of_gt hlt) hzlo
  refine ⟨T,hTpos,?_⟩
  calc
    Q+c=f*z := hz
    _=f*(N+(z-N)) := by rw [hsub]
    _=f*(c*T+N) := by rw [hT]; ring

#print axioms Trace74CoupledPositiveT.positive_T_of_residues
end Trace74CoupledPositiveT
