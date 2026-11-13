import Trace74CoupledPellStrongSeed

/-! Construct one strong Pell seed and a compatible positive trace coordinate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74CoupledPellSeedTJoin
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticPellPeriodicity ArithmeticPellHalfIndex
open Trace74CoupledPellPositiveShift Trace74CoupledPellStrongSeed
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The same constructed seed supplies the strong norm, the positive
trace coordinate, and the square shape required by the graph. -/
theorem exists_seed_and_T (a c tau j N : V) (hc : 0<c) (htau : 0<tau)
    (hcy : c=ycoord (4*j+1) a) (hN : N%c=(4*j+1)%c) :
    ∃ t i T : V, 0<t ∧ 0<i ∧ 0<T ∧ c∣t ∧
      ycoord t a=(c*c*tau)*i ∧
      let phi := xcoord t a
      let f := xcoord (2*t) a
      let I := delta a*ycoord (2*t) a
      let s := f*(N+c)
      let Q := oddQuotient (2*(j+t*(2*s+1))) (I-2)
      phi*phi=1+delta a*(i*c*c)*(i*c*c)*tau*tau ∧
      f=1+2*(delta a*(i*c*c)*(i*c*c)*tau*tau) ∧
      I*I+delta a=delta a*f*f ∧
      Q+c=f*(c*T+N) := by
  obtain ⟨t,i,ht,hi,hct,hyt,hI,hcI,hfc,hnorm⟩ := exists_strong_seed a c tau hc htau
  let f := xcoord (2*t) a
  let I := delta a*ycoord (2*t) a
  have hphi : xcoord t a*xcoord t a=1+delta a*(i*c*c)*(i*c*c)*tau*tau := by
    have h := norm t a
    rw [hyt] at h
    calc
      xcoord t a*xcoord t a=1+delta a*((c*c*tau)*i)*((c*c*tau)*i) := h
      _=1+delta a*(i*c*c)*(i*c*c)*tau*tau := by ring
  have hf : f=1+2*(delta a*(i*c*c)*(i*c*c)*tau*tau) := by
    dsimp [f]
    rw [double_x,hyt]
    ring
  obtain ⟨T,hT,hTeq⟩ := positive_T_with_shift a t j I c N ht hI hc hnorm hcI hct hcy hN hfc
  exact ⟨t,i,T,ht,hi,hT,hct,hyt,hphi,hf,hnorm,hTeq⟩

#print axioms Trace74CoupledPellSeedTJoin.exists_seed_and_T
end Trace74CoupledPellSeedTJoin
