import Trace74DynamicRegisters

/-! Bind the strong Pell seed to the actual static chart. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74StrongChartBinding
open Trace74ChartAssembly Trace74DynamicRegisters

/-- The three strong chart outputs follow from a single square identity.
The hypotheses are ring equations; no graph zero or positivity is assumed. -/
theorem strong_outputs {R : Type*} [CommRing R] (delta U tau v phi f I : R)
    (hu : U*tau=v) (hphi : phi*phi=1+delta*v*v)
    (hf : f=2*phi*phi-1) (hI : I=2*delta*phi*v) :
    delta*(U*(tau*tau))*U+1=phi*phi ∧
    (delta*(U*(tau*tau))*U)+(delta*(U*(tau*tau))*U+1)=f ∧
    delta*(4*((delta*(U*(tau*tau))*U)*(delta*(U*(tau*tau))*U+1)))=I*I := by
  have ha : delta*(U*(tau*tau))*U=delta*v*v := by rw [←hu]; ring
  constructor
  · rw [ha]; linear_combination -hphi
  constructor
  · rw [ha,hf]; linear_combination -2*hphi
  · rw [ha,hI]; linear_combination (4*delta*delta*v*v)*(-hphi)

/-- Interpret those identities in the actual 74-register chart. -/
theorem graph_strong_outputs {R : Type*} [CommRing R] (p : Fin 4 → R) (v : Fin 10 → R)
    (delta c tau y phi f I : R)
    (hc : (components p v).c=c)
    (he : (chart p v).E=tau*tau)
    (hd : let q := p 0*v 0+1; let Y := (q*q*q)*v 6; let X := v 5*q;
      let A := X*Y+Y; A*(A+2)=delta)
    (hu : (v 3*(c*c))*tau=y)
    (hphi : phi*phi=1+delta*y*y)
    (hf : f=2*phi*phi-1) (hI : I=2*delta*phi*y) :
    (chart p v).F=phi*phi ∧ (components p v).f=f ∧
      (chart p v).Q=I*I := by
  let q := p 0*v 0+1
  let Y := (q*q*q)*v 6
  let X := v 5*q
  let A := X*Y+Y
  let cc := (v 8+v 9)*Y+v 8
  let U := v 3*(cc*cc)
  let E := ((X*Y)*((v 8+v 9)*Y))*((X*Y)*((v 8+v 9)*Y)+(v 8+v 9))+1
  let a0 := (A*(A+2))*(U*E)*U
  have hFdef : (chart p v).F=a0+1 := rfl
  have hfdef : (components p v).f=a0+(a0+1) := rfl
  have hQdef : (chart p v).Q=(A*(A+2))*(4*(a0*(a0+1))) := rfl
  have he' : E=tau*tau := he
  have hc' : cc=c := hc
  have hU : U*tau=y := by dsimp [U]; rw [hc']; exact hu
  have hresults := strong_outputs delta U tau y phi f I hU hphi hf hI
  obtain ⟨hF,hf',hQ⟩ := hresults
  have ha : a0=delta*(U*(tau*tau))*U := by dsimp [a0]; rw [hd,he']
  refine ⟨?_,?_,?_⟩
  · rw [hFdef,ha]; exact hF
  · rw [hfdef,ha]; exact hf'
  · rw [hQdef,ha,hd]; exact hQ

#print axioms Trace74StrongChartBinding.strong_outputs
#print axioms Trace74StrongChartBinding.graph_strong_outputs
end Trace74StrongChartBinding
