import Trace74CarrierBound

/-! Trace75 projection divisor retaining its unavoidable X factor. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74Projection
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace74Representatives Trace74CarrierBound
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cancel_base {R : Type*} [CommRing R] (m t x : R)
    (hd : m*t-1∣m*x) : m*t-1∣x := by
  obtain ⟨s,hs⟩ := hd
  refine ⟨s*t-x,?_⟩
  calc
    x=(m*x)*t-(m*t-1)*x := by ring
    _=((m*t-1)*s)*t-(m*t-1)*x := by rw [hs]
    _=(m*t-1)*(s*t-x) := by ring

theorem graph_projection_divisibility (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0) :
    let rr := regs (ports p) (masked p v)
    rr.H∣(rr.h*rr.X)*rr.K := by
  let rr := regs (ports p) (masked p v)
  obtain ⟨tau,f,V0,Z0,y,_ht,_hf,_hV,_hy,_hVsq,hZsq,hZeq,_hbound⟩ := graph_carrier_bound p v hb hv hz
  let Z : DiffRing V := rr.Z
  let mz : DiffRing V := ι (M p v)*ι (tau*f*y)
  have hsq : Z*Z=mz*mz := by
    calc
      Z*Z=ι (Z0*Z0) := hZsq
      _=mz*mz := by rw [hZeq]; dsimp [mz]; simp only [map_mul]; ring
  have hfactor : (Z-mz)*(Z+mz)=0 := by rw [show (Z-mz)*(Z+mz)=Z*Z-mz*mz by ring,hsq]; ring
  obtain ⟨z,hZ⟩ : ∃ z : DiffRing V, rr.Z=rr.M*z := by
    rcases mul_eq_zero.mp hfactor with h|h
    · refine ⟨ι (tau*f*y),?_⟩
      have heq : Z=mz := sub_eq_zero.mp h
      rw [Trace74Representatives.M_eval p v hb hv]
      exact heq
    · refine ⟨-ι (tau*f*y),?_⟩
      have heq : Z= -mz := eq_neg_of_add_eq_zero_left h
      dsimp [mz] at heq
      rw [Trace74Representatives.M_eval p v hb hv]
      simpa only [mul_neg] using heq
  have hM : rr.M=rr.h*rr.D*rr.H := by dsimp [rr]; rw [M_def,D_def]
  have hshape : rr.Z=rr.h*rr.D*(rr.H*(ι (v 7)-(rr.V*rr.V)*rr.B)+rr.K)-
      rr.H*(rr.D*rr.B+rr.h*rr.e) := by dsimp [rr]; rw [Z_def,D_def]; simp [masked,Trace74Mask.oldVal]
  rw [hM] at hZ
  have hdiv : rr.H∣rr.Y*((rr.h*rr.X)*rr.K) := by
    refine ⟨rr.h*rr.D*z-rr.h*rr.D*(ι (v 7)-(rr.V*rr.V)*rr.B)+rr.D*rr.B+rr.h*rr.e,?_⟩
    have hD : rr.D=rr.X*rr.Y := by dsimp [rr]; rw [D_def]
    rw [hD] at hshape hZ ⊢
    linear_combination -hshape+hZ
  let t : DiffRing V := 4*(rr.X+1)
  have hH : rr.H=rr.Y*t-1 := by dsimp [rr,t]; simp only [H_def,Am1_def]; ring
  change rr.H∣(rr.h*rr.X)*rr.K
  rw [hH] at hdiv ⊢
  exact cancel_base rr.Y t ((rr.h*rr.X)*rr.K) hdiv

#print axioms Trace74Projection.graph_projection_divisibility
end Trace74Projection
