import Trace74CarrierBound

/-! UNCHECKED DRAFT. The 74 q³-chart carrier forces signed offset divisible by q⁴ without reverse guard. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74OffsetDiv
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace74Representatives Trace74CarrierBound
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cancel_one_mod_fourth {R : Type*} [CommRing R] (q r e : R)
    (hr : q∣r-1) (he : q^4∣r*e) : q^4∣e := by
  obtain ⟨t,ht⟩ := hr
  obtain ⟨s,hs⟩ := he
  have hr' : r=1+q*t := by linear_combination ht
  refine ⟨s*(1-q*t+(q*t)^2-(q*t)^3)+t^4*e,?_⟩
  calc
    e=(r*e)*(1-q*t+(q*t)^2-(q*t)^3)+q^4*(t^4*e) := by rw [hr']; ring
    _=q^4*(s*(1-q*t+(q*t)^2-(q*t)^3)+t^4*e) := by rw [hs]; ring

theorem graph_offset_divisible (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0) :
    (ι (q p v):DiffRing V)^4 ∣ (regs (ports p) (masked p v)).e := by
  let rr := regs (ports p) (masked p v)
  let qq : DiffRing V := ι (q p v)
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
  have hDdiv : rr.D∣(rr.h*rr.H)*rr.e := by
    refine ⟨rr.h*(rr.H*(ι (v 7)-(rr.V*rr.V)*rr.B)+rr.K)-rr.H*rr.B-rr.h*rr.H*z,?_⟩
    linear_combination hshape - hZ
  have hqdivD : qq^4∣rr.D := by
    refine ⟨ι (v 5*v 6),?_⟩
    change (regs (ports p) (fun j => ι (v j))).D =
      (ι (q p v):DiffRing V)^4 * ι (v 5*v 6)
    simp only [D_def,X_def,Y_def,q_def,h_def,ports,q,b,map_mul,map_add,map_one,map_natCast]
    ring
  have hqe : qq^4∣(rr.h*rr.H)*rr.e := dvd_trans hqdivD hDdiv
  have hrq : qq∣rr.h*rr.H-1 := by
    refine ⟨4*(qq-1)*qq^2*ι (v 6)*(rr.X+1)-1,?_⟩
    change (regs (ports p) (fun j => ι (v j))).h *
      (regs (ports p) (fun j => ι (v j))).H-1 =
      (ι (q p v):DiffRing V) *
        (4*((ι (q p v):DiffRing V)-1)*(ι (q p v):DiffRing V)^2*ι (v 6)*
          ((regs (ports p) (fun j => ι (v j))).X+1)-1)
    simp only [H_def,Am1_def,X_def,Y_def,q_def,h_def,ports,q,b,map_mul,map_add,map_one,map_natCast]
    ring
  exact cancel_one_mod_fourth qq (rr.h*rr.H) rr.e hrq hqe

#print axioms Trace74OffsetDiv.graph_offset_divisible
end Trace74OffsetDiv
