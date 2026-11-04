import Trace74CarrierBound

/-! UNCHECKED DRAFT. Guard-free carrier divisibility for the same 74 graph zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74CarrierResidue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace74Representatives Trace74CarrierBound
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_carrier_h_divides_HDB (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0) :
    let rr := regs (ports p) (masked p v)
    rr.h ∣ rr.H*rr.D*rr.B := by
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
  refine ⟨rr.D*(rr.H*(ι (v 7)-(rr.V*rr.V)*rr.B)+rr.K)-rr.H*rr.e-rr.D*rr.H*z,?_⟩
  linear_combination hshape - hZ

/-- Reduction of the carrier product modulo h, without coprimality. -/
theorem reduce_carrier_mod_h {R : Type*} [CommRing R] (h w s B : R)
    (hd : h ∣ (4*(h+1)^3*s*(w*(h+1)+1)-1)*(w*s*(h+1)^4)*B) :
    h ∣ (4*s*(w+1)-1)*w*s*B := by
  let q : R := h+1
  let H0 : R := 4*s*(w+1)-1
  let D0 : R := w*s
  let H : R := 4*q^3*s*(w*q+1)-1
  let D : R := w*s*q^4
  let HH : R := 4*s*((q^2+q+1)*(w*q+1)+w)
  let DD : R := w*s*(q^3+q^2+q+1)
  have heq : H*D=H0*D0+h*(HH*D+H0*DD) := by dsimp [H,D,H0,D0,HH,DD,q]; ring
  change h ∣ H*D*B at hd
  obtain ⟨z,hz⟩ := hd
  rw [heq] at hz
  refine ⟨z-(HH*D+H0*DD)*B,?_⟩
  dsimp [H0,D0]
  linear_combination hz

theorem graph_explicit_carrier_residue (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0) :
    (ι ((p 0:V)*v 0):DiffRing V) ∣
      (4*ι (v 6)*(ι (v 5)+1)-1)*ι (v 5)*ι (v 6)*
        ((ι (p 1:V)+ι (v 5))*ι (v 2)-ι (v 1)) := by
  let rr := regs (ports p) (masked p v)
  have hd := graph_carrier_h_divides_HDB p v hb hv hz
  change rr.h ∣ rr.H*rr.D*rr.B at hd
  have hh : rr.h=ι ((p 0:V)*v 0) := by
    dsimp [rr]
    change (regs (ports p) (fun j => ι (v j))).h=ι (b p v)
    simp only [h_def,ports,b,map_mul,map_natCast]
  have hq : (ι (q p v):DiffRing V)=ι ((p 0:V)*v 0)+1 := by
    simp only [q,b,map_add,map_mul,map_one]
  have hD : rr.D=ι (v 5)*ι (v 6)*(ι (q p v):DiffRing V)^4 := by
    dsimp [rr]
    change (regs (ports p) (fun j => ι (v j))).D = _
    simp only [D_def,X_def,Y_def,q_def,h_def,ports,q,b,map_mul,map_add,map_one,map_natCast]
    ring
  have hH : rr.H=4*(ι (q p v):DiffRing V)^3*ι (v 6)*(ι (v 5)*ι (q p v)+1)-1 := by
    dsimp [rr]
    change (regs (ports p) (fun j => ι (v j))).H = _
    simp only [H_def,Am1_def,X_def,Y_def,q_def,h_def,ports,q,b,map_mul,map_add,map_one,map_natCast]
    ring
  have hC : rr.C=ι (v 2) := by
    change ((ports p 0)*ι (v 0)+1)-ι (v 1)-
      (((ports p 0)*ι (v 0)+1)-ι (v 1)-ι (v 2))=ι (v 2)
    ring
  have hB : rr.B=(ι (p 1:V)+ι (v 5))*ι (v 2)-ι (v 1) := by
    rw [B_def,hC]
    change (((p 1:ℕ):DiffRing V)+ι (v 5))*ι (v 2)-ι (v 1) = _
    simp only [map_natCast]
  rw [hh,hH,hD,hB,hq] at hd
  exact reduce_carrier_mod_h _ _ _ _ hd

#print axioms Trace74CarrierResidue.graph_carrier_h_divides_HDB
#print axioms Trace74CarrierResidue.reduce_carrier_mod_h
#print axioms Trace74CarrierResidue.graph_explicit_carrier_residue
end Trace74CarrierResidue
