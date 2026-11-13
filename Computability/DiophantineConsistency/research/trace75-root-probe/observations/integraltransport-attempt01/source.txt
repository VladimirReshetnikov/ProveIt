import Trace75Kappa
import Trace75OffsetExact
import Trace75Transport

/-! Integral trace75 transport, with the actual carrier scale D=XY. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75IntegralTransport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace75CarrierBound Trace75Transport Trace75Kpos
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem natural_dvd_of_signed (a b : V) (hd : (ι a : DiffRing V)∣ι b) : a∣b := by
  obtain ⟨t,ht⟩ := hd
  rcases nonneg_or_nonpos t with ⟨s,hs⟩|⟨s,hs⟩
  · refine ⟨s,?_⟩
    apply ι_injective
    rw [map_mul,ht,hs]
  · have hb : b=0 := by
      apply ι_eq_neg_ι
      calc
        (ι b:DiffRing V)=ι a*t := ht
        _= -(ι (a*s)) := by rw [hs,map_mul]; ring
    rw [hb]
    exact dvd_zero a

theorem graph_integral_transport (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V))
    (hh : (p 3:V)<2*(p 0:V)) (hv : ∀j,0<v j)
    (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    ∃ t : V, (regs (ports p) (fun j => ι (v j))).B=ι (b p v*t) := by
  let rr := regs (ports p) (fun j => ι (v j))
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
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
      rw [M_eval p v hb hv]
      exact heq
    · refine ⟨-ι (tau*f*y),?_⟩
      have heq : Z= -mz := eq_neg_of_add_eq_zero_left h
      dsimp [mz] at heq
      rw [M_eval p v hb hv]
      simpa only [mul_neg] using heq
  obtain ⟨kappa,_hkpos,hK⟩ := Trace75Kappa.graph_positive_kappa p v hb31 hl hh hv hz
  change rr.K=rr.H*ι kappa at hK
  have hKpos : 0<rr.K := graph_K_positive p v hb hv hz
  have hHne : rr.H≠0 := by
    intro hH0
    rw [hH0,zero_mul] at hK
    exact (ne_of_gt hKpos) hK
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hy : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hx : 0<X p v := mul_pos (hv 5) hq
  have hDeval : rr.D=ι (X p v*Y p v) := by
    dsimp [rr]
    simp only [D_def,X_def,Y_def,q_def,h_def,ports,X,Y,q,b,map_mul,map_add,map_one,map_natCast]
  have hDne : rr.D≠0 := by
    rw [hDeval]
    exact ne_of_gt (by simpa only [map_zero] using ι_lt_ι.mpr (mul_pos hx hy))
  have hediv := Trace75OffsetExact.graph_offset_full_divisibility p v hb31 hl hh hv hz
  rw [←hDeval] at hediv
  obtain ⟨rho,hrho⟩ := hediv
  have hM : rr.M=rr.h*rr.D*rr.H := by dsimp [rr]; rw [M_def,D_def]
  have hcar : rr.Z=rr.h*rr.D*(rr.H*(ι (v 7)-(rr.V*rr.V)*rr.B)+rr.K)-
      rr.H*(rr.D*rr.B+rr.h*rr.e) := by dsimp [rr]; rw [Z_def,D_def]
  rw [hM] at hZ
  have hprod : (rr.D*rr.H)*(rr.B-rr.h*(ι (v 7)-(rr.V*rr.V)*rr.B+ι kappa-rho-z))=0 := by
    rw [hZ,hK,hrho] at hcar
    linear_combination hcar
  have hzero := (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero hDne hHne)
  have hdiv : rr.h∣rr.B := ⟨ι (v 7)-(rr.V*rr.V)*rr.B+ι kappa-rho-z,sub_eq_zero.mp hzero⟩
  have hB : 0≤rr.B := (graph_transport_and_mask p v hb hv hz).1
  obtain ⟨B0,hB0⟩ := nonneg_iff.mp hB
  have hheval : rr.h=ι (b p v) := by dsimp [rr]; simp only [h_def,ports,b,map_mul,map_natCast]
  rw [hheval,hB0] at hdiv
  obtain ⟨t,ht⟩ := natural_dvd_of_signed (b p v) B0 hdiv
  refine ⟨t,?_⟩
  change rr.B=ι (b p v*t)
  rw [hB0,ht]

#print axioms Trace75IntegralTransport.graph_integral_transport
end Trace75IntegralTransport
