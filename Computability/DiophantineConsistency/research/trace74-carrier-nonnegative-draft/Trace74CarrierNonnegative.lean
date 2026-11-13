import Trace74CarrierBound
import Trace74OffsetBound
import Trace74Kpos
import CarrierTransport

/-! UNCHECKED DRAFT. A positive 74 zero forces its signed B register nonnegative,
without assuming the strict reverse mask guard or individual F/C bounds. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74CarrierNonnegative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace74Representatives Trace74CarrierBound Trace74OffsetBound Trace74Kpos TenPositiveCarrierTransport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_B_nonnegative (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0) :
    0≤(regs (ports p) (masked p v)).B := by
  let rr := regs (ports p) (masked p v)
  obtain ⟨tau,f,V0,Z0,y,_ht,_hf,_hV,_hy,hVsq,hZsq,hZeq,hbound⟩ := graph_carrier_bound p v hb hv hz
  let Z : DiffRing V := rr.Z
  let mz : DiffRing V := ι (M p v)*ι (tau*f*y)
  have hsq : Z*Z=mz*mz := by
    calc
      Z*Z=ι (Z0*Z0) := hZsq
      _=mz*mz := by rw [hZeq]; dsimp [mz]; simp only [map_mul]; ring
  have hfactor : (Z-mz)*(Z+mz)=0 := by rw [show (Z-mz)*(Z+mz)=Z*Z-mz*mz by ring,hsq]; ring
  have hcarrier : ∃ z : DiffRing V, Z=ι (M p v)*z ∧ z≤ι (tau*f*y) := by
    rcases mul_eq_zero.mp hfactor with h|h
    · exact ⟨ι (tau*f*y),sub_eq_zero.mp h,le_rfl⟩
    · refine ⟨-ι (tau*f*y),?_,neg_le_self (ι_nonneg _)⟩
      have heq : Z= -mz := eq_neg_of_add_eq_zero_left h
      dsimp [mz] at heq
      simpa only [mul_neg] using heq
  obtain ⟨z,hZ,hzle⟩ := hcarrier
  have hboundR : (2:DiffRing V)*ι (tau*f*y)<ι (V0*V0) := by
    have h := ι_lt_ι.mpr hbound
    simpa only [map_mul,map_ofNat] using h
  have hzbound : 2*z<rr.V*rr.V := by
    calc
      2*z≤2*ι (tau*f*y) := mul_le_mul_of_nonneg_left hzle (by norm_num)
      _<ι (V0*V0) := hboundR
      _=rr.V*rr.V := hVsq.symm
  have hZ' : rr.Z=rr.M*z := by
    rw [Trace74Representatives.M_eval p v hb hv]
    exact hZ
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hA : 0<A p v := add_pos (mul_pos hX hY) hY
  have hhr : rr.h=ι (b p v) := by
    dsimp [rr]
    change (regs (ports p) (fun j => ι (v j))).h=ι (b p v)
    simp only [h_def,ports,b,map_mul,map_natCast]
  have hDr : rr.D=ι (X p v*Y p v) := by
    dsimp [rr]
    change (regs (ports p) (fun j => ι (v j))).D=ι (X p v*Y p v)
    simp only [D_def,X_def,Y_def,q_def,h_def,ports,X,Y,q,b,map_mul,map_add,map_one,map_natCast]
  have hAr : rr.Am1=ι (A p v) := by
    dsimp [rr]
    change (regs (ports p) (fun j => ι (v j))).Am1=ι (A p v)
    simp only [Am1_def,X_def,Y_def,q_def,h_def,ports,A,X,Y,q,b,map_mul,map_add,map_one,map_natCast]
  have hh : 0<rr.h := by rw [hhr,←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hb0
  have hm : 0<rr.D := by rw [hDr,←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact mul_pos hX hY
  have hH : 0<rr.H := by
    dsimp [rr]
    rw [H_def,hAr]
    have hA1 : (1:DiffRing V)≤ι (A p v) := by
      rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]
      exact pos_iff_one_le.mp hA
    linarith
  have hn : 0<(ι (v 7):DiffRing V) := by
    rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]
    exact hv 7
  have hK : 0≤rr.K := le_of_lt (graph_K_positive p v hb hv hz)
  have hL : 0≤rr.V*rr.V := mul_self_nonneg rr.V
  have he : 2*rr.e<(rr.V*rr.V)*rr.D := graph_offset_bound p v hb hv
  have hMshape : rr.M=rr.h*rr.D*rr.H := by
    dsimp [rr]
    rw [M_def,D_def]
  have hZ'' : rr.Z=rr.h*rr.D*rr.H*z := by
    simpa only [hMshape] using hZ'
  have hshape : rr.Z=rr.h*rr.D*(rr.H*(ι (v 7)-(rr.V*rr.V)*rr.B)+rr.K)-
      rr.H*(rr.D*rr.B+rr.h*rr.e) := by
    dsimp [rr]
    rw [Z_def,D_def]
    simp [masked,Trace74Mask.oldVal]
  have hB : 0≤rr.B := model_nonnegative_of_carrier rr.h rr.H rr.D (rr.V*rr.V) rr.B rr.K rr.e z
    (ι (v 7)) rr.Z hh hH hm hL hK hn hzbound he hZ'' hshape
  exact hB

theorem graph_F_carrier_bound (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0) :
    v 1≤((p 1:V)+v 5)*v 2 := by
  have hB := graph_B_nonnegative p v hb hv hz
  have hC : (regs (ports p) (masked p v)).C=ι (v 2) := by
    change ((ports p 0)*ι (v 0)+1)-ι (v 1)-
      (((ports p 0)*ι (v 0)+1)-ι (v 1)-ι (v 2))=ι (v 2)
    ring
  rw [B_def,hC] at hB
  change 0≤(((p 1:ℕ):DiffRing V)+ι (v 5))*ι (v 2)-ι (v 1) at hB
  apply ι_le_ι.mp
  have he := sub_nonneg.mp hB
  simpa only [map_add,map_mul,map_natCast] using he

#print axioms Trace74CarrierNonnegative.graph_F_carrier_bound
#print axioms Trace74CarrierNonnegative.graph_B_nonnegative
end Trace74CarrierNonnegative
