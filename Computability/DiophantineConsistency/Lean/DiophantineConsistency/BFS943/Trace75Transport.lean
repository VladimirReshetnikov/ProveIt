import DiophantineConsistency.BFS943.Trace75CarrierBound
import DiophantineConsistency.BFS943.Trace75OffsetBound
import DiophantineConsistency.BFS943.Trace75Kpos
import DiophantineConsistency.BFS943.CarrierTransport

/-! Nonnegative signed transport and positive mask for trace75 zeros. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75Transport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace75CarrierBound Trace75OffsetBound Trace75Kpos TenPositiveCarrierTransport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_transport_and_mask (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    0≤(regs (ports p) (fun j => ι (v j))).B ∧ v 1+v 2<q p v := by
  let rr := regs (ports p) (fun j => ι (v j))
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
    rw [M_eval p v hb hv]
    exact hZ
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hA : 0<A p v := add_pos (mul_pos hX hY) hY
  have hhr : rr.h=ι (b p v) := by
    dsimp [rr]
    simp only [h_def,ports,b,map_mul,map_natCast]
  have hDr : rr.D=ι (X p v*Y p v) := by
    dsimp [rr]
    simp only [D_def,X_def,Y_def,q_def,h_def,ports,X,Y,q,b,map_mul,map_add,map_one,map_natCast]
  have hAr : rr.Am1=ι (A p v) := by
    dsimp [rr]
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
  have hB : 0≤rr.B := model_nonnegative_of_carrier rr.h rr.H rr.D (rr.V*rr.V) rr.B rr.K rr.e z
    (ι (v 7)) rr.Z hh hH hm hL hK hn hzbound he hZ'' hshape
  have hwpos : (0:DiffRing V)<ι (v 5) := by rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hv 5
  have hfpos : (0:DiffRing V)<ι (v 1) := by rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hv 1
  have hcoef : 0<(ports p) 1+ι (v 5) := add_pos_of_nonneg_of_pos (by simp [ports]) hwpos
  have hBeq : rr.B=((ports p) 1+ι (v 5))*rr.C-ι (v 1) := by
    dsimp [rr]
    rw [B_def]
  have hprod : 0<((ports p) 1+ι (v 5))*rr.C := by rw [hBeq] at hB; linarith
  have hC : 0<rr.C := pos_of_mul_pos_right hprod (le_of_lt hcoef)
  have hCeq : rr.C=ι (q p v)-ι (v 1)-ι (v 2) := by
    dsimp [rr]
    simp only [C_def,q_def,h_def,ports,q,b,map_mul,map_add,map_one,map_natCast]
  have hqbound : (ι (v 1+v 2):DiffRing V)<ι (q p v) := by rw [hCeq] at hC; simp only [map_add]; linarith
  exact ⟨hB,ι_lt_ι.mp hqbound⟩

#print axioms Trace75Transport.graph_transport_and_mask
end Trace75Transport
