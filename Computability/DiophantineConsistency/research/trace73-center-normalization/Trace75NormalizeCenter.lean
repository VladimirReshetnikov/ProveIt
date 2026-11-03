import Trace75KappaRoot
import Trace75SignFlip
import Trace75IntegralTransport
import Trace73ModelSigns

/-! Normalize a trace75 zero to a positive trace73 center. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace75NormalizeCenter
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace75Adjacent Trace75Transport Trace75IntegralTransport
open Trace73ModelTransfer Trace73ModelSigns
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_zero_to_center (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V))
    (hh : (p 3:V)<2*(p 0:V)) (hv : ∀j,0<v j)
    (hz : value75 (Trace75Factors.ports p) (fun j => ι (v j)) = 0) :
    ∃ w : Fin 10 → V, (∀j,0<w j) ∧
      Trace73Literal.graph73 (Trace73ModelTransfer.ports p) (castVal w) = 0 := by
  let rr := regs (Trace75Factors.ports p) (fun j => ι (v j))
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  obtain ⟨tau,f,V0,Z0,y,ht,hf,hV,hy,hE,hf2,hVs,hZs,hZeq,_⟩ :=
    graph_adjacent p v hb hv hz
  obtain ⟨kappa,_hkp,hK⟩ := Trace75Kappa.graph_positive_kappa p v hb31 hl hh hv hz
  obtain ⟨t,hB⟩ := graph_integral_transport p v hb31 hl hh hv hz
  obtain ⟨_n,s,_hn,_halign,_hk,he⟩ := Trace75OffsetExact.graph_offset_exact p v hb31 hl hh hv hz
  let L : V := tau*f*y
  let rho : V := 4*Y p v*s
  have hkf : kappa<f := Trace75KappaRoot.quotient_below_root p v kappa f hb hv hK hf2
  have hfL : f≤L := by
    dsimp [L]
    calc
      f≤tau*f := le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp ht)
      _≤tau*f*y := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hy)
  have hkL : kappa<L := lt_of_lt_of_le hkf hfL
  have hkLR : (ι kappa : DiffRing V)<ι L := ι_lt_ι.mpr hkL
  have hBnonneg : 0≤rr.B := (graph_transport_and_mask p v hb hv hz).1
  have hshift : 0≤shift p v := shift_nonneg_of_B p v hBnonneg
  have hMpos : 0<M p v := (factors_positive p v hb hv).2.2.2
  have hMne : rr.M≠0 := by
    rw [show rr.M=ι (M p v) from M_eval p v hb hv]
    exact ne_of_gt (by simpa only [map_zero] using ι_lt_ι.mpr hMpos)
  have hZsq : rr.Z*rr.Z=(rr.M*ι L)*(rr.M*ι L) := by
    calc
      rr.Z*rr.Z=ι (Z0*Z0) := hZs
      _=(rr.M*ι L)*(rr.M*ι L) := by
        rw [hZeq, show rr.M=ι (M p v) from M_eval p v hb hv]
        dsimp [L]
        simp only [map_mul]
        ring
  have hsign : rr.Z=rr.M*ι L ∨ rr.Z= -(rr.M*ι L) := by
    have hfactor : (rr.Z-rr.M*ι L)*(rr.Z+rr.M*ι L)=0 := by
      rw [show (rr.Z-rr.M*ι L)*(rr.Z+rr.M*ι L)=rr.Z*rr.Z-(rr.M*ι L)*(rr.M*ι L) by ring,hZsq]
      ring
    rcases mul_eq_zero.mp hfactor with h|h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hheval : rr.h=ι (b p v) := by dsimp [rr]; simp only [h_def,Trace75Factors.ports,b,map_mul,map_natCast]
  have hDeval : rr.D=ι (X p v*Y p v) := by
    dsimp [rr]
    simp only [D_def,X_def,Y_def,q_def,h_def,Trace75Factors.ports,X,Y,q,b,map_mul,map_add,map_one,map_natCast]
  have heval : rr.e=ι (X p v*Y p v)*ι rho := by
    rw [he,←map_mul]
    congr 1
    dsimp [rho,Trace75Pell.firstParam]
    ring
  have hMshape : rr.M=rr.h*rr.D*rr.H := by dsimp [rr]; rw [M_def,D_def]
  have hshape : rr.Z=rr.h*rr.D*(rr.H*(ι (v 7)-shift p v)+rr.K)-
      rr.H*(rr.D*rr.B+rr.h*rr.e) := by
    change rr.Z=rr.h*rr.D*(rr.H*(ι (v 7)-rr.V*rr.V*rr.B)+rr.K)-
      rr.H*(rr.D*rr.B+rr.h*rr.e)
    dsimp [rr]
    rw [Z_def,D_def]
  have hZformula : rr.Z = rr.M*(ι (v 7)-shift p v+ι kappa-ι t-ι rho) := by
    rw [hshape,hMshape,hK,hB,heval,hheval,hDeval]
    simp only [map_mul]
    ring
  have ht0 : (0:DiffRing V)≤ι t := ι_nonneg t
  have hrho0 : (0:DiffRing V)≤ι rho := ι_nonneg rho
  rcases hsign with hplus|hminus
  · have hbal : (ι (v 7):DiffRing V)-shift p v+ι kappa-ι t-ι rho=ι L := by
      apply mul_left_cancel₀ hMne
      rw [←hZformula,hplus]
    have hbound : shift p v < (ι (v 7):DiffRing V) := by linarith
    exact from75_of_bounds p v hv hshift hbound hz
  · let w := Function.update v 7 (v 7+2*L)
    have hw : ∀j,0<w j := by
      intro j
      by_cases hj : j=7
      · subst j; simp only [w,Function.update_self]; exact lt_of_lt_of_le (hv 7) (by simp)
      · simpa [w,hj] using hv j
    have hbal : (ι (v 7):DiffRing V)-shift p v+ι kappa-ι t-ι rho= -ι L := by
      apply mul_left_cancel₀ hMne
      rw [←hZformula,hminus,mul_neg]
    have hbound : shift p w < (ι (w 7):DiffRing V) := by
      rw [show shift p w=shift p v from shift_update p v _]
      simp only [w,Function.update_self,map_add,map_mul,map_ofNat]
      linarith
    have hmove : castVal w=Trace75SignFlip.move (castVal v) (ι L) := by
      funext j
      by_cases hj : j=7
      · subst j; simp [w,castVal,Trace75SignFlip.move,map_add,map_mul,map_ofNat]
      · simp [w,castVal,Trace75SignFlip.move,hj]
    have hz' : value75 (Trace73ModelTransfer.ports p) (castVal w)=0 := by
      change value75 (Trace75Factors.ports p) (castVal w)=0
      rw [hmove]
      change value75 (Trace75Factors.ports p) (Trace75SignFlip.move (fun j => ι (v j)) (ι L))=0
      rw [Trace75SignFlip.value_flip _ _ _ hminus]
      exact hz
    have hshift' : 0≤shift p w := by rwa [show shift p w=shift p v from shift_update p v _]
    exact from75_of_bounds p w hw hshift' hbound hz'

#print axioms Trace75NormalizeCenter.positive_zero_to_center
end Trace75NormalizeCenter
