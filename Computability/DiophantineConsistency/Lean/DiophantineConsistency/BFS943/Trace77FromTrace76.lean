import DiophantineConsistency.BFS943.Trace77Circuit
import DiophantineConsistency.BFS943.Trace76Transport
import DiophantineConsistency.BFS943.Trace75OffsetExact

/-! # Every positive 76/352 zero gives a positive 77/348 zero

The completeness map. At a positive 76 zero, moving `n` up by
`(V² - bV) B ≥ 0` gives a positive 75 zero with the same offset `e`
(`Trace76Transport.graph_transport`, `value75_update`), so the promoted
first-index alignment `Trace75OffsetExact.graph_offset_exact` gives
`e = XY ρ` with `ρ = 4 Y s ≥ 0`. Moving the 76 coordinate `n` up by
`(w s - 1) ρ ≥ 0` multiplies nothing but rescales the carrier:
`TenPositiveTrace77.value77_shift` gives `(w s)² value77 = value76 = 0` at
the moved point. No 77-specific reverse construction is needed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace77FromTrace76
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 TenPositiveTrace76 TenPositiveTrace77
open Trace75Factors Trace75Pell
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive77_of_positive76 (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : value76 (ports p) (fun j => ι (v j)) = 0) :
    ∃ w : Fin 10 → V, (∀j,0<w j) ∧ value77 (ports p) (fun j => ι (w j)) = 0 := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  let rr := regs (ports p) (fun j => ι (v j))
  -- the 75 zero with the same offset
  let d : DiffRing V := (rr.V*rr.V-rr.b*rr.V)*rr.B
  have hd : 0≤d := (Trace76Transport.graph_transport p v hb hv hz).2
  obtain ⟨t,ht⟩ : ∃ t : V, (ι t:DiffRing V)=d := by
    rcases nonneg_or_nonpos d with ⟨t,ht⟩|⟨t,ht⟩
    · exact ⟨t,ht.symm⟩
    · refine ⟨t,?_⟩
      have h0 : (ι t:DiffRing V)≤0 := by linarith
      have h1 : (ι t:DiffRing V)=0 := le_antisymm h0 (ι_nonneg t)
      rw [ht,h1]; simp
  let w : Fin 10 → V := Function.update v 7 (v 7+t)
  have hw : ∀j,0<w j := by
    intro j
    by_cases hj : j=7
    · subst hj; simp only [w,Function.update_self]; exact add_pos_of_pos_of_nonneg (hv 7) (by simp)
    · simp only [w,Function.update_of_ne hj]; exact hv j
  have hcast : (fun j => (ι (w j):DiffRing V)) =
      Function.update (fun j => ι (v j)) 7 (ι (v 7)+d) := by
    funext j
    by_cases hj : j=7
    · subst hj; simp only [w,Function.update_self,map_add,ht]
    · simp only [w,Function.update_of_ne hj]
  have hz75 : value75 (ports p) (fun j => ι (w j)) = 0 := by
    rw [hcast,value75_update (ports p) (fun j => ι (v j)) (ι (v 7)+d) rfl]
    exact hz
  obtain ⟨_n,s,_hn,_halign,_hk,he⟩ := Trace75OffsetExact.graph_offset_exact p w hb31 hl hh hw hz75
  have hew : (regs (ports p) (fun j => ι (w j))).e=rr.e := by rw [hcast]; rfl
  have hfp : firstParam p w=firstParam p v := rfl
  have hYw : Y p w=Y p v := rfl
  rw [hew,hfp] at he
  -- the offset in the form `e = XY ρ`
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hXr : rr.X=ι (X p v) := by
    dsimp [rr]
    simp only [X_def,q_def,h_def,ports,X,q,b,map_mul,map_add,map_one,map_natCast]
  have hYr : rr.Y=ι (Y p v) := by
    dsimp [rr]
    simp only [Y_def,q_def,h_def,ports,Y,q,b,map_mul,map_add,map_one,map_natCast]
  let rho : DiffRing V := ι (4*Y p v*s)
  have heXY : rr.e=rr.X*rr.Y*rho := by
    rw [he,hXr,hYr]
    dsimp [rho,firstParam]
    simp only [map_mul,map_ofNat]
    ring
  -- the moved 77 coordinate
  have hws : 1≤v 5*v 6 := pos_iff_one_le.mp (mul_pos (hv 5) (hv 6))
  let n' : V := v 7+(v 5*v 6-1)*(4*Y p v*s)
  have hn' : 0<n' := add_pos_of_pos_of_nonneg (hv 7) (by simp)
  have hcastn : (ι n':DiffRing V)=ι (v 7)+(ι (v 5)*ι (v 6)-1)*rho := by
    have hsub : (ι (v 5*v 6-1):DiffRing V)=ι (v 5)*ι (v 6)-1 := by
      apply eq_sub_iff_add_eq.mpr
      rw [←map_one (ι : V →+* DiffRing V),←map_add,tsub_add_cancel_of_le hws,map_mul]
    dsimp [n',rho]
    rw [map_add,map_mul,hsub]
  let w' : Fin 10 → V := Function.update v 7 n'
  have hw' : ∀j,0<w' j := by
    intro j
    by_cases hj : j=7
    · subst hj; simp only [w',Function.update_self]; exact hn'
    · simp only [w',Function.update_of_ne hj]; exact hv j
  have hcast' : (fun j => (ι (w' j):DiffRing V)) =
      Function.update (fun j => ι (v j)) 7 (ι (v 7)+(ι (v 5)*ι (v 6)-1)*rho) := by
    funext j
    by_cases hj : j=7
    · subst hj; simp only [w',Function.update_self,hcastn]
    · simp only [w',Function.update_of_ne hj]
  refine ⟨w',hw',?_⟩
  have hshift := value77_shift (ports p) (fun j => ι (v j)) rho
    (ι (v 7)+(ι (v 5)*ι (v 6)-1)*rho) heXY rfl
  rw [hz] at hshift
  have hW : (ι (v 5)*ι (v 6):DiffRing V)≠0 := by
    apply ne_of_gt
    exact mul_pos (by rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hv 5)
      (by rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hv 6)
  rw [hcast']
  exact (mul_eq_zero.mp hshift).resolve_left (mul_ne_zero hW hW)

#print axioms Trace77FromTrace76.positive77_of_positive76
end Trace77FromTrace76
