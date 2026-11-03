import Trace75Factors
import AdjacentInteger

/-! Adjacent Pell quotient for actual positive zeros of the 75-row trace graph. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace75Adjacent
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Root Trace75RootNonzero Trace75Factors TenPositiveAdjacentInteger
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- An actual positive graph zero supplies the adjacent integral Pell root;
V0 and Z0 are magnitudes of the signed graph values. -/
theorem graph_adjacent (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    let D := delta p v
    let U0 := U p v
    let E0 := E p v
    let M0 := M p v
    let a := D*U0*U0*E0
    let Q := D*(4*a*(1+a))
    ∃ tau f V0 Z0 y : V, 0<tau ∧ 0<f ∧ 0<V0 ∧ 0<y ∧
      E0=tau*tau ∧ 1+a=f*f ∧
      (regs (ports p) (fun j => ι (v j))).V *
        (regs (ports p) (fun j => ι (v j))).V = ι (V0*V0) ∧
      (regs (ports p) (fun j => ι (v j))).Z *
        (regs (ports p) (fun j => ι (v j))).Z = ι (Z0*Z0) ∧
      Z0=(M0*tau*f)*y ∧ Q*(V0*V0)=1+(Q-1)*(y*y) := by
  let D : V := delta p v
  let U0 : V := U p v
  let E0 : V := E p v
  let M0 : V := M p v
  let a : V := D*U0*U0*E0
  let G : V := E0*(1+a)
  let Q : V := D*(4*a*(1+a))
  let B : V := Q-1
  obtain ⟨hD,hU,hE,hM⟩ := factors_positive p v hb hv
  have ha : 0<a := mul_pos (mul_pos (mul_pos hD hU) hU) hE
  have ha1 : 1≤a := pos_iff_one_le.mp ha
  have h4 : 1<4*a := lt_of_lt_of_le (by simp : (1:V)<4)
    (by simpa using mul_le_mul_of_nonneg_left ha1 (by simp : (0:V)≤4))
  have hk : 1<4*a*(1+a) := lt_of_lt_of_le h4 (le_mul_of_one_le_right (by simp) (by simp))
  have hQ : 1<Q := lt_of_lt_of_le hk (le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp hD))
  have hB : 0<B := tsub_pos_iff_lt.mpr hQ
  have hqsub : Q-1+1=Q := tsub_add_cancel_of_le (le_of_lt hQ)
  have hqeq : 1+B=Q := by dsimp [B]; rw [add_comm,hqsub]
  obtain ⟨tau,f,htau,hf,ht,hf2⟩ := graph_roots p v hb hv hz
  change E0=tau*tau at ht
  change 1+a=f*f at hf2
  have hVne := V_nonzero (ports p) v D U0 E0 M0
    hD hU hE hM (delta_eval p v) (U_eval p v) (E_eval p v) (M_eval p v hb hv) hz
  obtain ⟨V0,hV,hVp⟩ := square_rep ((regs (ports p) (fun j => ι (v j))).V)
  obtain ⟨Z0,hZ,_⟩ := square_rep ((regs (ports p) (fun j => ι (v j))).Z)
  have hVpos : 0<V0 := hVp hVne
  have hQV : 0<Q*(V0*V0) := mul_pos (lt_trans (by simp : (0:V)<1) hQ) (mul_pos hVpos hVpos)
  have hqvsub : Q*(V0*V0)-1+1=Q*(V0*V0) := tsub_add_cancel_of_le (pos_iff_one_le.mp hQV)
  have hQcast : ι (Q-1) = ι Q - 1 := by
    apply eq_sub_iff_add_eq.mpr
    rw [←map_one (ι : V →+* DiffRing V),←map_add,hqsub]
  have hQVcast : ι (Q*(V0*V0)-1) = ι (Q*(V0*V0)) - 1 := by
    apply eq_sub_iff_add_eq.mpr
    rw [←map_one (ι : V →+* DiffRing V),←map_add,hqvsub]
  have haeval : (regs (ports p) (fun j => ι (v j))).a = ι a := by
    rw [a_eq,delta_eval,U_eval,E_eval]
    simp only [a,D,U0,E0,pow_two,map_mul]
    ring
  have hgeval : (regs (ports p) (fun j => ι (v j))).Gn = ι G := by
    rw [Gn_def,F0_def,E_eval,haeval]
    simp only [G,E0,map_mul,map_add,map_one,add_comm]
  have hqeval : (regs (ports p) (fun j => ι (v j))).Q = ι Q := by
    rw [Q_def,F0_def,delta_eval,haeval]
    simp only [Q,D,map_mul,map_add,map_one,map_ofNat]
    ring
  have hzero := hz
  rw [value75_def,hqeval,hZ,M_eval p v hb hv,hgeval,hV] at hzero
  have hring : ((ι Q:DiffRing V)-1) * ι (Z0*Z0) =
      (ι M0)*(ι M0) * (ι G * ((ι Q)*(ι (V0*V0))-1)) := by
    linear_combination hzero
  have heq : (Q-1)*(Z0*Z0)=M0*M0*(G*(Q*(V0*V0)-1)) := by
    apply ι_injective
    simp only [map_mul,hQcast,hQVcast]
    simpa only [map_mul,hQcast,hQVcast,mul_assoc] using hring
  let S : V := M0*tau*f
  have hS : 0<S := mul_pos (mul_pos hM htau) hf
  have hG : G=(tau*f)*(tau*f) := by dsimp [G]; rw [ht,hf2]; ring
  have hscaled : (1+B)*((S*V0)*(S*V0))=S*S+B*(Z0*Z0) := calc
    (1+B)*((S*V0)*(S*V0))=M0*M0*(G*(Q*(V0*V0))) := by
      rw [hqeq,hG]; dsimp [S]; ring
    _=M0*M0*(G*((Q*(V0*V0)-1)+1)) := by rw [hqvsub]
    _=M0*M0*(G*(Q*(V0*V0)-1))+S*S := by rw [hG]; dsimp [S]; ring
    _=S*S+B*(Z0*Z0) := by rw [←heq]; ring
  obtain ⟨y,hy,hnorm⟩ := quotient_of_scaled_norm B S V0 Z0 hB hS hVpos hscaled
  rw [hqeq] at hnorm
  have hqnorm : Q*(V0*V0)=1+(Q-1)*(y*y) := hnorm
  have hypos : 0<y := by
    apply pos_iff_ne_zero.mpr
    intro hy0
    have hv1 : 1≤V0 := pos_iff_one_le.mp hVpos
    have hv2 : 1≤V0*V0 := by simpa using mul_le_mul hv1 hv1 (by simp : (0:V)≤1) (by simp : (0:V)≤V0)
    have hle : Q≤Q*(V0*V0) := le_mul_of_one_le_right (by simp) hv2
    rw [hy0] at hqnorm
    simp only [mul_zero,add_zero] at hqnorm
    rw [hqnorm] at hle
    exact (not_le_of_gt hQ) hle
  exact ⟨tau,f,V0,Z0,y,htau,hf,hVpos,hypos,ht,hf2,hV,hZ,hy,hqnorm⟩

#print axioms Trace75Adjacent.graph_adjacent
end Trace75Adjacent
