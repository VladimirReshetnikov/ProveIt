import Trace75Root

/-! Remove signed V/Z representatives from conditional trace75 extraction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace75RootNonzero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 Trace75Root
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem square_rep (x : DiffRing V) :
    ∃ a : V, x*x=ι (a*a) ∧ (x≠0 → 0<a) := by
  rcases nonneg_or_nonpos x with ⟨a,ha⟩ | ⟨a,ha⟩
  · refine ⟨a,?_,?_⟩
    · rw [ha,map_mul]
    · intro hx
      apply pos_iff_ne_zero.mpr
      intro h
      apply hx
      simpa [h] using ha
  · refine ⟨a,?_,?_⟩
    · rw [ha,map_mul]
      ring
    · intro hx
      apply pos_iff_ne_zero.mpr
      intro h
      apply hx
      simpa [h] using ha

theorem V_nonzero (p : Fin 4 → DiffRing V) (v : Fin 10 → V)
    (delta U E M : V) (hdelta : 0<delta) (hU : 0<U) (hE : 0<E) (hM : 0<M)
    (hd : (regs p (fun j => ι (v j))).Delta = ι delta)
    (hu : (regs p (fun j => ι (v j))).U = ι U)
    (he : (regs p (fun j => ι (v j))).E = ι E)
    (hm : (regs p (fun j => ι (v j))).M = ι M)
    (hzero : value75 p (fun j => ι (v j)) = 0) :
    (regs p (fun j => ι (v j))).V ≠ 0 := by
  let a : V := delta*U*U*E
  let G : V := E*(1+a)
  let Q : V := delta*(4*a*(1+a))
  have ha : 0<a := mul_pos (mul_pos (mul_pos hdelta hU) hU) hE
  have hQ : 0<Q := mul_pos hdelta (mul_pos (mul_pos (by simp) ha) (by simp))
  have hG : 0<G := mul_pos hE (by simp)
  have hqsub : Q-1+1=Q := tsub_add_cancel_of_le (pos_iff_one_le.mp hQ)
  have hQcast : ι (Q-1) = ι Q - 1 := by
    apply eq_sub_iff_add_eq.mpr
    rw [← map_one (ι : V →+* DiffRing V), ← map_add, hqsub]
  have haeval : (regs p (fun j => ι (v j))).a = ι a := by
    rw [a_eq,hd,hu,he]
    simp only [a,pow_two,map_mul]
    ring
  have hgeval : (regs p (fun j => ι (v j))).Gn = ι G := by
    rw [Gn_def,F0_def,he,haeval]
    simp only [G,map_mul,map_add,map_one,add_comm]
  have hqeval : (regs p (fun j => ι (v j))).Q = ι Q := by
    rw [Q_def,F0_def,hd,haeval]
    simp only [Q,map_mul,map_add,map_one,map_ofNat]
    ring
  have hnonneg : 0 ≤ ((regs p (fun j => ι (v j))).Q-1)*
      ((regs p (fun j => ι (v j))).Z*(regs p (fun j => ι (v j))).Z) := by
    apply mul_nonneg
    · rw [hqeval,←hQcast]
      exact ι_nonneg (Q-1)
    · simpa only [pow_two] using sq_nonneg ((regs p (fun j => ι (v j))).Z)
  have hmpos : 0<(ι M : DiffRing V) := ι_lt_ι.mpr hM
  have hgpos : 0<(ι G : DiffRing V) := ι_lt_ι.mpr hG
  have hprod : 0<(ι M : DiffRing V)*(ι M)*(ι G) := mul_pos (mul_pos hmpos hmpos) hgpos
  intro hv
  rw [value75_def,hv,hm,hgeval,hqeval] at hzero
  simp only [mul_zero] at hzero
  rw [hqeval] at hnonneg
  nlinarith

theorem roots_of_positive_representatives (p : Fin 4 → DiffRing V) (v : Fin 10 → V)
    (delta U E M : V) (hdelta : 0<delta) (hU : 0<U) (hE : 0<E) (hM : 0<M)
    (hd : (regs p (fun j => ι (v j))).Delta = ι delta)
    (hu : (regs p (fun j => ι (v j))).U = ι U)
    (he : (regs p (fun j => ι (v j))).E = ι E)
    (hm : (regs p (fun j => ι (v j))).M = ι M)
    (hzero : value75 p (fun j => ι (v j)) = 0) :
    ∃ tau f : V, 0<tau ∧ 0<f ∧ E=tau*tau ∧ 1+delta*U*U*E=f*f := by
  have hv := V_nonzero p v delta U E M hdelta hU hE hM hd hu he hm hzero
  obtain ⟨V0,hV0,hVp⟩ := square_rep ((regs p (fun j => ι (v j))).V)
  obtain ⟨Z0,hZ0,_⟩ := square_rep ((regs p (fun j => ι (v j))).Z)
  exact roots_of_representatives p v delta U E M V0 Z0 hdelta hU hE hM (hVp hv)
    hd hu he hm hV0 hZ0 hzero

#print axioms Trace75RootNonzero.roots_of_positive_representatives
end Trace75RootNonzero
