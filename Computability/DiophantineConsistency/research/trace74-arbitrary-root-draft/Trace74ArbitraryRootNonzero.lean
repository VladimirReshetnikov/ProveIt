import Trace74ArbitraryRoot

/-! UNCHECKED DRAFT: signed V/Z and arbitrary difference-ring valuation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74ArbitraryRootNonzero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 Trace74ArbitraryRoot
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

theorem V_nonzero (p : Fin 4 → DiffRing V) (w : Fin 10 → DiffRing V)
    (delta U E M : V) (hdelta : 0<delta) (hU : 0<U) (hE : 0<E) (hM : 0<M)
    (hd : (regs p w).Delta = ι delta)
    (hu : (regs p w).U = ι U)
    (he : (regs p w).E = ι E)
    (hm : (regs p w).M = ι M)
    (hzero : value75 p w = 0) :
    (regs p w).V ≠ 0 := by
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
  have haeval : (regs p w).a = ι a := by
    rw [a_eq,hd,hu,he]
    simp only [a,pow_two,map_mul]
    ring
  have hgeval : (regs p w).Gn = ι G := by
    rw [Gn_def,F0_def,he,haeval]
    simp only [G,map_mul,map_add,map_one,add_comm]
  have hqeval : (regs p w).Q = ι Q := by
    rw [Q_def,F0_def,hd,haeval]
    simp only [Q,map_mul,map_add,map_one,map_ofNat]
    ring
  have hnonneg : 0 ≤ ((regs p w).Q-1)*
      ((regs p w).Z*(regs p w).Z) := by
    apply mul_nonneg
    · rw [hqeval,←hQcast]
      exact ι_nonneg (Q-1)
    · simpa only [pow_two] using sq_nonneg ((regs p w).Z)
  have hmpos : 0<(ι M : DiffRing V) := ι_lt_ι.mpr hM
  have hgpos : 0<(ι G : DiffRing V) := ι_lt_ι.mpr hG
  have hprod : 0<(ι M : DiffRing V)*(ι M)*(ι G) := mul_pos (mul_pos hmpos hmpos) hgpos
  intro hv
  rw [value75_def,hv,hm,hgeval,hqeval] at hzero
  simp only [mul_zero] at hzero
  rw [hqeval] at hnonneg
  nlinarith

theorem roots_of_positive_representatives (p : Fin 4 → DiffRing V) (w : Fin 10 → DiffRing V)
    (delta U E M : V) (hdelta : 0<delta) (hU : 0<U) (hE : 0<E) (hM : 0<M)
    (hd : (regs p w).Delta = ι delta)
    (hu : (regs p w).U = ι U)
    (he : (regs p w).E = ι E)
    (hm : (regs p w).M = ι M)
    (hzero : value75 p w = 0) :
    ∃ tau f : V, 0<tau ∧ 0<f ∧ E=tau*tau ∧ 1+delta*U*U*E=f*f := by
  have hv := V_nonzero p w delta U E M hdelta hU hE hM hd hu he hm hzero
  obtain ⟨V0,hV0,hVp⟩ := square_rep ((regs p w).V)
  obtain ⟨Z0,hZ0,_⟩ := square_rep ((regs p w).Z)
  exact roots_of_representatives p w delta U E M V0 Z0 hdelta hU hE hM (hVp hv)
    hd hu he hm hV0 hZ0 hzero

#print axioms Trace74ArbitraryRootNonzero.roots_of_positive_representatives
end Trace74ArbitraryRootNonzero
