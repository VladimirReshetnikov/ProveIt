import DiophantineConsistency.TenPositiveTrace75
import DiophantineConsistency.ModelDifferenceRing
import ProductRoot

/-! UNCHECKED DRAFT: root extraction at an arbitrary difference-ring valuation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74ArbitraryRoot
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 TenPositiveProductRoot
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem roots_of_representatives (p : Fin 4 → DiffRing V) (w : Fin 10 → DiffRing V)
    (delta U E M V0 Z0 : V)
    (hdelta : 0<delta) (hU : 0<U) (hE : 0<E) (hM : 0<M) (hV0 : 0<V0)
    (hd : (regs p w).Delta = ι delta)
    (hu : (regs p w).U = ι U)
    (he : (regs p w).E = ι E)
    (hm : (regs p w).M = ι M)
    (hv : (regs p w).V * (regs p w).V = ι (V0*V0))
    (hz : (regs p w).Z * (regs p w).Z = ι (Z0*Z0))
    (hzero : value75 p w = 0) :
    ∃ tau f : V, 0<tau ∧ 0<f ∧ E=tau*tau ∧ 1+delta*U*U*E=f*f := by
  let a : V := delta*U*U*E
  let G : V := E*(1+a)
  let Q : V := delta*(4*a*(1+a))
  have ha : 0<a := mul_pos (mul_pos (mul_pos hdelta hU) hU) hE
  have hQ : 0<Q := mul_pos hdelta (mul_pos (mul_pos (by simp) ha) (by simp))
  have hQV : 0<Q*(V0*V0) := mul_pos hQ (mul_pos hV0 hV0)
  have hqsub : Q-1+1=Q := tsub_add_cancel_of_le (pos_iff_one_le.mp hQ)
  have hqvsub : Q*(V0*V0)-1+1=Q*(V0*V0) := tsub_add_cancel_of_le (pos_iff_one_le.mp hQV)
  have hQcast : ι (Q-1) = ι Q - 1 := by
    apply eq_sub_iff_add_eq.mpr
    rw [← map_one (ι : V →+* DiffRing V), ← map_add, hqsub]
  have hQVcast : ι (Q*(V0*V0)-1) = ι (Q*(V0*V0)) - 1 := by
    apply eq_sub_iff_add_eq.mpr
    rw [← map_one (ι : V →+* DiffRing V), ← map_add, hqvsub]
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
  rw [value75_def,hqeval,hz,hm,hgeval,hv] at hzero
  have hring : ((ι Q:DiffRing V)-1) * ι (Z0*Z0) =
      (ι M)*(ι M) * (ι G * ((ι Q)*(ι (V0*V0))-1)) := by
    linear_combination hzero
  have heq : (Q-1)*(Z0*Z0) = M*M*(G*(Q*(V0*V0)-1)) := by
    apply ι_injective
    simp only [map_mul,hQcast,hQVcast]
    simpa only [map_mul,hQcast,hQVcast,mul_assoc] using hring
  apply doubled_product_roots delta U E V0 Z0 M hdelta hU hE hV0 hM
  simpa only [Q,G,a,add_tsub_cancel_left,mul_assoc] using heq

#print axioms Trace74ArbitraryRoot.roots_of_representatives
end Trace74ArbitraryRoot
