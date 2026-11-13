import ParentTransportQuotients
import ParentFourFields
import ParentTo88Guard
import ParentTo88First

/-! Source-only parent→88 fresh-root witness. Every imported graph/model
client remains unelaborated; no Lean or endpoint claim. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ModelMapParentTo88Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open ParentTo88FirstDraft ArithmeticAdaptiveQuotients2011 ArithmeticAdaptiveTransportQuotient2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def target (v : Fin 13 → V) (s tau t : V) : Fin 14 → V :=
  ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,sigma v s tau,v 9,v 10,v 11,v 12,t]

theorem target_positive (v : Fin 13 → V) (s tau t : V)
    (hv : ∀ j, 0<v j) (htau : 0<tau) (ht : 0<t) : ∀ j, 0<target v s tau t j := by
  have hsigma : 0<sigma v s tau := by
    dsimp [sigma]
    exact lt_of_lt_of_le htau (by simp)
  intro j
  fin_cases j <;> simp [target,hv,hsigma,ht]

theorem cast_target (v : Fin 13 → V) (s tau t : V) :
    (fun j => ι (target v s tau t j)) =
      RingParentTo88Draft.extend (fun j => ι (v j)) (ι (sigma v s tau)) (ι t) := by
  funext j
  fin_cases j <;> simp [target,RingParentTo88Draft.extend]

/-- Proposed positive parent→quotient-guarded 88 map at natural ports.
No K upper bound, mask inequality, Mersenne condition or target zero is assumed. -/
theorem positive_map (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀ j, 0<v j)
    (hz : InternalZero (P88FourSquare.graph (fun j => (p j : ℤ))).output v) :
    ∃ w : Fin 14 → V, (∀ j, 0<w j) ∧
      InternalZero (P88QuotientGuarded.graph (fun j => (p j : ℤ))).output w := by
  let pi : Fin 4 → ℤ := fun j => (p j : ℤ)
  let z : Fin 13 → DiffRing V := fun j => ι (v j)
  obtain ⟨hq,htrans,s,hs,hY⟩ := ParentTransportQuotientsDraft.quotient_bundle p v hb hv hz
  obtain ⟨t,ht,hbal⟩ := htrans
  obtain ⟨tau,d,htau,hd,hfirst,hn,hmain,hnmain⟩ := hq
  have hY' : v 7=Q p v*s := by simpa only [Q,q,b] using hY
  have hn' : tau*tau=D v := by simpa only [D,ell,k] using hn
  have hf := ParentTo88FirstDraft.first_zero p v s tau t hY' hn'
  have hg := ParentTo88GuardDraft.guard_of_balance p v (sigma v s tau) t hbal
  have hp := ParentFourFieldsDraft.fields_of_zero pi v hz
  let w := RingParentTo88Draft.extend z (ι (sigma v s tau)) (ι t)
  have hm : (P88QuotientGuarded.graph pi).A1.evalRing w=0 := by
    rw [RingParentTo88Draft.main_eval]
    exact hp.2.1
  have ha : (P88QuotientGuarded.graph pi).aux.evalRing w-1=0 := by
    rw [RingParentTo88Draft.aux_eval]
    exact hp.2.2.1
  have hs0 : (P88QuotientGuarded.graph pi).gap.evalRing w=0 := by
    rw [RingParentTo88Draft.strong_eval]
    exact hp.2.2.2
  refine ⟨target v s tau t,target_positive v s tau t hv htau ht,?_⟩
  apply (internalZero_iff _ _).mpr
  rw [P88QuotientGuarded.output_shape]
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,Expr.evalRing_var,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one]
  rw [cast_target v s tau t]
  rw [hf,hm,ha,hs0,hg]
  ring

end DiophantineConsistency.ModelMapParentTo88Draft

#print axioms DiophantineConsistency.ModelMapParentTo88Draft.positive_map
