import ZFCinPA.ValidatorEindContext222

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace LeanProofs.ZFCinPA.ValidatorEindContext222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222 ValidatorEind222
open ValidatorEnvironmentVacuity222 ValidatorEindContext222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem empty_context (B : V) : eindContext (0 : V) B=0 := eindContext_nil B

theorem repeated_zero_diagonal : CProv (eindContext ((0 : V)∷0∷0) (0∷0∷0)) :=
  eindContext_diagonal _

theorem one_slot_projection (a b : V) :
    CProv (wim (eindContext (a∷0) (b∷0)) (Eind a b)) := by
  simpa using eindContext_projection (a∷0) (b∷0) 0 (by simp)

/-- The generalized label may equal the Eind atom's own auxiliary. -/
theorem auxiliary_collision (a b : V) :
    Vac (aux a b) (eindContext (a∷0) (b∷0)) :=
  eindContext_vac _ _ _ (by simp)
    (avoid_cons (avoid_nil _) (aux_ne a b).1)
    (avoid_cons (avoid_nil _) (aux_ne a b).2)

/-- Both binder labels may be zero; only the actual four Vac resources matter. -/
theorem zero_binders (B B' p q : V)
    (hb : CProv (wim (eindContext ((0 : V)∷B) (0∷B')) (wim p q)))
    (vh : Vac 0 (eindContext B B')) (vq : Vac 0 q) (vp : Vac 0 (wal 0 p)) :
    CProv (wim (eindContext B B') (wim (wal 0 p) (wal 0 q))) :=
  all_of_cons B B' p q 0 0 hb vh vq vh vp

#print axioms eindContext_graph
#print axioms eindContext_total_unique
#print axioms prefix_projection
#print axioms prefix_cons_equiv
#print axioms primitive_premise
#print axioms prefixContext_vac
#print axioms eindContext_diagonal
#print axioms all_of_cons_avoiding_context
#print axioms projection_witness
#print axioms repeated_zero_diagonal
#print axioms auxiliary_collision
#print axioms zero_binders
end LeanProofs.ZFCinPA.ValidatorEindContext222Checks
