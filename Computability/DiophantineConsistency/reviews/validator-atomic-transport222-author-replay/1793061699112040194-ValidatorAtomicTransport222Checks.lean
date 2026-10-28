import ZFCinPA.ValidatorAtomicTransport222

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace LeanProofs.ZFCinPA.ValidatorAtomicTransport222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorEind222 ValidatorEindContext222
open ValidatorAtomicTransport222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem repeated_zero_endpoints : CProv (Eind (0 : V) 0) := eind_refl 0

theorem auxiliary_as_endpoint (a b : V) :
    CProv (wim (Eind a (aux a b))
      (wim (Eind b (0 : V)) (wim (wel a b) (wel (aux a b) 0)))) :=
  rel_congr a (aux a b) b 0

theorem same_context_reverse (B B' s t P Q : V)
    (h : CProv (wim (eindContext (s∷B) (t∷B')) (wim Q P))) :
    CProv (wim (eindContext B B') (wim (weq t s) (wim Q P))) :=
  reverse_primitive_premise (discharge_cons B B' s t h)

theorem free_fallback_diagonal (B B' i : V) :
    CProv (wim (eindContext B B') (Eind (1 : V) 1)) := by
  have hf := term_eind_under
    (IsSemiterm.fvar (L := ℒₛₑₜ) (len B) i) (0 : V) B B' rfl
  simpa only [ValidatorEnvironmentLabels254.TermLabels.term_fvar,
    ValidatorEnvironmentLabels254.freeLabel_nil] using hf

#print axioms eind_refl
#print axioms eind_symm
#print axioms eind_trans
#print axioms eind_congr
#print axioms rel_congr
#print axioms term_eind_under
#print axioms atom_eq_under
#print axioms reverse_primitive_premise
#print axioms atom_forward_witness
#print axioms repeated_zero_endpoints
#print axioms auxiliary_as_endpoint
#print axioms same_context_reverse
#print axioms free_fallback_diagonal
end LeanProofs.ZFCinPA.ValidatorAtomicTransport222Checks
