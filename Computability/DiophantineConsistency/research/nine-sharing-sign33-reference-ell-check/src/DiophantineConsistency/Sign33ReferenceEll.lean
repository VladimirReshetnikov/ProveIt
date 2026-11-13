import DiophantineConsistency.Norm38ReferenceFieldsAll

/-! Generic source reference ell binding, independent of model witnesses. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ReferenceEll
open Norm38Reference

theorem reference_ell {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 30 = (Carrier65.core p x).ell := by
  simp [reference, Carrier65.core] <;> ring
end DiophantineConsistency.Sign33ReferenceEll
#print axioms DiophantineConsistency.Sign33ReferenceEll.reference_ell
