import Mask79Carrier

/-! Propagate the corrected gauge through an arbitrary finalizer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Mask79Finalizer
variable {R : Type*} [CommRing R]

theorem preserve_output (q b k w F C n v u H Z P t L T : R) :
    let D := q*(k+w)+1
    let F' := F+b*t
    let C' := C-q*b*t
    let n' := n-(b*v+1)*D*t
    let main' := (b*u)*(H*(n'-v*((k+w)*C'-F'))+Z)-H*(u*((k+w)*C'-F')+b*P)
    let main := (b*u)*(H*(n-v*((k+w)*C-F))+Z)-H*(u*((k+w)*C-F)+b*P)
    L*(main'*main'-T*v)+T-main'*main' = L*(main*main-T*v)+T-main*main := by
  have h := (Mask79Carrier.preserve_rank_and_main q b k w F C n v u H Z P t).2
  dsimp only at h ⊢
  rw [h]

#print axioms Mask79Finalizer.preserve_output
end Mask79Finalizer
