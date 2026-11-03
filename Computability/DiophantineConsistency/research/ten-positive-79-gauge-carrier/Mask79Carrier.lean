import Mathlib.Tactic.Ring

/-! Corrected 79-coordinate gauge preserving both rank and full main carrier. -/
set_option autoImplicit false
set_option Elab.async false
namespace Mask79Carrier
variable {R : Type*} [CommRing R]

theorem preserve_rank_and_main (q b k w F C n v u H Z P t : R) :
    let D := q*(k+w)+1
    let F' := F+b*t
    let C' := C-q*b*t
    let n' := n-(b*v+1)*D*t
    q*(q-F')-C' = q*(q-F)-C ∧
    (b*u)*(H*(n'-v*((k+w)*C'-F'))+Z)-H*(u*((k+w)*C'-F')+b*P) =
      (b*u)*(H*(n-v*((k+w)*C-F))+Z)-H*(u*((k+w)*C-F)+b*P) := by
  dsimp only
  constructor <;> ring

#print axioms Mask79Carrier.preserve_rank_and_main
end Mask79Carrier
