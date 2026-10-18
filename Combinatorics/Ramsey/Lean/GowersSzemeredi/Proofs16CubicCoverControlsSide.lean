import GowersSzemeredi.Proofs16CubicCoverControls
import GowersSzemeredi.Proofs16FreimanSliceProviderSide

/-! Declarations of `Proofs16CubicCoverControls` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

/-- Concrete sampled-slice covers with graph count independent of the loss
and an explicit cubic exponent. -/
theorem section16_cubic_slice_provider_of_freiman_families {N q : Nat} [Fact N.Prime]
    (hq : 0 < q) (B : Finset (Point N 2)) (phi : Point N 2 → ZMod N)
    (D : ZMod N → Fin q → Finset (Point N 1))
    (f : ZMod N → Fin q → Point N 1 → ZMod N)
    (hfreiman : ∀ t i, FreimanHom 8 (pointOneDomain (D t i)) (pointOneMap (f t i)))
    (hcover : ∀ t, partialGraph (section16FinalCoordinateSection B t)
      (section16FinalCoordinateRestriction phi t) ⊆
        section16FinsetUnion (fun i => partialGraph (D t i) (f t i))) :
    Section16SliceProvider B phi
      (fun r _ => ((3 * (max 1 r * q) : Nat) : Real))
      (fun r => cubicBaseExponent (max 1 r * q)) := by
  intro r sample
  have hp : 0 < max 1 r * q := Nat.mul_pos (by omega) hq
  apply (section16_slice_provider_of_freiman_families hq B phi D f
    hfreiman hcover r sample).weaken
  · intros; exact le_rfl
  · intro s hs _; exact cubicBaseExponent_pos hp hs
  · intro s hs hs1; exact polyBaseExponent_ge_cubic hp hs hs1

end

end LeanProofs.GowersSzemeredi
