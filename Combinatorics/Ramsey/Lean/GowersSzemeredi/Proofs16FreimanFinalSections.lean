import GowersSzemeredi.Proofs16FreimanFamilyRestriction
import GowersSzemeredi.Proofs16GoodDomainTransport

/-! Transport fixed Freiman families into the common-base good domain.
The original section families survive both translation and deletion; their
count is independent of the inner loss in the later affine lift.

`Section16FinalFreimanFamilies.cubic_slice_provider` and
`Section16FinalFreimanFamilies.good_domain` are in
`Proofs16FreimanFinalSectionsSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Every final-coordinate section has a fixed-size Freiman graph cover. -/
def Section16FinalFreimanFamilies {N : Nat} [NeZero N] (q : Nat)
    (B : Finset (Point N 2)) (phi : Point N 2 → ZMod N) : Prop :=
  ∀ t, Section16FreimanFamilyCover q (section16FinalCoordinateSection B t)
    (section16FinalCoordinateRestriction phi t)

theorem Section16FinalFreimanFamilies.mono {N q : Nat} [NeZero N]
    {B C : Finset (Point N 2)} {phi : Point N 2 → ZMod N}
    (h : Section16FinalFreimanFamilies q B phi) (hCB : C ⊆ B) :
    Section16FinalFreimanFamilies q C phi := by
  intro t
  apply (h t).mono
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hCB (Finset.mem_filter.mp hx).2⟩

end LeanProofs.GowersSzemeredi
