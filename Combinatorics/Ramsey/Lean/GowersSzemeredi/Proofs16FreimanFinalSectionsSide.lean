import GowersSzemeredi.Proofs16FreimanFinalSections
import GowersSzemeredi.Proofs16CubicCoverControlsSide

/-! Declarations of `Proofs16FreimanFinalSections` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- Concrete section-family witnesses discharge the cubic slice provider. -/
theorem Section16FinalFreimanFamilies.cubic_slice_provider {N q : Nat} [Fact N.Prime]
    {B : Finset (Point N 2)} {phi : Point N 2 → ZMod N}
    (h : Section16FinalFreimanFamilies q B phi) (hq : 0 < q) :
    Section16SliceProvider B phi
      (fun r _ => ((3 * (max 1 r * q) : Nat) : Real))
      (fun r => cubicBaseExponent (max 1 r * q)) := by
  choose D f hf hc using h
  exact section16_cubic_slice_provider_of_freiman_families hq B phi D f hf hc

end LeanProofs.GowersSzemeredi
