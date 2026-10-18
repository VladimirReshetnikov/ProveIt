import GowersSzemeredi.Proofs16FreimanFinalSections
import GowersSzemeredi.Proofs16CubicCoverControlsSide
import GowersSzemeredi.Proofs16FreimanFamilyRestrictionSide

/-! Declarations of `Proofs16FreimanFinalSections` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- The same family count works for the translated sections of any selected
common-base good domain. -/
theorem Section16FinalFreimanFamilies.good_domain {N q : Nat} [NeZero N]
    {B : Finset (Point N 2)} {phi : Point N 2 → ZMod N}
    (h : Section16FinalFreimanFamilies q B phi)
    (H : Finset (Point N 1)) (Y : (a : Point N 1) → Finset (Section16CubeElement B a))
    (x0 : Point N 1) :
    Section16FinalFreimanFamilies q (section16GoodDomain B H Y x0)
      (section16PhiOne phi x0) := by
  intro t
  have hp := (h t).translate (-x0)
  have heq : (fun y => section16FinalCoordinateRestriction phi t (y - -x0)) =
      section16FinalCoordinateRestriction (section16PhiOne phi x0) t := by
    funext y
    simp [section16FinalCoordinateRestriction, section16PhiOne,
      section16Init_appendCoordinate, section16Last_appendCoordinate, sub_neg_eq_add, add_comm]
    rfl
  rw [heq] at hp
  apply hp.mono
  intro y hy
  have hv := section16GoodDomain_vertex_mem B H Y x0 (Finset.mem_filter.mp hy).2 (fun _ => true)
  have hb : appendCoordinate (y + x0) t ∈ B := by
    simpa only [section16Init_appendCoordinate, section16Last_appendCoordinate,
      ite_true, ← Pi.add_def, add_comm] using hv
  apply Finset.mem_image.mpr
  refine ⟨y + x0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, by simp⟩

end LeanProofs.GowersSzemeredi

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
