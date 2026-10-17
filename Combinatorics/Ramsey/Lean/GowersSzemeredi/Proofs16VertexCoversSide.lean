import GowersSzemeredi.Proofs16VertexCovers
import GowersSzemeredi.Proofs16CoordinateMaskFacesSide
import GowersSzemeredi.Proofs16UnusedCoordinateParameter

/-! Declarations of `Proofs16VertexCovers` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- The proper-face hypothesis suffices for each non-top vertex, without
any line-cover or common-base spectral hypothesis. -/
theorem ProperCrossSectionsMultiplyLinear.good_domain_vertex_cover
    {N k : Nat} [NeZero N] [Fact N.Prime] {gamma r : Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (hfaces : ProperCrossSectionsMultiplyLinear gamma r B phi)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hr : 2 ≤ r)
    (hgraphs : ((3 ^ (k + 1) : Nat) : Real) ≤ r)
    (H : Finset (Point N k)) (Y : (h : Point N k) → Finset (Section16CubeElement B h))
    (x0 : Point N k) (e : Fin k → Bool) (he : e ≠ fun _ => true) :
    MultiplyLinearFunction gamma r (section16GoodDomain B H Y x0)
      (section16TranslatedVertex phi x0 e) := by
  have hp := hfaces.coordinate_mask_cover hg hg1 hr hgraphs (section16VertexDirections e)
    (section16VertexDirections_card_lt he) (appendCoordinate x0 0) (appendCoordinate x0 0)
    (section16GoodDomain B H Y x0) (by
      intro z hz
      rw [section16_vertex_coordinate_mask]
      exact section16GoodDomain_vertex_mem B H Y x0 hz e)
  simp only [section16_vertex_coordinate_mask] at hp
  exact hp

/-- The actual structured-pair parameter automatically pays for every
non-top vertex cover. -/
theorem Section16StructuredPair.good_domain_vertex_cover
    {N k : Nat} [NeZero N] [Fact N.Prime] {theta gamma : Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (h : Section16StructuredPair theta gamma B phi)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (H : Finset (Point N k)) (Y : (a : Point N k) → Finset (Section16CubeElement B a))
    (x0 : Point N k) (e : Fin k → Bool) (he : e ≠ fun _ => true) :
    MultiplyLinearFunction gamma
      (gamma ^ (-(2 : Int)) * multipleS ((2 : Real) ^ (-(k + 2 : Real)) * theta) gamma k)
      (section16GoodDomain B H Y x0) (section16TranslatedVertex phi x0 e) := by
  obtain ⟨hr, hreserve⟩ := section16_face_parameter_lift_reserve k ht ht1 hg hg1
  exact h.1.good_domain_vertex_cover hg hg1 hr (hreserve (k + 1) le_rfl) H Y x0 e he

end LeanProofs.GowersSzemeredi
