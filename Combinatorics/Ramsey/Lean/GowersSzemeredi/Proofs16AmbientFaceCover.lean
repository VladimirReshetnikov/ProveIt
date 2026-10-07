import GowersSzemeredi.Proofs16EmbeddedLift
import GowersSzemeredi.Proofs16Translations

/-! Genuine proper-face covers extend to ambient coordinate retractions.
The selected domain may be restricted arbitrarily as long as its retracted
points belong to the original domain. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Extend, translate, and restrict a face cover without changing its
parameters. This is the form needed for the non-top cube vertices. -/
theorem ProperCrossSectionsMultiplyLinear.ambient_face_cover
    {N d l : Nat} [NeZero N] [Fact N.Prime] {gamma s : Real}
    {B : Finset (Point N d)} {phi : Point N d → ZMod N}
    (hfaces : ProperCrossSectionsMultiplyLinear gamma s B phi)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hs : 2 ≤ s)
    (hgraphs : ((3 ^ d : Nat) : Real) ≤ s)
    (F : CoordinateFace N d l) (hl : l < d) (t : Point N d)
    (D : Finset (Point N d))
    (hD : ∀ z ∈ D, F.map (selectedCoordinates F.free (z + t)) ∈ B) :
    MultiplyLinearFunction gamma s D
      (fun z => phi (F.map (selectedCoordinates F.free (z + t)))) := by
  classical
  have hp := ((hfaces l hl F).lift_embedding hg hg1 hs hgraphs F.free).translate (-t)
  simp only [neg_neg] at hp
  apply hp.mono
  intro z hz
  refine Finset.mem_image.mpr ⟨z + t, ?_, by simp⟩
  rw [mem_selectedDomain, CoordinateFace.mem_domain]
  exact hD z hz

/-- The original structured-pair parameters meet the quantitative reserve
for each proper face, including a zero-dimensional face. -/
theorem Section16StructuredPair.ambient_face_cover
    {N k l : Nat} [NeZero N] [Fact N.Prime] {theta gamma : Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (h : Section16StructuredPair theta gamma B phi)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (F : CoordinateFace N (k + 1) l) (hl : l < k + 1) (t : Point N (k + 1))
    (D : Finset (Point N (k + 1)))
    (hD : ∀ z ∈ D, F.map (selectedCoordinates F.free (z + t)) ∈ B) :
    MultiplyLinearFunction gamma
      (gamma ^ (-(2 : Int)) * multipleS ((2 : Real) ^ (-(k + 2 : Real)) * theta) gamma k)
      D (fun z => phi (F.map (selectedCoordinates F.free (z + t)))) := by
  obtain ⟨hs, hreserve⟩ := section16_face_parameter_lift_reserve k ht ht1 hg hg1
  exact h.1.ambient_face_cover hg hg1 hs (hreserve (k + 1) le_rfl) F hl t D hD

end LeanProofs.GowersSzemeredi
