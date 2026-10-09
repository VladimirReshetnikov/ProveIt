import GowersSzemeredi.Proofs16VarietyPieceFamilyCover
import GowersSzemeredi.Proofs16VarietyStructureSide
import GowersSzemeredi.Proofs16WithLift

/-! The variety-piece class supplies the general slice-provider interface.
The hypothesis asks for structured data for each slice. The shared cover
constructs the simultaneous provider for every sample size, with valid
control ranges and polynomial dependence on the sample count.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A final-coordinate section, represented as pairs. -/
def section16FinalPairSection {N : Nat} [NeZero N] (B : Finset (Point N 3)) (t : ZMod N) :
    Finset (ZMod N × ZMod N) :=
  (section16FinalCoordinateSection B t).image fun x => (x 0, x 1)

theorem section16JointVarietyCoverExponent_le_one (C n D : Nat) {p : Nat}
    (hp : 0 < p) (c : Real) : section16JointVarietyCoverExponent C p n D c ≤ 1 := by
  unfold section16JointVarietyCoverExponent section16CappedWidthExponent
  apply (min_le_left _ _).trans
  unfold section16FreimanVarietyExponent
  apply inv_le_one_of_one_le₀
  have h := section16FreimanVarietyDegree_pos hp
    (n * (2 * Nat.ceil (milicevicBound D c))) (n * Nat.ceil (milicevicBound D c))
  exact_mod_cast (show 1 ≤ 2 * section16FreimanVarietyDegree p
    (n * (2 * Nat.ceil (milicevicBound D c))) (n * Nat.ceil (milicevicBound D c)) by omega)

/-- Variety structure on every slice constructs the simultaneous slice
provider required by the general polynomial affine lift. -/
theorem exists_variety_slice_provider :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (N D : Nat) [NeZero N] [Fact N.Prime] (c : Real)
    (B : Finset (Point N 3)) (phi : Point N 3 → ZMod N),
    (∀ t : ZMod N, IsVarietyPiece D c
      (fun q => phi (appendCoordinate (pairPoint q) t)) (section16FinalPairSection B t)) →
    Section16SliceProvider B phi (fun n _ => 9 * n)
      (fun n _ => section16JointVarietyCoverExponent C p n D c) ∧
    Section16SliceProviderRanges (fun n _ => 9 * n)
      (fun n _ => section16JointVarietyCoverExponent C p n D c) := by
  classical
  obtain ⟨C, p, hC, hp, hcover⟩ := exists_variety_piece_family_cover
  refine ⟨C, p, hC, hp, ?_⟩
  intro N D _ _ c B phi hpiece
  constructor
  · intro n sample
    apply hcover N n D c (fun i => section16FinalPairSection B (sample i))
      (fun i q => phi (appendCoordinate (pairPoint q) (sample i)))
      (fun i => hpiece (sample i))
      (fun i => partialGraph (section16FinalCoordinateSection B (sample i))
        (section16FinalCoordinateRestriction phi (sample i)))
    intro i z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    refine ⟨Finset.mem_image_of_mem _ hx, ?_⟩
    change phi (appendCoordinate x (sample i)) =
      phi (appendCoordinate (pairPoint (x 0, x 1)) (sample i))
    rw [pairPoint_coords]
  · intro n eps hn _ _
    have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
    exact ⟨by nlinarith, section16JointVarietyCoverExponent_pos C n D hp c,
      section16JointVarietyCoverExponent_le_one C n D hp c⟩

end LeanProofs.GowersSzemeredi
