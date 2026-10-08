import GowersSzemeredi.Proofs16FreimanFinalSections
import GowersSzemeredi.Proofs16ProductAnchors

/-! Extract fixed Freiman families on all final-coordinate slices at once.
The slices are disjoint, so the one-dimensional deletion bounds sum to one
ambient-volume loss. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Reassemble a family of final-coordinate sections. -/
def section16SliceUnion {N k : Nat} [NeZero N]
    (C : ZMod N → Finset (Point N k)) : Finset (Point N (k + 1)) :=
  Finset.univ.biUnion fun t => (C t).image (fun x => appendCoordinate x t)

theorem section16FinalCoordinateSection_sliceUnion {N k : Nat} [NeZero N]
    (C : ZMod N → Finset (Point N k)) (t : ZMod N) :
    section16FinalCoordinateSection (section16SliceUnion C) t = C t := by
  classical
  ext x
  simp only [section16FinalCoordinateSection, Finset.mem_filter, Finset.mem_univ, true_and,
    section16SliceUnion, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨s, y, hy, heq⟩
    have ht : s = t := by simpa only [section16Last_appendCoordinate] using congrArg section16Last heq
    have hx : y = x := by simpa only [section16Init_appendCoordinate] using congrArg section16Init heq
    simpa [ht, hx] using hy
  · exact fun hx => ⟨t, x, hx, rfl⟩

theorem section16SliceUnion_card {N k : Nat} [NeZero N]
    (C : ZMod N → Finset (Point N k)) :
    (section16SliceUnion C).card = ∑ t, (C t).card := by
  classical
  unfold section16SliceUnion
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro t _
    apply Finset.card_image_of_injective
    intro x y h
    simpa only [section16Init_appendCoordinate] using congrArg section16Init h
  · intro t _ s _ hts
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hz'
    apply hts
    simpa only [section16Last_appendCoordinate] using congrArg section16Last (hx.trans hy.symm)

theorem section16SliceUnion_sections {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) :
    section16SliceUnion (section16FinalCoordinateSection B) = B := by
  classical
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨t, -, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp hx).2
  · intro z hz
    apply Finset.mem_biUnion.mpr
    refine ⟨section16Last z, Finset.mem_univ _, Finset.mem_image.mpr
      ⟨section16Init z, ?_, appendCoordinate_init_last z⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [appendCoordinate_init_last] using hz⟩

/-- The final-coordinate sections can all be pruned with the same family
bound, paying theta times the ambient volume in total. -/
theorem section16_restrict_final_freiman_families {N : Nat} [Fact N.Prime]
    {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1)
    (B : Finset (Point N 2)) (phi : Point N 2 → ZMod N)
    (hprod : HasProductProperty B phi gamma) :
    ∃ C : Finset (Point N 2), C ⊆ B ∧
      (B.card : Real) - theta * (N : Real)^2 ≤ C.card ∧
      Section16FinalFreimanFamilies (section16BaseFamilyBound gamma theta) C phi := by
  classical
  have hs (t : ZMod N) : HasProductProperty (section16FinalCoordinateSection B t)
      (section16FinalCoordinateRestriction phi t) gamma :=
    hprod.coordinateFace (CoordinateFace.lastSlice t)
  choose C hsub hmass hfamily using fun t => section16_restrict_function_freiman_family
    hg hg1 ht ht1 _ _ (hs t)
  refine ⟨section16SliceUnion C, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨t, -, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp (hsub t hx)).2
  · have hsum := Finset.sum_le_sum (s := Finset.univ)
      (fun t (_ : t ∈ (Finset.univ : Finset (ZMod N))) => hmass t)
    have hBsum : (∑ t, ((section16FinalCoordinateSection B t).card : Real)) = B.card := by
      exact_mod_cast ((section16SliceUnion_card (section16FinalCoordinateSection B)).symm.trans
        (congrArg Finset.card (section16SliceUnion_sections B)))
    have hCsum : (∑ t, ((C t).card : Real)) = (section16SliceUnion C).card := by
      exact_mod_cast (section16SliceUnion_card C).symm
    rw [Finset.sum_sub_distrib, hBsum, hCsum] at hsum
    have hvol : (∑ _t : ZMod N, theta * (N : Real)) = theta * (N : Real)^2 := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      ring
    rwa [hvol] at hsum
  · intro t
    rw [section16FinalCoordinateSection_sliceUnion]
    exact hfamily t

end LeanProofs.GowersSzemeredi
