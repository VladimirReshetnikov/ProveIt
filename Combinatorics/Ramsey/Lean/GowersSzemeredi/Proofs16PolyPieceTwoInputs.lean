import GowersSzemeredi.Proofs16VertexWithCovers
import GowersSzemeredi.Proofs16FreimanFinalSections
import GowersSzemeredi.Proofs16FreimanFamilyRestriction
import GowersSzemeredi.Proofs16SynchronizedCover

/-! Inputs for the dimension-two polynomial piece cover.

`section16_piece_cover_with` needs a spectrum cover, a remainder cover and
a slice provider on one common sub-domain `D` of the good domain. In
dimension two each comes from `PolyCoverAt 1`, off a global deletion:
* `section16GoodDomain_inter`: restricting the base set to the spectrum's
  good set `J` filters the good domain by `init ∈ J`.
* `Section16PhiOneIdentity.mono`.
* `section16_final_freiman_families_of_product`: every final-coordinate
  slice keeps all but `θN` points in a Freiman family of size
  `section16BaseFamilyBound γ θ`. The pruned set `B*` carries
  `Section16FinalFreimanFamilies`.
* `Section16FinalFreimanFamilies.of_translate`: any domain whose
  translated points lie in `B*` carries the families of `φ₁`.
* `card_translated_slice_bad_le`: the translated points that miss `B*`
  number at most `θN²`.
* `cubicSlice_count_monotone` and `cubicSlice_exponent_antitone`: the
  cubic slice controls are monotone in the sample size.

`Section16FinalFreimanFamilies.of_translate`, `cubicSlice_count_monotone` and
`cubicSlice_exponent_antitone` are in `Proofs16PolyPieceTwoInputsSide`, outside
the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem section16GoodDomain_inter {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H J : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h)) (x0 : Point N k) :
    section16GoodDomain B (H ∩ J) Y x0 =
      (section16GoodDomain B H Y x0).filter fun z => section16Init z ∈ J := by
  ext z
  simp only [section16GoodDomain, Section16GoodInducedPair, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_inter]
  tauto

theorem Section16PhiOneIdentity.mono {N k : Nat} [NeZero N]
    {B1 B1' : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N} {x0 : Point N k}
    {phiPrime : Point N k → ZMod N → ZMod N}
    (h : Section16PhiOneIdentity B1 phi x0 phiPrime) (hsub : B1' ⊆ B1) :
    Section16PhiOneIdentity B1' phi x0 phiPrime :=
  fun z hz => h z (hsub hz)

/-- Every final-coordinate slice of a product-property function keeps all
but `θN` of its points in a Freiman family. -/
theorem section16_final_freiman_families_of_product {N : Nat} [Fact N.Prime]
    {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (B : Finset (Point N 2)) (phi : Point N 2 → ZMod N)
    (hprod : HasProductProperty B phi gamma) :
    ∃ C : ZMod N → Finset (Point N 1),
      (∀ t, C t ⊆ section16FinalCoordinateSection B t) ∧
      (∀ t, ((section16FinalCoordinateSection B t).card : Real) - theta * N ≤ (C t).card) ∧
      Section16FinalFreimanFamilies (section16BaseFamilyBound gamma theta)
        (B.filter fun z => section16Init z ∈ C (section16Last z)) phi := by
  have hsl (t : ZMod N) : HasProductProperty (section16FinalCoordinateSection B t)
      (section16FinalCoordinateRestriction phi t) gamma := by
    have hdom : (lastSliceFace 1 t).domain B = section16FinalCoordinateSection B t := by
      ext x; simp [CoordinateFace.domain, section16FinalCoordinateSection, lastSliceFace]
    rw [← hdom]
    exact hprod.coordinateFace (lastSliceFace 1 t)
  choose C hCsub hCcard hCfam using fun t =>
    section16_restrict_function_freiman_family hg hg1 ht ht1 _ _ (hsl t)
  refine ⟨C, hCsub, hCcard, fun t => (hCfam t).mono fun y hy => ?_⟩
  simpa only [section16Init_appendCoordinate, section16Last_appendCoordinate] using
    (Finset.mem_filter.mp (Finset.mem_filter.mp hy).2).2

/-- The translated points of a slice-pruned set that miss it are sparse, in
every dimension. -/
theorem card_translated_slice_bad_le_succ {N k : Nat} [NeZero N] {theta : Real}
    (B : Finset (Point N (k + 1))) (C : ZMod N → Finset (Point N k))
    (hC : ∀ t, C t ⊆ section16FinalCoordinateSection B t)
    (hcard : ∀ t, ((section16FinalCoordinateSection B t).card : Real) - theta * (N : Real) ^ k ≤
      (C t).card)
    (x0 : Point N k) :
    (((Finset.univ : Finset (Point N (k + 1))).filter fun z =>
        appendCoordinate (section16Init z + x0) (section16Last z) ∈ B ∧
          section16Init z + x0 ∉ C (section16Last z)).card : Real) ≤
      theta * (N : Real) ^ (k + 1) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := section16Last) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  push_cast
  refine (Finset.sum_le_card_nsmul _ _ (theta * (N : Real) ^ k) fun t _ => ?_).trans_eq
    (by rw [Finset.card_univ, ZMod.card, nsmul_eq_mul, pow_succ]; ring)
  have hsum : ((section16FinalCoordinateSection B t \ C t).card : Real) + (C t).card =
      (section16FinalCoordinateSection B t).card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card (hC t)
  refine le_trans (Nat.cast_le.2 (Finset.card_le_card_of_injOn (fun z => section16Init z + x0)
    (t := section16FinalCoordinateSection B t \ C t) (fun z hz => ?_)
    fun z hz z' hz' hzz => ?_)) (by linarith [hcard t])
  · obtain ⟨hz1, rfl⟩ := Finset.mem_filter.mp hz
    simpa [section16FinalCoordinateSection] using (Finset.mem_filter.mp hz1).2
  · exact initLast_injective (Prod.ext (add_right_cancel hzz)
      ((Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hz').2.symm))

/-- The translated points of a slice-pruned set that miss it are sparse. -/
theorem card_translated_slice_bad_le {N : Nat} [NeZero N] {theta : Real}
    (B : Finset (Point N 2)) (C : ZMod N → Finset (Point N 1))
    (hC : ∀ t, C t ⊆ section16FinalCoordinateSection B t)
    (hcard : ∀ t, ((section16FinalCoordinateSection B t).card : Real) - theta * N ≤ (C t).card)
    (x0 : Point N 1) :
    (((Finset.univ : Finset (Point N 2)).filter fun z =>
        appendCoordinate (section16Init z + x0) (section16Last z) ∈ B ∧
          section16Init z + x0 ∉ C (section16Last z)).card : Real) ≤
      theta * (N : Real) ^ 2 := by
  simpa using card_translated_slice_bad_le_succ (k := 1) B C hC (fun t => by simpa using hcard t) x0

end LeanProofs.GowersSzemeredi
