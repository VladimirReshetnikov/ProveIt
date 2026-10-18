import GowersSzemeredi.Proofs16ThreeSlices
import GowersSzemeredi.Proofs16PolyCoverTwoSide
import GowersSzemeredi.Proofs16UniformCoverTwoBounds

/-! Declarations of `Proofs16ThreeSlices` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false
set_option exponentiation.threshold 1024

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

/-! ### The slice decomposition -/

/-- **Every section decomposes into pieces of the uniform class.** -/
theorem section16_slice_decomposition_three
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] (hN : polyTwoThreshold theta gamma ≤ N)
    (B : Finset (Point N 3)) (phi : Point N 3 → ZMod N) (hprod : HasProductProperty B phi gamma) :
    ∃ C : ZMod N → Finset (Point N 2),
      (∀ t, C t ⊆ section16FinalCoordinateSection B t) ∧
      (∀ t, ((section16FinalCoordinateSection B t).card : Real) - theta * (N : Real) ^ 2 ≤
        (C t).card) ∧
      ∃ P : ZMod N → Fin (polyTwoPieces gamma theta) → PolyPieceTwo N theta gamma,
        ∀ t, partialGraph (C t) (section16FinalCoordinateRestriction phi t) ⊆
          polyPieceTwoGraphs (P t) := by
  have hex : ∀ t : ZMod N, ∃ J : Finset (Point N 2), (1 - theta) * (N : Real) ^ 2 ≤ J.card ∧
      ∃ P : Fin (polyTwoPieces gamma theta) → PolyPieceTwo N theta gamma,
        restrictRelation (partialGraph (section16FinalCoordinateSection B t)
          (section16FinalCoordinateRestriction phi t)) J ⊆ polyPieceTwoGraphs P := by
    intro t
    have hg2 : (1 : Real) ≤ gamma ^ (-(2 : Int)) := by
      rw [zpow_neg, zpow_ofNat]
      exact one_le_inv₀ (by positivity) |>.mpr (pow_le_one₀ hg.le hg1)
    have hsize : ((partialGraph (section16FinalCoordinateSection B t)
        (section16FinalCoordinateRestriction phi t)).card : Real) ≤
        gamma ^ (-(2 : Int)) * (N : Real) ^ 2 := by
      rw [partialGraph_card]
      have h : ((section16FinalCoordinateSection B t).card : Real) ≤ (N : Real) ^ 2 := by
        have h := Finset.card_le_univ (section16FinalCoordinateSection B t)
        have hc : Fintype.card (Point N 2) = N ^ 2 := by
          simp [Point, ZMod.card]
        rw [hc] at h
        exact_mod_cast h
      nlinarith
    exact section16_poly_piece_decomposition_two ht ht1 hg hg1 hN _ hsize
      (partialGraph_relationProductProperty (hprod.final_section t))
  choose J hJ P hP using hex
  refine ⟨fun t => (section16FinalCoordinateSection B t).filter (· ∈ J t), fun t =>
    Finset.filter_subset _ _, ?_, P, ?_⟩
  · intro t
    have hsplit : ((section16FinalCoordinateSection B t).filter (· ∈ J t)).card +
        ((section16FinalCoordinateSection B t).filter (fun h => ¬ h ∈ J t)).card =
        (section16FinalCoordinateSection B t).card :=
      Finset.card_filter_add_card_filter_not (fun h => h ∈ J t)
    have hbad : ((section16FinalCoordinateSection B t).filter (fun h => ¬ h ∈ J t)).card ≤
        (Finset.univ \ J t).card := by
      apply Finset.card_le_card
      intro h hh
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hh).2⟩
    have hcompl : ((Finset.univ \ J t).card : Real) = (N : Real) ^ 2 - (J t).card := by
      have hsd := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (J t))
      have hc : (Finset.univ : Finset (Point N 2)).card = N ^ 2 := by
        rw [Finset.card_univ]; simp [Point, ZMod.card]
      rw [hc] at hsd
      have hsd' : ((Finset.univ \ J t).card : Real) + (J t).card = (N : Real) ^ 2 := by
        exact_mod_cast hsd
      linarith
    have h1 : (((section16FinalCoordinateSection B t).filter (· ∈ J t)).card : Real) +
        ((section16FinalCoordinateSection B t).filter (fun h => ¬ h ∈ J t)).card =
        (section16FinalCoordinateSection B t).card := by exact_mod_cast hsplit
    have h2 : (((section16FinalCoordinateSection B t).filter (fun h => ¬ h ∈ J t)).card : Real) ≤
        (Finset.univ \ J t).card := by exact_mod_cast hbad
    have h3 := hJ t
    rw [hcompl] at h2
    linarith
  · intro t z hz
    apply hP t
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hhS, hhJ⟩ := Finset.mem_filter.mp hh
    unfold restrictRelation
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨h, hhS, rfl⟩, hhJ⟩

/-- The uniform cover of `r` slices, at the envelope controls. -/
theorem section16_slices_envelope_cover {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1)
    (hlemma6 : AbstractFamilyLemma166At 1
      (section16PowerWidth (familyWidthPrefactor K1) (familyWidthDivisor 1 p1)))
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] {r : Nat}
    (Gammas : Fin r → Finset (Point N 2 × ZMod N))
    (P : Fin r → Fin (polyTwoPieces gamma theta) → PolyPieceTwo N theta gamma)
    (hP : ∀ i, Gammas i ⊆ polyPieceTwoGraphs (P i)) :
    MultiplyLinearWith (threeSlicePb theta gamma K1 p1 r) (threeSliceEs theta gamma K1 p1 r)
      (Finset.univ.biUnion Gammas) := by
  have hA : ∀ q, 0 < familyWidthPrefactor K1 q := familyWidthPrefactor_pos (by omega)
  have hB : ∀ q, 0 < familyWidthDivisor 1 p1 q := familyWidthDivisor_pos hp1
  have hcov := section16_uniform_cover_two hA hB hlemma6 ht ht1 hg hg1 Gammas
    (fun _ => Finset.univ) P (fun i => (Finset.filter_subset _ _).trans (hP i))
  have hsub : Finset.univ.biUnion Gammas ⊆
      Finset.univ.biUnion fun i => restrictRelation (Gammas i) Finset.univ := by
    intro z hz
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hz
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩
    unfold restrictRelation
    exact Finset.mem_filter.mpr ⟨hi, Finset.mem_univ _⟩
  refine MultiplyLinearWith.subset (MultiplyLinearWith.weaken hcov ?_ ?_ ?_) hsub
  · intro eps he he1
    obtain ⟨hv, hr, hM, _, _⟩ := threeSliceBase_facts ht ht1 hg hg1 K1 p1 r he he1
    have hW2 := threeSliceBase_two_le ht ht1 hg hg1 K1 p1 r he he1
    have hW1 : 1 ≤ threeSliceBase theta gamma K1 p1 r eps := le_trans (by norm_num) hW2
    exact uniTwoCount_le_power hg hg1 ht ht1 he he1 hv hr
      (hM.trans (le_self_pow₀ hW1 (by norm_num)))
  · intro eps he he1
    have hW2 := threeSliceBase_two_le ht ht1 hg hg1 K1 p1 r he he1
    exact inv_pos.mpr (pow_pos (lt_of_lt_of_le (by norm_num) hW2) _)
  · intro eps he he1
    obtain ⟨hv, hr, hM, hKw, hpw⟩ := threeSliceBase_facts ht ht1 hg hg1 K1 p1 r he he1
    have hW2 := threeSliceBase_two_le ht ht1 hg hg1 K1 p1 r he he1
    have hW1 : 1 ≤ threeSliceBase theta gamma K1 p1 r eps := le_trans (by norm_num) hW2
    have h := uniTwoExp_inv_le_power hK1 hp1 hg hg1 ht ht1 he he1 hv hr
      (hM.trans (le_self_pow₀ hW1 (by norm_num))) (hKw.trans (le_self_pow₀ hW1 (by norm_num)))
      (hpw.trans (le_self_pow₀ hW1 (by norm_num)))
    have h0 := uniTwoExp_pos (A := familyWidthPrefactor K1) hB (theta := theta) (gamma := gamma)
      (r * polyTwoPieces gamma theta) he
    exact (inv_le_comm₀ h0 (pow_pos (lt_of_lt_of_le (by norm_num) hW2) _)).mp h

/-- **The slice provider of a three-dimensional piece.** -/
theorem section16_three_slice_provider {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1)
    (hlemma6 : AbstractFamilyLemma166At 1
      (section16PowerWidth (familyWidthPrefactor K1) (familyWidthDivisor 1 p1)))
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] (phi : Point N 3 → ZMod N)
    (C : ZMod N → Finset (Point N 2))
    (P : ZMod N → Fin (polyTwoPieces gamma theta) → PolyPieceTwo N theta gamma)
    (hP : ∀ t, partialGraph (C t) (section16FinalCoordinateRestriction phi t) ⊆
      polyPieceTwoGraphs (P t))
    (x0 : Point N 2) (D : Finset (Point N 3))
    (hD : ∀ z ∈ D, section16Init z + x0 ∈ C (section16Last z)) :
    Section16SliceProvider D (section16PhiOne phi x0) (threeSlicePb theta gamma K1 p1)
      (threeSliceEs theta gamma K1 p1) := by
  intro r sample
  have hcov := section16_slices_envelope_cover hK1 hp1 hlemma6 ht ht1 hg hg1
    (fun i => partialGraph (C (sample i)) (section16FinalCoordinateRestriction phi (sample i)))
    (fun i => P (sample i)) (fun i => hP (sample i))
  refine MultiplyLinearWith.subset (hcov.translate (-x0)) ?_
  intro z hz
  unfold section16StackedSlices section16FinsetUnion at hz
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hi
  have hhD : appendCoordinate h (sample i) ∈ D := by
    unfold section16FinalCoordinateSection at hh
    exact (Finset.mem_filter.mp hh).2
  have hC := hD _ hhD
  simp only [section16Init_appendCoordinate, section16Last_appendCoordinate] at hC
  refine Finset.mem_image.mpr ⟨(h + x0, section16FinalCoordinateRestriction phi (sample i) (h + x0)),
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨h + x0, hC, rfl⟩⟩, ?_⟩
  have hfun : (fun j => x0 j + section16Init (appendCoordinate h (sample i)) j) = h + x0 := by
    funext j
    simp [section16Init_appendCoordinate, add_comm]
  simp only [section16FinalCoordinateRestriction, section16PhiOne, hfun,
    section16Last_appendCoordinate, add_neg_cancel_right]

end

end LeanProofs.GowersSzemeredi
