import GowersSzemeredi.Proofs16UniformCoverTwoBounds

/-! The slices of a three-dimensional piece (Notes L.5, D2).

In dimension three the final-coordinate sections `h ↦ φ(h, t)` of a piece are
two-dimensional partial functions with the product property. The cubic lift
needs any `r` of them, stacked, to be covered with controls monotone in `r`.
* `section16_slice_decomposition_three`: above Lemma 15.6's threshold, every
  section has a good part `C t` of all but `θN²` points. Its graph lies in
  `polyTwoPieces γ θ` pieces of the uniform class.
* `section16_three_slice_provider`: the stacked slices of `φ₁ = φ(x₀ + ·, ·)`
  on any domain `D` with `init z + x₀ ∈ C (last z)` for all `z ∈ D` form a
  `Section16SliceProvider`. The proof is the uniform cover at
  `r·polyTwoPieces` pieces (`section16_uniform_cover_two`), translated by
  `-x₀`.
* The controls are the power envelopes `threeSlicePb`, `threeSliceEs` of the
  base `(r+1)(m+1)(K₁+p₁+1)·2/(γθε)`. They are monotone and antitone in `r`
  and dominate the actual controls by `uniTwoCount_le_power` and
  `uniTwoExp_inv_le_power`.
* `card_translated_slice_bad_le_succ`: the translated points that miss the
  good parts number at most `θN^(k+1)`, in every dimension. -/
set_option autoImplicit false
set_option exponentiation.threshold 1024
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
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
  classical
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

/-! ### The stacked slice provider -/

/-- The base of the slice envelopes. -/
def threeSliceBase (theta gamma : Real) (K1 p1 : Nat) (r : Nat) (eps : Real) : Real :=
  ((r : Real) + 1) * ((polyTwoPieces gamma theta : Real) + 1) * ((K1 : Real) + p1 + 1) *
    (2 / (gamma * theta * |eps|))

/-- The count envelope of the stacked slices. -/
def threeSlicePb (theta gamma : Real) (K1 p1 : Nat) : Nat → Real → Real :=
  fun r eps => threeSliceBase theta gamma K1 p1 r eps ^ ((2 : Nat) ^ 89)

/-- The exponent envelope of the stacked slices. -/
def threeSliceEs (theta gamma : Real) (K1 p1 : Nat) : Nat → Real → Real :=
  fun r eps => (threeSliceBase theta gamma K1 p1 r eps ^ ((2 : Nat) ^ 130))⁻¹

theorem threeSliceBase_facts {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (K1 p1 r : Nat) {eps : Real} (he : 0 < eps)
    (he1 : eps ≤ 1) :
    2 / (gamma * theta) ≤ threeSliceBase theta gamma K1 p1 r eps ∧
      eps⁻¹ ≤ threeSliceBase theta gamma K1 p1 r eps ∧
      ((r * polyTwoPieces gamma theta : Nat) : Real) ≤ threeSliceBase theta gamma K1 p1 r eps ∧
      (K1 : Real) ≤ threeSliceBase theta gamma K1 p1 r eps ∧
      (p1 : Real) ≤ threeSliceBase theta gamma K1 p1 r eps := by
  have hgt : 0 < gamma * theta := mul_pos hg ht
  have hgt1 : gamma * theta ≤ 1 := mul_le_one₀ hg1 ht.le ht1
  unfold threeSliceBase
  rw [abs_of_pos he]
  have hc2 : 2 ≤ 2 / (gamma * theta * eps) := by
    rw [le_div_iff₀ (by positivity)]
    have : gamma * theta * eps ≤ 1 := mul_le_one₀ hgt1 he.le he1
    linarith
  have hv : 2 / (gamma * theta) ≤ 2 / (gamma * theta * eps) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  have hei : eps⁻¹ ≤ 2 / (gamma * theta * eps) := by
    rw [show 2 / (gamma * theta * eps) = 2 / (gamma * theta) * eps⁻¹ by field_simp]
    have h2 : (1 : Real) ≤ 2 / (gamma * theta) := by rw [le_div_iff₀ hgt]; linarith
    have := inv_pos.mpr he
    nlinarith
  have hr1 : (1 : Real) ≤ (r : Real) + 1 := by linarith [(Nat.cast_nonneg r : (0 : Real) ≤ r)]
  have hm1 : (1 : Real) ≤ (polyTwoPieces gamma theta : Real) + 1 := by
    linarith [(Nat.cast_nonneg (polyTwoPieces gamma theta) : (0 : Real) ≤ _)]
  have hK1 : (1 : Real) ≤ (K1 : Real) + p1 + 1 := by
    linarith [(Nat.cast_nonneg K1 : (0 : Real) ≤ K1), (Nat.cast_nonneg p1 : (0 : Real) ≤ p1)]
  have hc0 : (0 : Real) ≤ 2 / (gamma * theta * eps) := by positivity
  set c := 2 / (gamma * theta * eps)
  set a := (r : Real) + 1
  set b := (polyTwoPieces gamma theta : Real) + 1
  set d := (K1 : Real) + p1 + 1
  have hab : 1 ≤ a * b := one_le_mul_of_one_le_of_one_le hr1 hm1
  have habd : 1 ≤ a * b * d := one_le_mul_of_one_le_of_one_le hab hK1
  have hbase : c ≤ a * b * d * c := le_mul_of_one_le_left hc0 habd
  have hc1 : 1 ≤ c := le_trans (by norm_num) hc2
  refine ⟨hv.trans hbase, hei.trans hbase, ?_, ?_, ?_⟩
  · push_cast
    have h1 : (r : Real) * (polyTwoPieces gamma theta : Real) ≤ a * b := by
      have := Nat.cast_nonneg (α := Real) r
      have := Nat.cast_nonneg (α := Real) (polyTwoPieces gamma theta)
      nlinarith
    calc (r : Real) * (polyTwoPieces gamma theta : Real) ≤ a * b := h1
      _ ≤ a * b * d := le_mul_of_one_le_right (by linarith) hK1
      _ ≤ a * b * d * c := le_mul_of_one_le_right (by linarith) hc1
  · have h1 : (K1 : Real) ≤ d := by linarith [(Nat.cast_nonneg p1 : (0 : Real) ≤ p1)]
    calc (K1 : Real) ≤ d := h1
      _ ≤ a * b * d := le_mul_of_one_le_left (by linarith) hab
      _ ≤ a * b * d * c := le_mul_of_one_le_right (by linarith) hc1
  · have h1 : (p1 : Real) ≤ d := by linarith [(Nat.cast_nonneg K1 : (0 : Real) ≤ K1)]
    calc (p1 : Real) ≤ d := h1
      _ ≤ a * b * d := le_mul_of_one_le_left (by linarith) hab
      _ ≤ a * b * d * c := le_mul_of_one_le_right (by linarith) hc1

theorem threeSliceBase_two_le {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (K1 p1 r : Nat) {eps : Real} (he : 0 < eps)
    (he1 : eps ≤ 1) : 2 ≤ threeSliceBase theta gamma K1 p1 r eps := by
  obtain ⟨hv, -, -, -, -⟩ := threeSliceBase_facts ht ht1 hg hg1 K1 p1 r he he1
  obtain ⟨hv2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  exact hv2.trans hv

theorem threeSliceBase_mono (theta gamma : Real) (ht : 0 < theta) (hg : 0 < gamma)
    (K1 p1 : Nat) (eps : Real) : Monotone fun r => threeSliceBase theta gamma K1 p1 r eps := by
  intro r r' hrr
  dsimp only
  unfold threeSliceBase
  have hr : (r : Real) ≤ r' := by exact_mod_cast hrr
  have h0 : (0 : Real) ≤ ((polyTwoPieces gamma theta : Real) + 1) * ((K1 : Real) + p1 + 1) *
      (2 / (gamma * theta * |eps|)) := by positivity
  have e1 : ((r : Real) + 1) * ((polyTwoPieces gamma theta : Real) + 1) * ((K1 : Real) + p1 + 1) *
      (2 / (gamma * theta * |eps|)) = ((r : Real) + 1) * (((polyTwoPieces gamma theta : Real) + 1) *
      ((K1 : Real) + p1 + 1) * (2 / (gamma * theta * |eps|))) := by ring
  have e2 : ((r' : Real) + 1) * ((polyTwoPieces gamma theta : Real) + 1) * ((K1 : Real) + p1 + 1) *
      (2 / (gamma * theta * |eps|)) = ((r' : Real) + 1) * (((polyTwoPieces gamma theta : Real) + 1) *
      ((K1 : Real) + p1 + 1) * (2 / (gamma * theta * |eps|))) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right (by linarith) h0

/-- The envelopes have the ranges and monotonicity the lift needs. -/
theorem threeSlice_ranges {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (K1 p1 : Nat) :
    Section16SliceProviderRanges (threeSlicePb theta gamma K1 p1) (threeSliceEs theta gamma K1 p1) ∧
      (∀ eps, Monotone fun r => threeSlicePb theta gamma K1 p1 r eps) ∧
      (∀ eps, 0 < eps → Antitone fun r => threeSliceEs theta gamma K1 p1 r eps) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r eps _ he he1
    have h2 := threeSliceBase_two_le ht ht1 hg hg1 K1 p1 r he he1
    have hpos : 0 < threeSliceBase theta gamma K1 p1 r eps := lt_of_lt_of_le (by norm_num) h2
    refine ⟨one_le_pow₀ (le_trans (by norm_num) h2), inv_pos.mpr (pow_pos hpos _), ?_⟩
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_trans (by norm_num) h2))
  · intro eps r r' hrr
    show threeSliceBase theta gamma K1 p1 r eps ^ ((2 : Nat) ^ 89) ≤
      threeSliceBase theta gamma K1 p1 r' eps ^ ((2 : Nat) ^ 89)
    exact pow_le_pow_left₀ (by unfold threeSliceBase; positivity)
      (threeSliceBase_mono theta gamma ht hg K1 p1 eps hrr) _
  · intro eps he r r' hrr
    show (threeSliceBase theta gamma K1 p1 r' eps ^ ((2 : Nat) ^ 130))⁻¹ ≤
      (threeSliceBase theta gamma K1 p1 r eps ^ ((2 : Nat) ^ 130))⁻¹
    have hpos : 0 < threeSliceBase theta gamma K1 p1 r eps := by
      unfold threeSliceBase
      have : 0 < |eps| := abs_pos.mpr he.ne'
      positivity
    exact inv_anti₀ (pow_pos hpos _)
      (pow_le_pow_left₀ hpos.le (threeSliceBase_mono theta gamma ht hg K1 p1 eps hrr) _)

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
  classical
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
  classical
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
end LeanProofs.GowersSzemeredi
