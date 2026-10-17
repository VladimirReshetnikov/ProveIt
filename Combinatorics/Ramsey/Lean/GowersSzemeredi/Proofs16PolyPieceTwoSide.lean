import GowersSzemeredi.Proofs16PolyPieceTwo
import GowersSzemeredi.Proofs16PieceCoverWithRemainderSide
import GowersSzemeredi.Proofs16SinglePieceGlobalSide

/-! Declarations of `Proofs16PolyPieceTwo` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- **One polynomial piece in dimension two.** -/
theorem section16_poly_piece_two
    {A Bq : Nat → Real} (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q)
    (hlemma6 : AllScaleLemma166WidthAt 1 (section16PowerWidth A Bq))
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime]
    (B : Finset (Point N 2)) (phi : Point N 2 → ZMod N)
    (hBarr : section16ThetaOne theta gamma 1 * (N : Real) ^ (17 * 1 + 15) ≤
        generalArrangementCount 8 B ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
        respectedGeneralArrangementCount 8 B phi)
    (hprodB : HasProductProperty B phi gamma) :
    ∃ (x0 : Point N 1) (D : Finset (Point N 2)),
      (∀ z ∈ D, appendCoordinate (section16Init z + x0) (section16Last z) ∈ B) ∧
      5 * polyPieceBudget theta gamma * (N : Real) ^ 2 ≤ D.card ∧
      MultiplyLinearWith (polyPieceTwoCount theta gamma) (polyPieceTwoExponent A Bq theta gamma)
        (partialGraph D (section16PhiOne phi x0)) := by
  obtain ⟨hθ₁pos, _, hδpos, hδle⟩ := section16_theta_delta_bounds 1 ht ht1 hg hg1
  obtain ⟨hθ₂pos, hθ₂le⟩ := section16ThetaTwo_pos_le 1 ht ht1 hg hg1
  have hθ'pos : 0 < polyPieceBudget theta gamma := by
    unfold polyPieceBudget; positivity
  have hθ'le : polyPieceBudget theta gamma ≤ 1 := by
    unfold polyPieceBudget; linarith
  set θ' := polyPieceBudget theta gamma with hθ'def
  have hθ₂eq : section16ThetaTwo (section16ThetaOne theta gamma 1) = 8 * θ' := by
    rw [hθ'def, polyPieceBudget]; ring
  set δ := section16Delta (section16ThetaOne theta gamma 1)
  have hq0 : 0 < polyPieceSpecCount theta gamma := section16BaseFamilyBound_pos _ _
  have hqg : 0 < polyPieceFaceCount theta gamma := section16BaseFamilyBound_pos _ _
  -- 1. Lemmas 16.5 and 16.7
  obtain ⟨H, Y, phiPrime, hH, hcube, hselected, hselection⟩ :=
    section16_dense_induced_selection_of_arrangements (Fact.out : N.Prime) theta gamma B phi
      ht ht1 hg hg1 hBarr
  have hmass : section16ThetaOne theta gamma 1 / 8 * (N : Real) ^ 1 ≤ H.card := by
    refine le_trans ?_ hH
    have : (0 : Real) ≤ (N : Real) ^ 1 := by positivity
    nlinarith
  obtain ⟨x0, hgood, hidentity⟩ := lemma_16_7_holds N 1 theta gamma B phi H Y phiPrime
    hmass hcube hselected hselection
  have hid : Section16PhiOneIdentity (section16GoodDomain B H Y x0) phi x0 phiPrime :=
    section16_phi_one_identity_of_common_base B phi H Y x0 phiPrime hidentity
  set B1 := section16GoodDomain B H Y x0 with hB1def
  have hB1card : section16ThetaTwo (section16ThetaOne theta gamma 1) * (N : Real) ^ (1 + 1) ≤
      B1.card := by
    rw [hB1def, section16GoodDomain_card]; exact hgood
  -- 2. the spectrum cover
  obtain ⟨JΔ, hJΔ, hMLΔ⟩ := polyCoverAt_one N δ θ' hδpos hδle hθ'pos hθ'le
    (section16SpectrumRelation B δ) (section16_spectrum_relation_card B hδpos)
    (section16_spectrum_relation_product B hδpos)
  -- 3. the remainder cover
  have hEface : ∀ s, 0 < s → s ≤ 1 →
      0 < cubicBaseExponent (section16BaseFamilyBound gamma θ') s ∧
        cubicBaseExponent (section16BaseFamilyBound gamma θ') s ≤ 1 := fun s hs hs1 =>
    ⟨cubicBaseExponent_pos (section16BaseFamilyBound_pos _ _) hs,
      cubicBaseExponent_le_one (section16BaseFamilyBound_pos _ _) hs hs1⟩
  obtain ⟨Jr, hJr, hMLr⟩ := remainder_multiplyLinearWith_one_of_polyCover polyCoverAt_one
    hg hg1 hθ'pos hθ'le hEface hprodB x0
  -- 4. the slice families
  obtain ⟨C, hCsub, hCcard, hfam⟩ :=
    section16_final_freiman_families_of_product hg hg1 hθ'pos hθ'le B phi hprodB
  set Bs := B.filter fun z => section16Init z ∈ C (section16Last z) with hBsdef
  -- 5. the common domain
  set t := appendCoordinate x0 0 with htdef
  set F := coordinateSubsetFace (section16VertexDirections (fun _ : Fin 1 => false)) t with hFdef
  set DomR := Finset.univ.filter fun z : Point N 2 =>
    selectedCoordinates F.free (z + t) ∈ F.domain B ∩ Jr with hDomRdef
  set D := (section16GoodDomain B (H ∩ JΔ) Y x0).filter fun z =>
    z ∈ DomR ∧ appendCoordinate (section16Init z + x0) (section16Last z) ∈ Bs with hDdef
  have hDgood : D ⊆ section16GoodDomain B (H ∩ JΔ) Y x0 := Finset.filter_subset _ _
  have hDR : D ⊆ DomR := fun z hz => (Finset.mem_filter.mp hz).2.1
  have hDBs : ∀ z ∈ D, appendCoordinate (section16Init z + x0) (section16Last z) ∈ Bs :=
    fun z hz => (Finset.mem_filter.mp hz).2.2
  have hDB : ∀ z ∈ D, appendCoordinate (section16Init z + x0) (section16Last z) ∈ B :=
    fun z hz => (Finset.mem_filter.mp (hDBs z hz)).1
  -- 6. the three deletions are sparse
  set X1 := Finset.univ.filter fun z : Point N 2 => section16Init z ∉ JΔ with hX1
  set X2 := Finset.univ.filter fun z : Point N 2 =>
    selectedCoordinates F.free (z + t) ∉ Jr with hX2
  set X3 := Finset.univ.filter fun z : Point N 2 =>
    appendCoordinate (section16Init z + x0) (section16Last z) ∈ B ∧
      section16Init z + x0 ∉ C (section16Last z) with hX3
  have hX1card : (X1.card : Real) ≤ θ' * (N : Real) ^ 2 := by
    have h := card_filter_selected_not_mem_le (n := 2) (l := 1)
      ⟨Fin.castSucc, Fin.castSucc_injective 1⟩ 0 JΔ (by simpa using hJΔ) (by omega)
    have hfun : ∀ z : Point N 2,
        (fun i => z ((⟨Fin.castSucc, Fin.castSucc_injective 1⟩ : Fin 1 ↪ Fin 2) i) +
          (0 : Point N 1) i) = section16Init z := fun z => by
      funext i; simp [section16Init]
    simp only [hfun] at h
    exact h
  have hX2card : (X2.card : Real) ≤ θ' * (N : Real) ^ 2 := by
    have hl : (section16VertexDirections (fun _ : Fin 1 => false)).card ≤ 2 := by
      rw [section16VertexDirections_false_card_one]; omega
    exact card_filter_selected_not_mem_le F.free (fun i => t (F.free i)) Jr hJr hl
  have hX3card : (X3.card : Real) ≤ θ' * (N : Real) ^ 2 :=
    card_translated_slice_bad_le B C hCsub hCcard x0
  -- 7. the good domain minus the deletions lies in D
  have hcover : B1 ⊆ D ∪ X1 ∪ X2 ∪ X3 := by
    intro z hz
    by_cases h1 : section16Init z ∈ JΔ
    · by_cases h2 : selectedCoordinates F.free (z + t) ∈ Jr
      · by_cases h3 : section16Init z + x0 ∈ C (section16Last z)
        · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
          have hzG : z ∈ section16GoodDomain B (H ∩ JΔ) Y x0 := by
            rw [section16GoodDomain_inter]
            exact Finset.mem_filter.mpr ⟨hz, h1⟩
          have hmap : F.map (selectedCoordinates F.free (z + t)) =
              appendCoordinate (fun i => x0 i + if (fun _ : Fin 1 => false) i then
                section16Init z i else 0) (section16Last z) := by
            rw [← section16_vertex_coordinate_mask x0 (fun _ : Fin 1 => false) z]
            funext j
            exact coordinateSubsetFace_retraction _ t (z + t) j
          have hzR : z ∈ DomR := by
            simp only [hDomRdef, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_inter, CoordinateFace.mem_domain]
            refine ⟨?_, h2⟩
            rw [hmap]
            exact section16GoodDomain_vertex_mem B H Y x0 hz (fun _ => false)
          have hzB : appendCoordinate (section16Init z + x0) (section16Last z) ∈ B := by
            have h := section16GoodDomain_vertex_mem B H Y x0 hz (fun _ => true)
            simp only [if_true] at h
            have hcomm : (fun i => x0 i + section16Init z i) = section16Init z + x0 := by
              funext i; simp [add_comm]
            rw [hcomm] at h
            exact h
          have hzBs : appendCoordinate (section16Init z + x0) (section16Last z) ∈ Bs := by
            refine Finset.mem_filter.mpr ⟨hzB, ?_⟩
            simpa only [section16Init_appendCoordinate, section16Last_appendCoordinate] using h3
          exact Finset.mem_filter.mpr ⟨hzG, hzR, hzBs⟩
        · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, h3⟩)
          have h := section16GoodDomain_vertex_mem B H Y x0 hz (fun _ => true)
          simp only [if_true] at h
          have hcomm : (fun i => x0 i + section16Init z i) = section16Init z + x0 := by
            funext i; simp [add_comm]
          rw [hcomm] at h
          exact h
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)))
  have hDcard : 5 * θ' * (N : Real) ^ 2 ≤ D.card := by
    have hc := Finset.card_le_card hcover
    have hu1 := Finset.card_union_le (D ∪ X1 ∪ X2) X3
    have hu2 := Finset.card_union_le (D ∪ X1) X2
    have hu3 := Finset.card_union_le D X1
    have h' : (B1.card : Real) ≤ (D.card : Real) + (X1.card : Real) + (X2.card : Real) +
        (X3.card : Real) := by
      have h := (hc.trans hu1).trans (Nat.add_le_add_right (hu2.trans
        (Nat.add_le_add_right hu3 _)) _)
      exact_mod_cast h
    rw [hθ₂eq] at hB1card
    norm_num at hB1card
    nlinarith
  -- 8. the piece cover
  have hQb : ∀ s, 0 < s → s ≤ 1 → 0 ≤ polyPieceTwoQb theta gamma s ∧
      0 < polyPieceTwoEb theta gamma s ∧ polyPieceTwoEb theta gamma s ≤ 1 := by
    intro s hs hs1
    exact ⟨Nat.cast_nonneg _, cubicBaseExponent_pos hq0 hs, cubicBaseExponent_le_one hq0 hs hs1⟩
  have hEr : ∀ s, 0 < s → s ≤ 1 → 0 < polyPieceTwoEr theta gamma s := by
    intro s hs _
    have := cubicBaseExponent_pos hqg hs
    unfold polyPieceTwoEr
    positivity
  have hMLΔ' : MultiplyLinearWith (polyPieceTwoQb theta gamma) (polyPieceTwoEb theta gamma)
      (restrictRelation (section16SpectrumRelation B
        (section16Delta (section16ThetaOne theta gamma 1))) JΔ) := hMLΔ
  have hrem : MultiplyLinearWith (polyPieceTwoQr theta gamma) (polyPieceTwoEr theta gamma)
      (partialGraph D (section16PhiRemainder phi x0)) :=
    MultiplyLinearWith.congr_graph hMLr hDR (fun _ _ => rfl)
  have hslice : Section16SliceProvider D (section16PhiOne phi x0)
      (polyPieceTwoPb theta gamma) (polyPieceTwoEs theta gamma) :=
    (Section16FinalFreimanFamilies.of_translate hfam x0 D hDBs).cubic_slice_provider hqg
  have hcover' := section16_piece_cover_with (k := 1) le_rfl hA hB hlemma6 ht ht1 hg hg1
    hQb hEr (H := H) (Jbase := JΔ) (H1 := H ∩ JΔ) (Y := Y) (phiPrime := phiPrime) (x0 := x0)
    rfl hMLΔ' hselection
    (hid.mono (fun z hz => by
      rw [section16GoodDomain_inter] at hz
      exact (Finset.mem_filter.mp hz).1))
    hDgood hrem hslice (section16_cubic_slice_provider_ranges hqg)
    (fun _ => cubicSlice_count_monotone _)
    (fun _ heps => cubicSlice_exponent_antitone hqg heps)
  exact ⟨x0, D, hDB, hDcard, hcover'⟩

/-- **A dense piece of `B` on which `φ` itself is polynomially multiply
linear.** This is the extraction step of Theorem 16.2's loop in dimension
two: translating the piece cover of `φ₁` back by `(x₀, 0)`. -/
theorem section16_poly_piece_two_original
    {A Bq : Nat → Real} (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q)
    (hlemma6 : AllScaleLemma166WidthAt 1 (section16PowerWidth A Bq))
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime]
    (B : Finset (Point N 2)) (phi : Point N 2 → ZMod N)
    (hBarr : section16ThetaOne theta gamma 1 * (N : Real) ^ (17 * 1 + 15) ≤
        generalArrangementCount 8 B ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
        respectedGeneralArrangementCount 8 B phi)
    (hprodB : HasProductProperty B phi gamma) :
    ∃ D' : Finset (Point N 2), D' ⊆ B ∧
      5 * polyPieceBudget theta gamma * (N : Real) ^ 2 ≤ D'.card ∧
      MultiplyLinearWith (polyPieceTwoCount theta gamma) (polyPieceTwoExponent A Bq theta gamma)
        (partialGraph D' phi) := by
  obtain ⟨x0, D, hDB, hDcard, hML⟩ :=
    section16_poly_piece_two hA hB hlemma6 ht ht1 hg hg1 B phi hBarr hprodB
  set t := appendCoordinate x0 0 with htdef
  have hfun : section16PhiOne phi x0 = fun z => phi (z + t) := by
    funext z
    simp only [section16PhiOne]
    have hc : (fun i => x0 i + section16Init z i) = section16Init z + x0 := by
      funext i; simp [add_comm]
    rw [hc, appendCoordinate_init_add]
  rw [hfun] at hML
  have h2 := MultiplyLinearWith.translate_graph hML (-t)
  refine ⟨Finset.univ.filter fun w => w + -t ∈ D, ?_, ?_, ?_⟩
  · intro w hw
    have hw' := hDB _ (Finset.mem_filter.mp hw).2
    rw [appendCoordinate_init_add] at hw'
    simpa [htdef] using hw'
  · have hinj : (Finset.univ.filter fun w : Point N 2 => w + -t ∈ D) = D.image (· + t) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hw
        exact ⟨w + -t, hw, by simp⟩
      · rintro ⟨z, hz, rfl⟩
        simpa using hz
    rw [hinj, Finset.card_image_of_injective _ (add_left_injective t)]
    exact hDcard
  · refine MultiplyLinearWith.congr_graph h2 Finset.Subset.rfl ?_
    intro w _
    simp

end LeanProofs.GowersSzemeredi
