import GowersSzemeredi.Proofs16PolyPieceThreeInputs

/-! **One three-dimensional piece with its data** (Notes L.5, D3).

`section16_poly_piece_three_data`: let `(B, φ)` be a three-dimensional
partial function inside a relation `Γ`. Assume it meets Lemma 16.4's
arrangement conditions at `k = 2` and has the product property. Then there is
a `PolyPieceThreeData` of `Γ` of mass `3θ′`, where `θ′ = θ₂/8`
(`threeBudget`). This is the dimension-two construction
(`section16_poly_piece_two_data`) one level up:
* Lemmas 16.5 and 16.7 give the dense selection, the base point `x₀` and
  the identity `φ₁ = φ′ + φ″` on the good domain `B₁` (`|B₁| ≥ 8θ′N³`).
* The spectrum relation, translated by `x₀`, is a two-dimensional product
  relation (`RelationProductProperty.translate`). It decomposes into pieces
  of the uniform class at `(θ′, δ)` off a good set `J_T`.
* The remainder is `g₁(dropMid w) + g₂(dropFirst w) − g₃(lastPt3 w)` with
  the face functions of `midFace3`, `firstFace3`, `lastFace3`. The first two
  face graphs decompose into pieces at `(θ′, γ)` off `J₁`, `J₂`. The third
  has Freiman families off `J₃`.
* The slices decompose into pieces at `(θ′, γ)` off `C t`
  (`section16_slice_decomposition_three`).
* Five deletions of at most `θ′N³` points each leave `3θ′N³`.

All the data is then rebuilt in the original frame `w = origPt x₀ z`. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-- The deletion budget of a three-dimensional piece: `θ₂/8`. -/
def threeBudget (theta gamma : Real) : Real :=
  section16ThetaTwo (section16ThetaOne theta gamma 2) / 8

/-- The spectrum parameter `δ(θ₁)` at `k = 2`. -/
def threeDelta (theta gamma : Real) : Real := section16Delta (section16ThetaOne theta gamma 2)

/-- The Freiman count of the last-coordinate face. -/
def threeFaceCount (theta gamma : Real) : Nat :=
  section16BaseFamilyBound gamma (threeBudget theta gamma)

/-- The modulus threshold of a three-dimensional piece. -/
def threeThreshold (theta gamma : Real) : Real :=
  max (polyTwoThreshold (threeBudget theta gamma) (threeDelta theta gamma))
    (polyTwoThreshold (threeBudget theta gamma) gamma)

theorem origPt_eq_add {N : Nat} (x0 : Point N 2) (z : Point N 3) :
    origPt x0 z = z + appendCoordinate x0 0 := by
  unfold origPt
  conv_rhs => rw [← appendCoordinate_init_last z]
  rw [appendCoordinate_add, add_zero]

theorem origPt_injective {N : Nat} (x0 : Point N 2) : Function.Injective (origPt x0) := by
  intro z z' h
  rw [origPt_eq_add, origPt_eq_add] at h
  exact add_right_cancel h

theorem phiOne_eq_origPt {N : Nat} (phi : Point N 3 → ZMod N) (x0 : Point N 2) (z : Point N 3) :
    section16PhiOne phi x0 z = phi (origPt x0 z) := by
  unfold section16PhiOne origPt
  congr 2
  funext i
  simp [add_comm]

theorem card_point_le_pow {N : Nat} [NeZero N] (k : Nat) (S : Finset (Point N k)) :
    (S.card : Real) ≤ (N : Real) ^ k := by
  have h := Finset.card_le_univ S
  have hc : Fintype.card (Point N k) = N ^ k := by
    simp [Point, ZMod.card]
  rw [hc] at h
  exact_mod_cast h

theorem one_le_gamma_inv_sq {gamma : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    (1 : Real) ≤ gamma ^ (-(2 : Int)) := by
  rw [zpow_neg, zpow_ofNat]
  exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)

/-- **A three-dimensional piece with its data, in the original frame.** -/
theorem section16_poly_piece_three_data
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] (hN : threeThreshold theta gamma ≤ N)
    (Gamma : Finset (Point N 3 × ZMod N))
    (B : Finset (Point N 3)) (phi : Point N 3 → ZMod N)
    (hBG : partialGraph B phi ⊆ Gamma)
    (hBarr : section16ThetaOne theta gamma 2 * (N : Real) ^ (17 * 2 + 15) ≤
        generalArrangementCount 8 B ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
        respectedGeneralArrangementCount 8 B phi)
    (hprodB : HasProductProperty B phi gamma) :
    Nonempty (PolyPieceThreeData Gamma (section16Zeta theta gamma 2)
      (3 * threeBudget theta gamma) (threeBudget theta gamma) (threeDelta theta gamma)
      (threeBudget theta gamma) gamma (threeFaceCount theta gamma)) := by
  obtain ⟨hθ₁pos, _, hδpos, hδle⟩ := section16_theta_delta_bounds 2 ht ht1 hg hg1
  obtain ⟨hθ₂pos, hθ₂le⟩ := section16ThetaTwo_pos_le 2 ht ht1 hg hg1
  have hθ'pos : 0 < threeBudget theta gamma := by unfold threeBudget; positivity
  have hθ'le : threeBudget theta gamma ≤ 1 := by unfold threeBudget; linarith
  set θ' := threeBudget theta gamma with hθ'def
  have hθ₂eq : section16ThetaTwo (section16ThetaOne theta gamma 2) = 8 * θ' := by
    rw [hθ'def, threeBudget]; ring
  set δ := threeDelta theta gamma with hδdef
  have hδeq : section16Delta (section16ThetaOne theta gamma 2) = δ := rfl
  rw [hδeq] at hδpos hδle
  have hN1 : polyTwoThreshold θ' δ ≤ N := (le_max_left _ _).trans hN
  have hN2 : polyTwoThreshold θ' gamma ≤ N := (le_max_right _ _).trans hN
  -- 1. Lemmas 16.5 and 16.7
  obtain ⟨H, Y, phiPrime, hH, hcube, hselected, hselection⟩ :=
    section16_dense_induced_selection_of_arrangements (k := 2) (Fact.out : N.Prime) theta gamma
      B phi ht ht1 hg hg1 hBarr
  have hmass : section16ThetaOne theta gamma 2 / 8 * (N : Real) ^ 2 ≤ H.card := by
    refine le_trans ?_ hH
    have : (0 : Real) ≤ (N : Real) ^ 2 := by positivity
    nlinarith
  obtain ⟨x0, hgood, hidentity⟩ := lemma_16_7_holds N 2 theta gamma B phi H Y phiPrime
    hmass hcube hselected hselection
  have hid : Section16PhiOneIdentity (section16GoodDomain B H Y x0) phi x0 phiPrime :=
    section16_phi_one_identity_of_common_base B phi H Y x0 phiPrime hidentity
  set B1 := section16GoodDomain B H Y x0 with hB1def
  have hB1card : section16ThetaTwo (section16ThetaOne theta gamma 2) * (N : Real) ^ (2 + 1) ≤
      B1.card := by
    rw [hB1def, section16GoodDomain_card]; exact hgood
  -- 2. the spectrum, translated to the original frame
  set T := (section16SpectrumRelation B δ).image fun z => (z.1 + x0, z.2) with hTdef
  have hsizeT : (T.card : Real) ≤ δ ^ (-(2 : Int)) * (N : Real) ^ 2 := by
    have hc : (T.card : Real) ≤ (section16SpectrumRelation B δ).card := by
      exact_mod_cast Finset.card_image_le
    exact hc.trans (section16_spectrum_relation_card B hδpos)
  obtain ⟨JT, hJT, Pspec, hPspec⟩ := section16_poly_piece_decomposition_two hθ'pos hθ'le
    hδpos hδle hN1 T hsizeT ((section16_spectrum_relation_product B hδpos).translate x0)
  -- 3. the faces
  set F1 := midFace3 (N := N) x0
  set F2 := firstFace3 (N := N) x0
  set F3 := lastFace3 (N := N) x0
  have hsizeF : ∀ (F : CoordinateFace N 3 2), ((partialGraph (F.domain B) (F.pullback phi)).card : Real) ≤
      gamma ^ (-(2 : Int)) * (N : Real) ^ 2 := by
    intro F
    rw [partialGraph_card]
    exact (card_point_le_pow 2 _).trans (le_mul_of_one_le_left (by positivity)
      (one_le_gamma_inv_sq hg hg1))
  obtain ⟨J1, hJ1, P1, hP1⟩ := section16_poly_piece_decomposition_two hθ'pos hθ'le hg hg1 hN2
    _ (hsizeF F1) (partialGraph_relationProductProperty (hprodB.coordinateFace F1))
  obtain ⟨J2, hJ2, P2, hP2⟩ := section16_poly_piece_decomposition_two hθ'pos hθ'le hg hg1 hN2
    _ (hsizeF F2) (partialGraph_relationProductProperty (hprodB.coordinateFace F2))
  have hsize3 : ((partialGraph (F3.domain B) (F3.pullback phi)).card : Real) ≤
      gamma ^ (-(2 : Int)) * N := by
    rw [partialGraph_card]
    have h := card_point_le_pow 1 (F3.domain B)
    rw [pow_one] at h
    exact h.trans (le_mul_of_one_le_left (by positivity) (one_le_gamma_inv_sq hg hg1))
  obtain ⟨J3, D3, f3, hJ3, hf3, hc3⟩ := section16_extract_uniform_base_family hg hg1
    hθ'pos hθ'le (partialGraph (F3.domain B) (F3.pullback phi)) hsize3
    (partialGraph_relationProductProperty (hprodB.coordinateFace F3))
  -- 4. the slices
  obtain ⟨C, hCsub, hCcard, Pslice, hPslice⟩ :=
    section16_slice_decomposition_three hθ'pos hθ'le hg hg1 hN2 B phi hprodB
  -- 5. the domain in the shifted frame
  set D := B1.filter fun z => section16Init (origPt x0 z) ∈ JT ∧ dropMid (origPt x0 z) ∈ J1 ∧
    dropFirst (origPt x0 z) ∈ J2 ∧ lastPt3 (origPt x0 z) ∈ J3 ∧
    section16Init z + x0 ∈ C (section16Last z) with hDdef
  set X1 := Finset.univ.filter fun z : Point N 3 => section16Init (origPt x0 z) ∉ JT
  set X2 := Finset.univ.filter fun z : Point N 3 => dropMid (origPt x0 z) ∉ J1
  set X3 := Finset.univ.filter fun z : Point N 3 => dropFirst (origPt x0 z) ∉ J2
  set X4 := Finset.univ.filter fun z : Point N 3 => lastPt3 (origPt x0 z) ∉ J3
  set X5 := Finset.univ.filter fun z : Point N 3 =>
    appendCoordinate (section16Init z + x0) (section16Last z) ∈ B ∧
      section16Init z + x0 ∉ C (section16Last z)
  have hX1 : (X1.card : Real) ≤ θ' * (N : Real) ^ 3 := card_init_bad_le x0 JT hJT
  have hX2 : (X2.card : Real) ≤ θ' * (N : Real) ^ 3 := card_dropMid_bad_le x0 J1 hJ1
  have hX3 : (X3.card : Real) ≤ θ' * (N : Real) ^ 3 := card_dropFirst_bad_le x0 J2 hJ2
  have hX4 : (X4.card : Real) ≤ θ' * (N : Real) ^ 3 := card_lastPt3_bad_le x0 J3 (by simpa using hJ3)
  have hX5 : (X5.card : Real) ≤ θ' * (N : Real) ^ 3 :=
    card_translated_slice_bad_le_succ (k := 2) B C hCsub hCcard x0
  have hvert_true : ∀ z ∈ B1, origPt x0 z ∈ B := by
    intro z hz
    have h := section16GoodDomain_vertex_mem B H Y x0 hz (fun _ => true)
    simp only [if_true] at h
    have hcomm : (fun i => x0 i + section16Init z i) = section16Init z + x0 := by
      funext i; simp [add_comm]
    rw [hcomm] at h
    exact h
  have hcover : B1 ⊆ D ∪ X1 ∪ X2 ∪ X3 ∪ X4 ∪ X5 := by
    intro z hz
    have mk : ∀ {P : Point N 3 → Prop} [DecidablePred P], P z →
        z ∈ (Finset.univ : Finset (Point N 3)).filter P :=
      fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    by_cases h1 : section16Init (origPt x0 z) ∈ JT
    · by_cases h2 : dropMid (origPt x0 z) ∈ J1
      · by_cases h3 : dropFirst (origPt x0 z) ∈ J2
        · by_cases h4 : lastPt3 (origPt x0 z) ∈ J3
          · by_cases h5 : section16Init z + x0 ∈ C (section16Last z)
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_filter.mpr ⟨hz, h1, h2, h3, h4, h5⟩)))))
            · exact Finset.mem_union_right _ (mk ⟨hvert_true z hz, h5⟩)
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (mk h4))
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (mk h3)))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (mk h2))))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_right _ (mk h1)))))
  have hDcard : 3 * θ' * (N : Real) ^ 3 ≤ D.card := by
    have hc := Finset.card_le_card hcover
    have hu1 := Finset.card_union_le (D ∪ X1 ∪ X2 ∪ X3 ∪ X4) X5
    have hu2 := Finset.card_union_le (D ∪ X1 ∪ X2 ∪ X3) X4
    have hu3 := Finset.card_union_le (D ∪ X1 ∪ X2) X3
    have hu4 := Finset.card_union_le (D ∪ X1) X2
    have hu5 := Finset.card_union_le D X1
    have h' : (B1.card : Real) ≤ (D.card : Real) + X1.card + X2.card + X3.card + X4.card +
        X5.card := by
      have h := (hc.trans hu1).trans (Nat.add_le_add_right (hu2.trans (Nat.add_le_add_right
        (hu3.trans (Nat.add_le_add_right (hu4.trans (Nat.add_le_add_right hu5 _)) _)) _)) _)
      exact_mod_cast h
    rw [hθ₂eq] at hB1card
    norm_num at hB1card
    nlinarith
  -- 6. the original frame
  set D' := D.image (origPt x0)
  have hD'card : D'.card = D.card := Finset.card_image_of_injective _ (origPt_injective x0)
  have hDmem : ∀ z ∈ D, z ∈ B1 ∧ section16Init (origPt x0 z) ∈ JT ∧ dropMid (origPt x0 z) ∈ J1 ∧
      dropFirst (origPt x0 z) ∈ J2 ∧ lastPt3 (origPt x0 z) ∈ J3 ∧
      section16Init z + x0 ∈ C (section16Last z) := fun z hz => Finset.mem_filter.mp hz
  let H1' := (H.filter fun h => h + x0 ∈ JT).image fun h => h + x0
  let K' : Point N 2 → Finset (ZMod N) := fun x => section16LargeSpectrum B (x - x0) δ
  let A' : Point N 2 → Finset (ZMod N) := fun x =>
    Finset.univ.filter fun y => (x - x0, y) ∈ section16InducedDomain B H Y
  let f' : Point N 2 → ZMod N → ZMod N := fun x y => phiPrime (x - x0) y
  let rem' : Point N 3 → ZMod N := fun w =>
    F1.pullback phi (dropMid w) + F2.pullback phi (dropFirst w) - F3.pullback phi (lastPt3 w)
  have hHsub : H ⊆ H := le_rfl
  refine ⟨{
    D := D'
    phi := phi
    graph_sub := ?_
    card_ge := ?_
    H1 := H1'
    K := K'
    A := A'
    f := f'
    rem := rem'
    linear := ?_
    dom := ?_
    ident := ?_
    spec := Pspec
    spec_sub := ?_
    g1 := F1.pullback phi
    g2 := F2.pullback phi
    g3 := F3.pullback phi
    rem_eq := fun _ _ => rfl
    P1 := P1
    P2 := P2
    rel1 := ?_
    rel2 := ?_
    rel3 := ?_
    slices := Pslice
    slices_sub := ?_ }⟩
  · -- graph inside Gamma
    intro p hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    exact hBG (Finset.mem_image.mpr ⟨origPt x0 z, hvert_true z (hDmem z hz).1, rfl⟩)
  · rw [hD'card]; exact hDcard
  · -- Bohr linearity
    intro x hx v hv J hJ hd
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hx
    have hhH : h ∈ H := (Finset.mem_filter.mp hh).1
    have hsh : h + x0 - x0 = h := add_sub_cancel_right h x0
    have hd' : J.step ∈ bohr (section16LargeSpectrum B h δ) (section16Zeta theta gamma 2 / v) := by
      simpa only [K', hsh] using hd
    have hlin := hselection.2 h hhH v hv J.step hd' J rfl hJ
    simpa only [A', f', hsh, Finset.inter_filter, Finset.inter_univ] using hlin
  · -- domains
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hzB1, hzT, -, -, -, -⟩ := hDmem z hz
    have hzG' : appendCoordinate (section16Init z) (section16Last z) ∈
        section16GoodDomain B H Y x0 := by
      rw [appendCoordinate_init_last]; exact hzB1
    obtain ⟨hhH1, hdom⟩ := section16GoodDomain_fibre_mem B H H Y x0
      (section16Init z) (section16Last z) hHsub hzG'
    rw [origPt_init, origPt_last]
    rw [origPt_init] at hzT
    refine ⟨Finset.mem_image.mpr ⟨section16Init z, Finset.mem_filter.mpr ⟨hhH1, hzT⟩, rfl⟩, ?_⟩
    simp only [A', Finset.mem_filter, Finset.mem_univ, true_and, add_sub_cancel_right]
    exact hdom
  · -- the identity
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hzB1, -, -, -, -, -⟩ := hDmem z hz
    have hidz := hid z hzB1
    rw [section16PhiRemainder_two, phiOne_eq_origPt] at hidz
    obtain ⟨e1, e2, e3⟩ := translatedVertex_two_faces phi x0 z
    rw [e1, e2, e3] at hidz
    simp only [section16PhiPrimeLift] at hidz
    simp only [f', rem', origPt_init, origPt_last, add_sub_cancel_right]
    rw [hidz]
  · -- the spectrum
    intro p hp
    apply hPspec
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    obtain ⟨hx, -⟩ := Finset.mem_product.mp hp1
    obtain ⟨h, hh, hx'⟩ := Finset.mem_image.mp hx
    obtain ⟨_, hhT⟩ := Finset.mem_filter.mp hh
    unfold restrictRelation
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(h, p.2), ?_, ?_⟩, ?_⟩
    · have hr : p.2 ∈ section16LargeSpectrum B h δ := by
        simpa only [K', ← hx', add_sub_cancel_right] using hp2
      unfold section16SpectrumRelation
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩
    · rw [hx']
    · rw [← hx']; exact hhT
  · -- the first face
    intro p hp
    apply hP1
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hzB1, -, hz1, -, -, -⟩ := hDmem z hz
    unfold restrictRelation
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨dropMid (origPt x0 z), ?_, rfl⟩, hz1⟩
    rw [CoordinateFace.mem_domain, midFace3_map]
    exact section16GoodDomain_vertex_mem B H Y x0 hzB1 vTF
  · -- the second face
    intro p hp
    apply hP2
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hzB1, -, -, hz2, -, -⟩ := hDmem z hz
    unfold restrictRelation
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨dropFirst (origPt x0 z), ?_, rfl⟩, hz2⟩
    rw [CoordinateFace.mem_domain, firstFace3_map]
    exact section16GoodDomain_vertex_mem B H Y x0 hzB1 vFT
  · -- the last face
    have hR : RelFreimanCover (threeFaceCount theta gamma)
        (restrictRelation (partialGraph (F3.domain B) (F3.pullback phi)) J3) := ⟨D3, f3, hf3, hc3⟩
    refine hR.mono ?_
    intro p hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hzB1, -, -, -, hz3, -⟩ := hDmem z hz
    unfold restrictRelation
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨lastPt3 (origPt x0 z), ?_, rfl⟩, hz3⟩
    rw [CoordinateFace.mem_domain, lastFace3_map]
    exact section16GoodDomain_vertex_mem B H Y x0 hzB1 (fun _ => false)
  · -- the slices
    intro s
    refine Finset.Subset.trans ?_ (hPslice s)
    intro p hp
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_image.mpr ⟨h, ?_, rfl⟩
    unfold section16FinalCoordinateSection at hh
    obtain ⟨-, hhD⟩ := Finset.mem_filter.mp hh
    obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp hhD
    obtain ⟨-, -, -, -, -, hz5⟩ := hDmem z hz
    have hi := congrArg section16Init hzeq
    have hl := congrArg section16Last hzeq
    rw [origPt_init, section16Init_appendCoordinate] at hi
    rw [origPt_last, section16Last_appendCoordinate] at hl
    rw [← hi, ← hl]
    exact hz5

end LeanProofs.GowersSzemeredi
