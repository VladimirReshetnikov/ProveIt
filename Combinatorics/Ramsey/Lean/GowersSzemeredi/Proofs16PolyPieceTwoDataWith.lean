import GowersSzemeredi.Proofs16PolyPieceTwoData
import GowersSzemeredi.Proofs16DenseSelectionWith

/-! **Dimension-two pieces with `(θ₁, ζ)` as parameters** (Notes L.16d).

`section16_poly_piece_two_data` builds the pieces of the uniform
dimension-two cover, the seed of the split-class recursion (Notes L.16c).
Its output, `PolyPieceTwoData Γ ζ mass qs qr ql`, is already generic in the
radius and the counts. Only the producer fixes the printed
`θ₁ = section16ThetaOne θ γ 1` and `ζ = section16Zeta θ γ 1`.

* `polyPieceBudgetW t1 = θ₂(t1)/8`, `polyPieceSpecCountW t1` and
  `polyPieceFaceCountW t1 γ`: the deletion budget and the Freiman-family
  counts as functions of the density `t1`. At the printed `t1` they are
  `polyPieceBudget`, `polyPieceSpecCount` and `polyPieceFaceCount`.
* `section16_theta_delta_bounds_with` and `section16ThetaTwo_pos_le_with`:
  the bounds the proof uses, from `0 < t1/4 ≤ 1/36`.
* `section16_poly_piece_two_data_with`: the producer with `(t1, zeta)`. It
  is generated from the corpus proof by a script with a guard that no
  printed parameter survives, and runs through `Proofs16DenseSelectionWith`. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The deletion budget `θ₂(t1)/8` of a dimension-two piece. -/
def polyPieceBudgetW (t1 : Real) : Real := section16ThetaTwo t1 / 8

/-- The Freiman-family count of the spectrum relation, at density `t1`. -/
def polyPieceSpecCountW (t1 : Real) : Nat :=
  section16BaseFamilyBound (section16Delta t1) (polyPieceBudgetW t1)

/-- The Freiman-family count of the faces and slices, at density `t1`. -/
def polyPieceFaceCountW (t1 gamma : Real) : Nat :=
  section16BaseFamilyBound gamma (polyPieceBudgetW t1)

theorem polyPieceBudgetW_printed (theta gamma : Real) :
    polyPieceBudgetW (section16ThetaOne theta gamma 1) = polyPieceBudget theta gamma := rfl

theorem polyPieceSpecCountW_printed (theta gamma : Real) :
    polyPieceSpecCountW (section16ThetaOne theta gamma 1) = polyPieceSpecCount theta gamma := rfl

theorem polyPieceFaceCountW_printed (theta gamma : Real) :
    polyPieceFaceCountW (section16ThetaOne theta gamma 1) gamma =
      polyPieceFaceCount theta gamma := rfl

theorem section16_theta_delta_bounds_with {t1 : Real} (ha0 : 0 < t1 / 4) (haS : t1 / 4 ≤ 1 / 36) :
    0 < t1 ∧ t1 ≤ 1 ∧ 0 < section16Delta t1 ∧ section16Delta t1 ≤ 1 := by
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · unfold section16Delta
    exact mul_pos (by positivity) (Real.rpow_pos_of_pos ha0 _)
  · unfold section16Delta
    have h1 : (t1 / 4) ^ ((11 : Real) / 2) ≤ 1 :=
      Real.rpow_le_one ha0.le (by linarith) (by norm_num)
    have h2 : (2 : Real) ^ (-(37 : Real)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    calc (2 : Real) ^ (-(37 : Real)) * (t1 / 4) ^ ((11 : Real) / 2) ≤ 1 * 1 :=
          mul_le_mul h2 h1 (Real.rpow_nonneg ha0.le _) (by norm_num)
      _ = 1 := by norm_num

theorem section16ThetaTwo_pos_le_with {t1 : Real} (ha0 : 0 < t1 / 4) (haS : t1 / 4 ≤ 1 / 36) :
    0 < section16ThetaTwo t1 ∧ section16ThetaTwo t1 ≤ 1 := by
  have ht : 0 < t1 := by linarith
  have ht1 : t1 ≤ 1 := by linarith
  unfold section16ThetaTwo
  refine ⟨mul_pos (by positivity) (pow_pos ht 8), ?_⟩
  have h1 : t1 ^ 8 ≤ 1 := pow_le_one₀ ht.le ht1
  have h2 : (2 : Real) ^ (-(32 : Real)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  calc (2 : Real) ^ (-(32 : Real)) * t1 ^ 8 ≤ 1 * 1 :=
        mul_le_mul h2 h1 (pow_nonneg ht.le 8) (by norm_num)
    _ = 1 := by norm_num

/-- **A dimension-two piece with its Freiman data, in the original frame.** -/
theorem section16_poly_piece_two_data_with
    {t1 zeta gamma : Real} (ha0 : 0 < t1 / 4) (haS : t1 / 4 ≤ 1 / 36)
    (hzeta : ∀ alpha : Real, t1 / 4 ≤ alpha → alpha ≤ 1 / 6 → zeta ≤ section10Zeta alpha)
    (hz0 : 0 < zeta) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] (Gamma : Finset (Point N 2 × ZMod N))
    (B : Finset (Point N 2)) (phi : Point N 2 → ZMod N)
    (hBG : partialGraph B phi ⊆ Gamma)
    (hBarr : t1 * (N : Real) ^ (17 * 1 + 15) ≤
        generalArrangementCount 8 B ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
        respectedGeneralArrangementCount 8 B phi)
    (hprodB : HasProductProperty B phi gamma) :
    Nonempty (PolyPieceTwoData Gamma (zeta)
      (5 * polyPieceBudgetW t1) (polyPieceSpecCountW t1)
      (polyPieceFaceCountW t1 gamma) (polyPieceFaceCountW t1 gamma)) := by
  obtain ⟨hθ₁pos, _, hδpos, hδle⟩ := section16_theta_delta_bounds_with ha0 haS
  obtain ⟨hθ₂pos, hθ₂le⟩ := section16ThetaTwo_pos_le_with ha0 haS
  have hθ'pos : 0 < polyPieceBudgetW t1 := by
    unfold polyPieceBudgetW; linarith
  have hθ'le : polyPieceBudgetW t1 ≤ 1 := by
    unfold polyPieceBudgetW; linarith
  set θ' := polyPieceBudgetW t1 with hθ'def
  have hθ₂eq : section16ThetaTwo (t1) = 8 * θ' := by
    rw [hθ'def, polyPieceBudgetW]; ring
  set δ := section16Delta (t1)
  -- 1. Lemmas 16.5 and 16.7
  obtain ⟨H, Y, phiPrime, hH, hcube, hselected, hselection⟩ :=
    section16_dense_induced_selection_with (Fact.out : N.Prime) t1 zeta B phi
      ha0 haS hzeta hz0 hBarr
  have hmass : t1 / 8 * (N : Real) ^ 1 ≤ H.card := by
    refine le_trans ?_ hH
    have : (0 : Real) ≤ (N : Real) ^ 1 := by positivity
    nlinarith
  obtain ⟨x0, hgood, hidentity⟩ := lemma_16_7_with t1 zeta hθ₁pos.le B phi H Y phiPrime
    hmass hcube hselected hselection
  have hid : Section16PhiOneIdentity (section16GoodDomain B H Y x0) phi x0 phiPrime :=
    section16_phi_one_identity_of_common_base B phi H Y x0 phiPrime hidentity
  set B1 := section16GoodDomain B H Y x0 with hB1def
  have hB1card : section16ThetaTwo (t1) * (N : Real) ^ (1 + 1) ≤
      B1.card := by
    rw [hB1def, section16GoodDomain_card]; exact hgood
  -- 2. the spectrum families
  obtain ⟨JΔ, Dsp, fsp, hJΔ, hfsp, hcsp⟩ := section16_extract_uniform_base_family hδpos hδle
    hθ'pos hθ'le (section16SpectrumRelation B δ)
    (by simpa using section16_spectrum_relation_card B hδpos)
    (section16_spectrum_relation_product B hδpos)
  -- 3. the face families
  set F := firstFixedFace (N := N) x0 with hFdef
  set Fdom := F.domain B with hFdomdef
  set g := F.pullback phi with hgdef
  have hsizeF : ((partialGraph Fdom g).card : Real) ≤ gamma ^ (-(2 : Int)) * N := by
    rw [partialGraph_card]
    have hle : (Fdom.card : Real) ≤ N := by
      exact_mod_cast (show Fdom.card ≤ N by
        simpa [Point, ZMod.card] using Finset.card_le_univ Fdom)
    have hginv : 1 ≤ gamma ^ (-(2 : Int)) := by
      rw [zpow_neg, zpow_ofNat]
      exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
    exact hle.trans (le_mul_of_one_le_left (by positivity) hginv)
  obtain ⟨Jr, Dr, fr, hJr, hfr, hcr⟩ := section16_extract_uniform_base_family hg hg1
    hθ'pos hθ'le (partialGraph Fdom g) hsizeF
    (partialGraph_relationProductProperty (hprodB.coordinateFace F))
  -- 4. the slice families
  obtain ⟨C, hCsub, hCcard, hfam⟩ :=
    section16_final_freiman_families_of_product hg hg1 hθ'pos hθ'le B phi hprodB
  set Bs := B.filter fun z => section16Init z ∈ C (section16Last z) with hBsdef
  -- 5. the domain in the shifted frame
  set t : Point N 2 := appendCoordinate x0 0 with htdef
  set D := (section16GoodDomain B (H ∩ JΔ) Y x0).filter fun z =>
    lastPt z ∈ Fdom ∩ Jr ∧ appendCoordinate (section16Init z + x0) (section16Last z) ∈ Bs
    with hDdef
  have hDgood : D ⊆ section16GoodDomain B (H ∩ JΔ) Y x0 := Finset.filter_subset _ _
  -- 6. the three deletions are sparse
  set X1 := Finset.univ.filter fun z : Point N 2 => section16Init z ∉ JΔ with hX1
  set X2 := Finset.univ.filter fun z : Point N 2 => lastPt z ∉ Jr with hX2
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
    have h := card_filter_selected_not_mem_le (n := 2) (l := 1)
      ⟨fun _ => Fin.last 1, fun a b _ => Subsingleton.elim a b⟩ 0 Jr (by simpa using hJr)
      (by omega)
    have hfun : ∀ z : Point N 2,
        (fun i => z ((⟨fun _ => Fin.last 1, fun a b _ => Subsingleton.elim a b⟩ :
          Fin 1 ↪ Fin 2) i) + (0 : Point N 1) i) = lastPt z := fun z => by
      funext i; simp [lastPt, section16Last]
    simp only [hfun] at h
    exact h
  have hX3card : (X3.card : Real) ≤ θ' * (N : Real) ^ 2 :=
    card_translated_slice_bad_le B C hCsub hCcard x0
  have hvert_true : ∀ z ∈ B1, appendCoordinate (section16Init z + x0) (section16Last z) ∈ B := by
    intro z hz
    have h := section16GoodDomain_vertex_mem B H Y x0 hz (fun _ => true)
    simp only [if_true] at h
    have hcomm : (fun i => x0 i + section16Init z i) = section16Init z + x0 := by
      funext i; simp [add_comm]
    rw [hcomm] at h
    exact h
  have hvert_false : ∀ z ∈ B1, lastPt z ∈ Fdom := by
    intro z hz
    have h := section16GoodDomain_vertex_mem B H Y x0 hz (fun _ => false)
    simp only [Bool.false_eq_true, if_false, add_zero] at h
    rw [hFdomdef, CoordinateFace.mem_domain]
    exact h
  have hcover : B1 ⊆ D ∪ X1 ∪ X2 ∪ X3 := by
    intro z hz
    by_cases h1 : section16Init z ∈ JΔ
    · by_cases h2 : lastPt z ∈ Jr
      · by_cases h3 : section16Init z + x0 ∈ C (section16Last z)
        · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
          have hzG : z ∈ section16GoodDomain B (H ∩ JΔ) Y x0 := by
            rw [section16GoodDomain_inter]
            exact Finset.mem_filter.mpr ⟨hz, h1⟩
          have hzBs : appendCoordinate (section16Init z + x0) (section16Last z) ∈ Bs := by
            refine Finset.mem_filter.mpr ⟨hvert_true z hz, ?_⟩
            simpa only [section16Init_appendCoordinate, section16Last_appendCoordinate] using h3
          exact Finset.mem_filter.mpr ⟨hzG, Finset.mem_inter.mpr ⟨hvert_false z hz, h2⟩, hzBs⟩
        · exact Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvert_true z hz, h3⟩)
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
  -- 7. the original frame
  set D' := D.image fun z => z + t
  have hD'card : D'.card = D.card := Finset.card_image_of_injective _ (add_left_injective t)
  have hshift : ∀ z : Point N 2,
      appendCoordinate (section16Init z + x0) (section16Last z) = z + t := fun z => by
    rw [htdef]; exact appendCoordinate_init_add z x0
  have hinit : ∀ z : Point N 2, section16Init (z + t) = section16Init z + x0 := by
    intro z
    have h := congrArg section16Init (hshift z)
    simpa only [section16Init_appendCoordinate] using h.symm
  have hlast : ∀ z : Point N 2, section16Last (z + t) = section16Last z := by
    intro z
    have h := congrArg section16Last (hshift z)
    simpa only [section16Last_appendCoordinate] using h.symm
  have hDmem : ∀ z ∈ D, z ∈ section16GoodDomain B (H ∩ JΔ) Y x0 ∧
      lastPt z ∈ Fdom ∩ Jr ∧ z + t ∈ Bs := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp hz
    exact ⟨h1, h2, by rw [← hshift]; exact h3⟩
  let H1' := (H ∩ JΔ).image fun h => h + x0
  let K' : Point N 1 → Finset (ZMod N) := fun x => section16LargeSpectrum B (x - x0) δ
  let A' : Point N 1 → Finset (ZMod N) := fun x =>
    Finset.univ.filter fun y => (x - x0, y) ∈ section16InducedDomain B H Y
  let f' : Point N 1 → ZMod N → ZMod N := fun x y => phiPrime (x - x0) y
  let rem' : Point N 2 → ZMod N := fun w => phi (appendCoordinate x0 (section16Last w))
  have hHsub : H ∩ JΔ ⊆ H := Finset.inter_subset_left
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
    spec := ?_
    remc := ?_
    slices := ?_ }⟩
  · -- graph inside Gamma
    intro p hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    exact hBG (Finset.mem_image.mpr ⟨z + t, (Finset.mem_filter.mp (hDmem z hz).2.2).1, rfl⟩)
  · rw [hD'card]; exact hDcard
  · -- Bohr linearity
    intro x hx v hv J hJ hd
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hx
    have hsh : h + x0 - x0 = h := add_sub_cancel_right h x0
    have hd' : J.step ∈ bohr (section16LargeSpectrum B h δ) (zeta / v) := by
      simpa only [K', hsh] using hd
    have hlin := hselection.2 h (hHsub hh) v hv J.step hd' J rfl hJ
    simpa only [A', f', hsh, Finset.inter_filter, Finset.inter_univ] using hlin
  · -- domains
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hzG, -, -⟩ := hDmem z hz
    have hzG' : appendCoordinate (section16Init z) (section16Last z) ∈
        section16GoodDomain B (H ∩ JΔ) Y x0 := by
      rw [appendCoordinate_init_last]; exact hzG
    obtain ⟨hhH1, hdom⟩ := section16GoodDomain_fibre_mem B H (H ∩ JΔ) Y x0
      (section16Init z) (section16Last z) hHsub hzG'
    rw [hinit, hlast]
    refine ⟨Finset.mem_image.mpr ⟨section16Init z, hhH1, rfl⟩, ?_⟩
    simp only [A', Finset.mem_filter, Finset.mem_univ, true_and, add_sub_cancel_right]
    exact hdom
  · -- the identity
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hzG, -, -⟩ := hDmem z hz
    have hzB1 : z ∈ B1 := by
      rw [section16GoodDomain_inter] at hzG
      exact (Finset.mem_filter.mp hzG).1
    have hidz := hid z hzB1
    rw [section16PhiRemainder_one] at hidz
    simp only [section16PhiOne, section16PhiPrimeLift, section16TranslatedVertex,
      Bool.false_eq_true, if_false, add_zero] at hidz
    have hcomm : (fun i => x0 i + section16Init z i) = section16Init z + x0 := by
      funext i; simp [add_comm]
    rw [hcomm, hshift] at hidz
    simp only [f', rem', hinit, hlast, add_sub_cancel_right]
    exact hidz
  · -- the spectrum cover
    have hR : RelFreimanCover (polyPieceSpecCountW t1)
        (restrictRelation (section16SpectrumRelation B δ) JΔ) := ⟨Dsp, fsp, hfsp, hcsp⟩
    refine (hR.translate x0).mono ?_
    intro z hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_filter.mp hz
    obtain ⟨hx, -⟩ := Finset.mem_product.mp hz1
    obtain ⟨h, hh, hx'⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨(h, z.2), ?_, ?_⟩
    · have hr : z.2 ∈ section16LargeSpectrum B h δ := by
        simpa only [K', ← hx', add_sub_cancel_right] using hz2
      simpa only [restrictRelation, section16SpectrumRelation, Finset.mem_filter,
        Finset.mem_univ, true_and] using And.intro hr (Finset.mem_inter.mp hh).2
    · rw [hx']
  · -- the remainder cover
    have hR : RelFreimanCover (polyPieceFaceCountW t1 gamma)
        (restrictRelation (partialGraph Fdom g) Jr) := ⟨Dr, fr, hfr, hcr⟩
    refine hR.mono ?_
    intro p hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨-, hzR, -⟩ := hDmem z hz
    obtain ⟨hzF, hzJ⟩ := Finset.mem_inter.mp hzR
    have hlp : lastPt (z + t) = lastPt z := by
      funext i; simp only [lastPt, hlast]
    rw [hlp]
    have hval : rem' (z + t) = g (lastPt z) := by
      simp only [rem', hgdef, CoordinateFace.pullback, hFdef, firstFixedFace, hlast, lastPt]
    rw [hval]
    simp only [restrictRelation, Finset.mem_filter]
    exact ⟨Finset.mem_image.mpr ⟨lastPt z, hzF, rfl⟩, hzJ⟩
  · -- the slices
    refine hfam.mono ?_
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    exact (hDmem z hz).2.2
end LeanProofs.GowersSzemeredi
