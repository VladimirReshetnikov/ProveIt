import GowersSzemeredi.Proofs16RelationLift
import GowersSzemeredi.Proofs16RelFreimanCover
import GowersSzemeredi.Proofs16PolyPieceTwo
import GowersSzemeredi.Proofs16AbstractFamily

/-! Dimension-two pieces in the original frame, with their Freiman data.

`section16_poly_piece_two` returns one piece with its cover. To cover many
pieces at once (`abstract_family_piece_cover_with`), each piece must
instead expose, in the original frame:
* its abstract member data (frequencies, linearity domains, the
  Bohr-linear part, the remainder);
* Freiman covers of its spectrum relation, its remainder relation and all
  its final-coordinate slices.

The unions of these over pieces are again Freiman covers
(`relFreimanCover_union`), so their cubic covers serve every piece
simultaneously.

This part collects the tools: `lastPt`, `lastCylinder` and its cover from
a dimension-one cover (`MultiplyLinearWith.last_cylinder`, the relation lift
followed by the coordinate swap), the fibre bound of a Freiman cover,
and the face `firstFixedFace x₀ : y ↦ (x₀, y)`. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-- The last coordinate as a one-dimensional point. -/
def lastPt {N : Nat} (w : Point N 2) : Point N 1 := fun _ => section16Last w

/-- The cylinder over the last coordinate of a dimension-one relation. -/
def lastCylinder {N : Nat} [NeZero N] (Λ : Finset (Point N 1 × ZMod N)) :
    Finset (Point N 2 × ZMod N) := by
  classical
  exact Finset.univ.filter fun z => (lastPt z.1, z.2) ∈ Λ

theorem mem_lastCylinder {N : Nat} [NeZero N] {Λ : Finset (Point N 1 × ZMod N)}
    {z : Point N 2 × ZMod N} : z ∈ lastCylinder Λ ↔ (lastPt z.1, z.2) ∈ Λ := by
  classical
  simp [lastCylinder]

/-- A relation inside `q` graphs has fibres of size at most `q`. -/
theorem RelFreimanCover.fiber_le {N q : Nat} [NeZero N] {R : Finset (Point N 1 × ZMod N)}
    (h : RelFreimanCover q R) (x : Point N 1) : (R.filter fun z => z.1 = x).card ≤ q := by
  classical
  obtain ⟨D, f, -, hc⟩ := h
  have hsub : (R.filter fun z => z.1 = x) ⊆
      (section16FinsetUnion (fun i => partialGraph (D i) (f i))).filter fun z => z.1 = x :=
    Finset.filter_subset_filter _ hc
  refine (Finset.card_le_card hsub).trans ?_
  unfold section16FinsetUnion
  rw [Finset.filter_biUnion]
  calc (Finset.univ.biUnion fun i => (partialGraph (D i) (f i)).filter fun z => z.1 = x).card
      ≤ ∑ i, ((partialGraph (D i) (f i)).filter fun z => z.1 = x).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin q, 1 := Finset.sum_le_sum fun i _ => partialGraph_fiber_card_le_one _ _ x
    _ = q := by simp

/-- **A cylinder over the last coordinate inherits a cover.** -/
theorem MultiplyLinearWith.last_cylinder {N : Nat} [NeZero N] [Fact N.Prime]
    {Qb Eb : Real → Real} {Λ : Finset (Point N 1 × ZMod N)}
    (hML : MultiplyLinearWith Qb Eb Λ)
    (M : Nat) (hfib : ∀ x : Point N 1, (Λ.filter fun z => z.1 = x).card ≤ M)
    (hQ : ∀ t, 0 < t → t ≤ 1 → 0 ≤ Qb t)
    (hE : ∀ t, 0 < t → t ≤ 1 → 0 < Eb t ∧ Eb t ≤ 1) :
    MultiplyLinearWith (fun t => max (Qb t) ((3 ^ (1 + 1) * M : Nat) : Real))
      (fun t => Eb t / 16) (lastCylinder Λ) := by
  classical
  have h := hML.relation_lift_last M hfib hQ hE (by norm_num)
  have h2 := MultiplyLinearWith.coordinateReindex h (Equiv.swap 0 1)
  refine MultiplyLinearWith.subset h2 ?_
  intro z hz
  have hzΛ := mem_lastCylinder.mp hz
  refine Finset.mem_image.mpr ⟨(LeanProofs.GowersSzemeredi.coordinateReindex (Equiv.swap (0 : Fin 2) 1) z.1, z.2), ?_, ?_⟩
  · apply mem_lastLiftRelation.mpr
    have heq : section16Init (LeanProofs.GowersSzemeredi.coordinateReindex (Equiv.swap (0 : Fin 2) 1) z.1) = lastPt z.1 := by
      funext i
      fin_cases i
      rfl
    rw [heq]
    exact hzΛ
  · refine Prod.ext ?_ rfl
    funext i
    fin_cases i <;> rfl

/-- The face `y ↦ (x₀, y)` of the plane. -/
def firstFixedFace {N : Nat} (x0 : Point N 1) : CoordinateFace N 2 1 where
  free := ⟨fun _ => Fin.last 1, fun a b _ => Subsingleton.elim a b⟩
  anchor := appendCoordinate x0 0
  map y := appendCoordinate x0 (y 0)
  map_free := by
    intro y i
    fin_cases i
    change appendCoordinate x0 (y 0) (Fin.last 1) = y 0
    rw [appendCoordinate_eq_snoc]
    exact Fin.snoc_last _ _
  map_fixed := by
    intro y j hj
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · simp [appendCoordinate_eq_snoc]
    · exact ((hj 0) rfl).elim


/-- **One dimension-two piece of a relation, in the original frame**, with
its abstract member data and its Freiman covers exposed. -/
structure PolyPieceTwoData {N : Nat} [NeZero N] (Gamma : Finset (Point N 2 × ZMod N))
    (zeta mass : Real) (qs qr ql : Nat) where
  D : Finset (Point N 2)
  phi : Point N 2 → ZMod N
  graph_sub : partialGraph D phi ⊆ Gamma
  card_ge : mass * (N : Real) ^ 2 ≤ D.card
  H1 : Finset (Point N 1)
  K : Point N 1 → Finset (ZMod N)
  A : Point N 1 → Finset (ZMod N)
  f : Point N 1 → ZMod N → ZMod N
  rem : Point N 2 → ZMod N
  linear : ∀ x ∈ H1, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
    J.step ∈ bohr (K x) (zeta / v) → LinearOn (J.carrier ∩ A x) (f x)
  dom : ∀ z ∈ D, section16Init z ∈ H1 ∧ section16Last z ∈ A (section16Init z)
  ident : ∀ z ∈ D,
    phi z = (-1 : ZMod N) ^ 1 * f (section16Init z) (section16Last z) + rem z
  spec : RelFreimanCover qs ((H1 ×ˢ (Finset.univ : Finset (ZMod N))).filter fun z => z.2 ∈ K z.1)
  remc : RelFreimanCover qr (D.image fun w => (lastPt w, rem w))
  slices : Section16FinalFreimanFamilies ql D phi

/-- **A dimension-two piece with its Freiman data, in the original frame.** -/
theorem section16_poly_piece_two_data
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] (Gamma : Finset (Point N 2 × ZMod N))
    (B : Finset (Point N 2)) (phi : Point N 2 → ZMod N)
    (hBG : partialGraph B phi ⊆ Gamma)
    (hBarr : section16ThetaOne theta gamma 1 * (N : Real) ^ (17 * 1 + 15) ≤
        generalArrangementCount 8 B ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
        respectedGeneralArrangementCount 8 B phi)
    (hprodB : HasProductProperty B phi gamma) :
    Nonempty (PolyPieceTwoData Gamma (section16Zeta theta gamma 1)
      (5 * polyPieceBudget theta gamma) (polyPieceSpecCount theta gamma)
      (polyPieceFaceCount theta gamma) (polyPieceFaceCount theta gamma)) := by
  classical
  obtain ⟨hθ₁pos, hθ₁le, hδpos, hδle⟩ := section16_theta_delta_bounds 1 ht ht1 hg hg1
  obtain ⟨hθ₂pos, hθ₂le⟩ := section16ThetaTwo_pos_le 1 ht ht1 hg hg1
  have hθ'pos : 0 < polyPieceBudget theta gamma := by
    unfold polyPieceBudget; positivity
  have hθ'le : polyPieceBudget theta gamma ≤ 1 := by
    unfold polyPieceBudget; linarith
  set θ' := polyPieceBudget theta gamma with hθ'def
  have hθ₂eq : section16ThetaTwo (section16ThetaOne theta gamma 1) = 8 * θ' := by
    rw [hθ'def, polyPieceBudget]; ring
  set δ := section16Delta (section16ThetaOne theta gamma 1) with hδdef
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
  set D' := D.image fun z => z + t with hD'def
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
    have hd' : J.step ∈ bohr (section16LargeSpectrum B h δ) (section16Zeta theta gamma 1 / v) := by
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
    have hR : RelFreimanCover (polyPieceSpecCount theta gamma)
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
    have hR : RelFreimanCover (polyPieceFaceCount theta gamma)
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
