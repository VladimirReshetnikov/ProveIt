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
and the face `firstFixedFace x₀ : y ↦ (x₀, y)`.

The budgets `polyPieceBudgetW`, `polyPieceSpecCountW`, `polyPieceFaceCountW` and
`section16_poly_piece_two_data_with` take the density `t1` and the radius `ζ`
as parameters (Notes L.16d). At the printed values the budgets are the printed
ones by `rfl`, and `section16_poly_piece_two_data` is the
instance.

`section16_poly_piece_two_data` is in `Proofs16PolyPieceTwoDataSide`, outside
the final route. -/
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
  simp [lastCylinder]

/-- A relation inside `q` graphs has fibres of size at most `q`. -/
theorem RelFreimanCover.fiber_le {N q : Nat} [NeZero N] {R : Finset (Point N 1 × ZMod N)}
    (h : RelFreimanCover q R) (x : Point N 1) : (R.filter fun z => z.1 = x).card ≤ q := by
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

/-- The deletion budget `θ₂(t1)/8` of a dimension-two piece. -/
def polyPieceBudgetW (t1 : Real) : Real := section16ThetaTwo t1 / 8

/-- The Freiman-family count of the spectrum relation, at density `t1`. -/
def polyPieceSpecCountW (t1 : Real) : Nat :=
  section16BaseFamilyBound (section16Delta t1) (polyPieceBudgetW t1)

/-- The Freiman-family count of the faces and slices, at density `t1`. -/
def polyPieceFaceCountW (t1 gamma : Real) : Nat :=
  section16BaseFamilyBound gamma (polyPieceBudgetW t1)

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
  have hθ'pos : 0 < polyPieceBudgetW t1 := by unfold polyPieceBudgetW; linarith
  have hθ'le : polyPieceBudgetW t1 ≤ 1 := by unfold polyPieceBudgetW; linarith
  set θ' := polyPieceBudgetW t1 with hθ'def
  have hθ₂eq : section16ThetaTwo t1 = 8 * θ' := by rw [hθ'def, polyPieceBudgetW]; ring
  set δ := section16Delta t1
  -- 1. Lemmas 16.5 and 16.7
  obtain ⟨H, Y, phiPrime, hH, hcube, hselected, hselection⟩ :=
    section16_dense_induced_selection_with (Fact.out : N.Prime) t1 zeta B phi
      ha0 haS hzeta hz0 hBarr
  obtain ⟨x0, hgood, hidentity⟩ := lemma_16_7_with t1 zeta hθ₁pos.le B phi H Y phiPrime
    (le_trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) hH) hcube hselected
    hselection
  have hid := section16_phi_one_identity_of_common_base B phi H Y x0 phiPrime hidentity
  set B1 := section16GoodDomain B H Y x0 with hB1def
  have hB1card : 8 * θ' * (N : Real) ^ 2 ≤ B1.card := by
    rw [hB1def, section16GoodDomain_card, ← hθ₂eq]; exact hgood
  -- 2. the spectrum families
  obtain ⟨JΔ, Dsp, fsp, hJΔ, hfsp, hcsp⟩ := section16_extract_uniform_base_family hδpos hδle
    hθ'pos hθ'le (section16SpectrumRelation B δ)
    (by simpa using section16_spectrum_relation_card B hδpos)
    (section16_spectrum_relation_product B hδpos)
  -- 3. the face families
  set F := firstFixedFace (N := N) x0
  set Fdom := F.domain B
  set g := F.pullback phi
  have hsizeF : ((partialGraph Fdom g).card : Real) ≤ gamma ^ (-(2 : Int)) * N := by
    rw [partialGraph_card, zpow_neg, zpow_ofNat]
    refine le_trans ?_ (le_mul_of_one_le_left (Nat.cast_nonneg _)
      ((one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)))
    exact_mod_cast (show Fdom.card ≤ N by simpa [Point, ZMod.card] using Finset.card_le_univ Fdom)
  obtain ⟨Jr, Dr, fr, hJr, hfr, hcr⟩ := section16_extract_uniform_base_family hg hg1
    hθ'pos hθ'le (partialGraph Fdom g) hsizeF
    (partialGraph_relationProductProperty (hprodB.coordinateFace F))
  -- 4. the slice families
  obtain ⟨C, hCsub, hCcard, hfam⟩ :=
    section16_final_freiman_families_of_product hg hg1 hθ'pos hθ'le B phi hprodB
  set Bs := B.filter fun z => section16Init z ∈ C (section16Last z)
  -- 5. the domain in the shifted frame; the original frame is `w = z + t`
  set t : Point N 2 := appendCoordinate x0 0
  have hshift (z : Point N 2) :
      appendCoordinate (section16Init z + x0) (section16Last z) = z + t :=
    appendCoordinate_init_add z x0
  have hshift' (z : Point N 2) :
      appendCoordinate (fun i => x0 i + section16Init z i) (section16Last z) = z + t :=
    (congrArg (appendCoordinate · (section16Last z)) (add_comm x0 _)).trans (hshift z)
  have hinit (z : Point N 2) : section16Init (z + t) = section16Init z + x0 := by
    rw [← hshift, section16Init_appendCoordinate]
  have hlast (z : Point N 2) : section16Last (z + t) = section16Last z := by
    rw [← hshift, section16Last_appendCoordinate]
  have hvert : ∀ z ∈ B1, z + t ∈ B ∧ lastPt z ∈ Fdom := fun z hz => by
    have h1 := section16GoodDomain_vertex_mem B H Y x0 hz (fun _ => true)
    have h0 := section16GoodDomain_vertex_mem B H Y x0 hz (fun _ => false)
    simp only [if_true, Bool.false_eq_true, if_false, add_zero, hshift'] at h1 h0
    exact ⟨h1, (CoordinateFace.mem_domain _ _ _).mpr h0⟩
  set D := B1.filter fun z => section16Init z ∈ JΔ ∧ lastPt z ∈ Fdom ∩ Jr ∧ z + t ∈ Bs
  -- 6. the three deletions are sparse
  set X1 := Finset.univ.filter fun z : Point N 2 => section16Init z ∉ JΔ
  set X2 := Finset.univ.filter fun z : Point N 2 => lastPt z ∉ Jr
  set X3 := Finset.univ.filter fun z : Point N 2 =>
    appendCoordinate (section16Init z + x0) (section16Last z) ∈ B ∧
      section16Init z + x0 ∉ C (section16Last z)
  have hX1card : (X1.card : Real) ≤ θ' * (N : Real) ^ 2 := by
    have h := card_filter_selected_not_mem_le (n := 2) (l := 1)
      ⟨Fin.castSucc, Fin.castSucc_injective 1⟩ 0 JΔ (by simpa using hJΔ) (by omega)
    simp only [Function.Embedding.coeFn_mk, Pi.zero_apply, add_zero] at h
    exact h
  have hX2card : (X2.card : Real) ≤ θ' * (N : Real) ^ 2 := by
    have h := card_filter_selected_not_mem_le (n := 2) (l := 1)
      ⟨fun _ => Fin.last 1, fun a b _ => Subsingleton.elim a b⟩ 0 Jr (by simpa using hJr)
      (by omega)
    simp only [Function.Embedding.coeFn_mk, Pi.zero_apply, add_zero] at h
    exact h
  have hX3card : (X3.card : Real) ≤ θ' * (N : Real) ^ 2 :=
    card_translated_slice_bad_le B C hCsub hCcard x0
  have hcover : B1 ⊆ D ∪ X1 ∪ X2 ∪ X3 := fun z hz => by
    obtain ⟨hzt, hzF⟩ := hvert z hz
    simp only [D, X1, X2, X3, Bs, Finset.mem_union, Finset.mem_filter, Finset.mem_inter,
      Finset.mem_univ, true_and, hshift, hinit, hlast, hz, hzt, hzF]
    tauto
  have hDcard : 5 * θ' * (N : Real) ^ 2 ≤ D.card := by
    have h : B1.card ≤ D.card + X1.card + X2.card + X3.card :=
      (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_right
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _))
    have h' : (B1.card : Real) ≤ D.card + X1.card + X2.card + X3.card := by exact_mod_cast h
    linarith
  -- 7. the original frame
  let H1' := (H ∩ JΔ).image fun h => h + x0
  let K' : Point N 1 → Finset (ZMod N) := fun x => section16LargeSpectrum B (x - x0) δ
  let A' : Point N 1 → Finset (ZMod N) := fun x =>
    Finset.univ.filter fun y => (x - x0, y) ∈ section16InducedDomain B H Y
  let f' : Point N 1 → ZMod N → ZMod N := fun x y => phiPrime (x - x0) y
  let rem' : Point N 2 → ZMod N := fun w => phi (appendCoordinate x0 (section16Last w))
  refine ⟨{
    D := D.image fun z => z + t, phi := phi, H1 := H1', K := K', A := A', f := f', rem := rem',
    graph_sub := ?_, card_ge := ?_, linear := ?_, dom := ?_, ident := ?_, spec := ?_,
    remc := ?_, slices := ?_ }⟩
  · -- graph inside Gamma
    intro p hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    exact hBG (Finset.mem_image.mpr ⟨z + t, (hvert z (Finset.mem_filter.mp hz).1).1, rfl⟩)
  · rw [Finset.card_image_of_injective _ (add_left_injective t)]; exact hDcard
  · -- Bohr linearity
    intro x hx v hv J hJ hd
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hx
    simp only [K', A', f', add_sub_cancel_right, Finset.inter_filter, Finset.inter_univ] at hd ⊢
    exact hselection.2 h (Finset.mem_inter.mp hh).1 v hv J.step hd J rfl hJ
  · -- domains
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hzB1, hzJ, -⟩ := Finset.mem_filter.mp hz
    obtain ⟨hhH, hdom⟩ := section16GoodDomain_fibre_mem B H H Y x0 (section16Init z)
      (section16Last z) (Finset.Subset.refl _) ((appendCoordinate_init_last z).symm ▸ hzB1)
    rw [hinit, hlast]
    exact ⟨Finset.mem_image.mpr ⟨_, Finset.mem_inter.mpr ⟨hhH, hzJ⟩, rfl⟩,
      by simpa [A'] using hdom⟩
  · -- the identity
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    have hidz := hid z (Finset.mem_filter.mp hz).1
    rw [section16PhiRemainder_one] at hidz
    simp only [section16PhiOne, section16PhiPrimeLift, section16TranslatedVertex,
      Bool.false_eq_true, if_false, add_zero, hshift'] at hidz
    simpa only [f', rem', hinit, hlast, add_sub_cancel_right] using hidz
  · -- the spectrum cover
    have hR : RelFreimanCover (polyPieceSpecCountW t1)
        (restrictRelation (section16SpectrumRelation B δ) JΔ) := ⟨Dsp, fsp, hfsp, hcsp⟩
    refine (hR.translate x0).mono fun z hz => ?_
    obtain ⟨hz1, hz2⟩ := Finset.mem_filter.mp hz
    obtain ⟨h, hh, hx⟩ := Finset.mem_image.mp (Finset.mem_product.mp hz1).1
    have hr : z.2 ∈ section16LargeSpectrum B h δ := by
      simpa only [K', ← hx, add_sub_cancel_right] using hz2
    refine Finset.mem_image.mpr ⟨(h, z.2), ?_, by rw [hx]⟩
    simpa only [restrictRelation, section16SpectrumRelation, Finset.mem_filter,
      Finset.mem_univ, true_and] using And.intro hr (Finset.mem_inter.mp hh).2
  · -- the remainder cover
    have hR : RelFreimanCover (polyPieceFaceCountW t1 gamma)
        (restrictRelation (partialGraph Fdom g) Jr) := ⟨Dr, fr, hfr, hcr⟩
    refine hR.mono fun p hp => ?_
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hzF, hzJ⟩ := Finset.mem_inter.mp (Finset.mem_filter.mp hz).2.2.1
    have hlp : lastPt (z + t) = lastPt z := funext fun _ => hlast z
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨lastPt z, hzF, ?_⟩, hlp ▸ hzJ⟩
    rw [hlp]; simp only [rem', hlast]; rfl
  · -- the slices
    refine hfam.mono fun w hw => ?_
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    exact (Finset.mem_filter.mp hz).2.2.2

end LeanProofs.GowersSzemeredi
