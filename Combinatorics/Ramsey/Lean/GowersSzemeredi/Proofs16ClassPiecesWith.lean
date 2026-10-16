import GowersSzemeredi.Proofs16ClassPieces
import GowersSzemeredi.Proofs16DenseSelectionWith
import GowersSzemeredi.Proofs16PolyPieceTwoDataWith

/-! **Class pieces with `(θ₁, ζ)` as parameters** (Notes L.16d).

`class_piece_data` (`Proofs16ClassPieces`) builds one piece of the next
uniform class from an arrangement-dense subset. It fixes the printed
`θ₁ = section16ThetaOne θ γ k` and `ζ = section16Zeta θ γ k`, through the
budget `classBudget = θ₂(θ₁)/2^(k+2)`, the spectrum parameter
`classDelta = δ(θ₁)` and the radius. Here:
* `classBudgetW t1 k = θ₂(t1)/2^(k+2)` and
  `classPieceThrW Thr t1 γ k` are the parameterized budget and threshold.
  At the printed `t1` they equal `classBudget` and `classPieceThr` by `rfl`.
* `class_piece_data_with` is the producer with `(t1, zeta)`, under
  `0 < t1/4 ≤ 1/36`, `ζ ≤ section10Zeta α` for `t1/4 ≤ α ≤ 1/6`, and
  `0 < ζ`. It is generated from the corpus proof by a script with a guard
  that no printed parameter survives.

`ClassPiece` itself is generic in the radius and the budgets. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The class budget `θ₂(t1)/2^(k+2)` at density `t1`. -/
def classBudgetW (t1 : Real) (k : Nat) : Real := section16ThetaTwo t1 / 2 ^ (k + 2)

/-- The class thresholds a piece needs, at density `t1`. -/
def classPieceThrW (Thr : Real → Real → Real) (t1 gamma : Real) (k : Nat) : Real :=
  max (Thr (classBudgetW t1 k) (section16Delta t1)) (Thr (classBudgetW t1 k) gamma)

theorem classBudgetW_printed (theta gamma : Real) (k : Nat) :
    classBudgetW (section16ThetaOne theta gamma k) k = classBudget theta gamma k := rfl

theorem classPieceThrW_printed (Thr : Real → Real → Real) (theta gamma : Real) (k : Nat) :
    classPieceThrW Thr (section16ThetaOne theta gamma k) gamma k = classPieceThr Thr theta gamma k := rfl

theorem classBudgetW_pos_le {t1 : Real} (k : Nat) (ha0 : 0 < t1 / 4) (haS : t1 / 4 ≤ 1 / 36) :
    0 < classBudgetW t1 k ∧ classBudgetW t1 k ≤ 1 := by
  obtain ⟨h0, h1⟩ := section16ThetaTwo_pos_le_with ha0 haS
  have h2 : (1 : Real) ≤ 2 ^ (k + 2) := one_le_pow₀ (by norm_num)
  unfold classBudgetW
  refine ⟨div_pos h0 (by positivity), ?_⟩
  rw [div_le_one (by positivity)]
  linarith

theorem class_piece_data_with {k : Nat} {Thr : Real → Real → Real}
    {Cnt Exp : Real → Real → Nat → Real → Real} (C : UniformClassWith k Thr Cnt Exp)
    {t1 zeta gamma : Real} (ha0 : 0 < t1 / 4) (haS : t1 / 4 ≤ 1 / 36)
    (hzeta : ∀ alpha : Real, t1 / 4 ≤ alpha → alpha ≤ 1 / 6 → zeta ≤ section10Zeta alpha)
    (hz0 : 0 < zeta) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] (hN : classPieceThrW Thr t1 gamma k ≤ N)
    (Gamma : Finset (Point N (k + 1) × ZMod N))
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (hBG : partialGraph B phi ⊆ Gamma)
    (hBarr : t1 * (N : Real) ^ (17 * k + 15) ≤
        generalArrangementCount 8 B ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
        respectedGeneralArrangementCount 8 B phi)
    (hprodB : HasProductProperty B phi gamma) :
    Nonempty (ClassPiece C Gamma (zeta) (classBudgetW t1 k)
      (classBudgetW t1 k) (section16Delta t1) (classBudgetW t1 k) gamma) := by
  classical
  obtain ⟨hθ₁pos, _, hδpos, hδle⟩ := section16_theta_delta_bounds_with ha0 haS
  obtain ⟨hθ'pos, hθ'le⟩ := classBudgetW_pos_le k ha0 haS
  set θ' := classBudgetW t1 k with hθ'def
  have hθ₂eq : section16ThetaTwo (t1) = 2 ^ (k + 2) * θ' := by
    rw [hθ'def, classBudgetW]; field_simp
  set δ := section16Delta t1
  have hN1 : Thr θ' δ ≤ (N : Real) := (le_max_left _ _).trans hN
  have hN2 : Thr θ' gamma ≤ (N : Real) := (le_max_right _ _).trans hN
  -- 1. Lemmas 16.5 and 16.7
  obtain ⟨H, Y, phiPrime, hH, hcube, hselected, hselection⟩ :=
    section16_dense_induced_selection_with (k := k) (Fact.out : N.Prime) t1 zeta
      B phi ha0 haS hzeta hz0 hBarr
  have hmass : t1 / 8 * (N : Real) ^ k ≤ H.card := by
    refine le_trans ?_ hH
    have : (0 : Real) ≤ (N : Real) ^ k := by positivity
    nlinarith
  obtain ⟨x0, hgood, hidentity⟩ := lemma_16_7_with t1 zeta hθ₁pos.le B phi H Y phiPrime
    hmass hcube hselected hselection
  have hid : Section16PhiOneIdentity (section16GoodDomain B H Y x0) phi x0 phiPrime :=
    section16_phi_one_identity_of_common_base B phi H Y x0 phiPrime hidentity
  set B1 := section16GoodDomain B H Y x0 with hB1def
  have hB1card : section16ThetaTwo (t1) * (N : Real) ^ (k + 1) ≤
      B1.card := by
    rw [hB1def, section16GoodDomain_card]; exact hgood
  -- 2. the spectrum, translated to the original frame
  set T := (section16SpectrumRelation B δ).image fun z => (z.1 + x0, z.2) with hTdef
  have hsizeT : (T.card : Real) ≤ δ ^ (-(2 : Int)) * (N : Real) ^ k := by
    have hc : (T.card : Real) ≤ (section16SpectrumRelation B δ).card := by
      exact_mod_cast Finset.card_image_le
    exact hc.trans (section16_spectrum_relation_card B hδpos)
  obtain ⟨JT, hJT, hUT⟩ := C.decomp θ' δ hθ'pos hθ'le hδpos hδle N hN1 T hsizeT
    ((section16_spectrum_relation_product B hδpos).translate x0)
  -- 3. the faces
  have hface : ∀ e : Fin k → Bool, ∃ J : Finset (Point N k),
      (1 - θ') * (N : Real) ^ k ≤ J.card ∧
      (e ≠ (fun _ => true) → C.U N θ' gamma
        (restrictRelation (partialGraph (classFaceDomain B x0 e) (classFace phi x0 e)) J)) := by
    intro e
    by_cases he : e = fun _ => true
    · refine ⟨Finset.univ, ?_, fun h => absurd he h⟩
      have hc : ((Finset.univ : Finset (Point N k)).card : Real) = (N : Real) ^ k := by
        simp [Point, ZMod.card]
      rw [hc]
      have : (0 : Real) ≤ (N : Real) ^ k := by positivity
      nlinarith
    · have hsize : ((partialGraph (classFaceDomain B x0 e) (classFace phi x0 e)).card : Real) ≤
          gamma ^ (-(2 : Int)) * (N : Real) ^ k := by
        rw [partialGraph_card]
        exact (card_point_le_pow k _).trans (le_mul_of_one_le_left (by positivity)
          (one_le_gamma_inv_sq hg hg1))
      obtain ⟨J, hJ, hU⟩ := C.decomp θ' gamma hθ'pos hθ'le hg hg1 N hN2 _ hsize
        (partialGraph_relationProductProperty (classFace_product hprodB hg.le hg1 x0 he))
      exact ⟨J, hJ, fun _ => hU⟩
  choose JF hJF hUF using hface
  -- 4. the slices
  obtain ⟨Cs, hCsub, hCcard, hUS⟩ := class_slice_decomposition C hθ'pos hθ'le hg hg1 hN2 B phi
    hprodB
  -- 5. the domain in the shifted frame
  set D := B1.filter fun z => section16Init (shiftPt x0 z) ∈ JT ∧
    (∀ e ∈ otherVertices k, dropAt (vertexDrop e) (shiftPt x0 z) ∈ JF e) ∧
    section16Init z + x0 ∈ Cs (section16Last z) with hDdef
  set X1 := Finset.univ.filter fun z : Point N (k + 1) => section16Init (shiftPt x0 z) ∉ JT
  set XF := (otherVertices k).biUnion fun e =>
    Finset.univ.filter fun z : Point N (k + 1) => dropAt (vertexDrop e) (shiftPt x0 z) ∉ JF e
  set X5 := Finset.univ.filter fun z : Point N (k + 1) =>
    appendCoordinate (section16Init z + x0) (section16Last z) ∈ B ∧
      section16Init z + x0 ∉ Cs (section16Last z)
  set a := θ' * (N : Real) ^ (k + 1) with hadef
  have ha0 : 0 ≤ a := by positivity
  have hX1 : (X1.card : Real) ≤ a := card_shift_init_bad_le x0 JT hJT
  have hXF : (XF.card : Real) ≤ 2 ^ k * a := by
    have h1 := Finset.card_biUnion_le (s := otherVertices k) (t := fun e =>
      Finset.univ.filter fun z : Point N (k + 1) => dropAt (vertexDrop e) (shiftPt x0 z) ∉ JF e)
    have h2 : (∑ e ∈ otherVertices k, ((Finset.univ.filter fun z : Point N (k + 1) =>
        dropAt (vertexDrop e) (shiftPt x0 z) ∉ JF e).card : Real)) ≤
        ∑ _e ∈ otherVertices k, a :=
      Finset.sum_le_sum fun e _ => card_dropAt_shift_bad_le x0 (vertexDrop e) (JF e) (hJF e)
    have h3 : ((otherVertices k).card : Real) ≤ 2 ^ k := by
      have : (otherVertices k).card ≤ 2 ^ k := by
        refine (Finset.card_filter_le _ _).trans ?_
        simp [Finset.card_univ]
      exact_mod_cast this
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    have h1' : (XF.card : Real) ≤ ∑ e ∈ otherVertices k, ((Finset.univ.filter
        fun z : Point N (k + 1) => dropAt (vertexDrop e) (shiftPt x0 z) ∉ JF e).card : Real) := by
      exact_mod_cast h1
    nlinarith
  have hX5 : (X5.card : Real) ≤ a :=
    card_translated_slice_bad_le_succ (k := k) B Cs hCsub hCcard x0
  have hvert : ∀ z ∈ B1, ∀ e : Fin k → Bool,
      selectPt (Fin.snoc e true) (Fin.snoc x0 0) (shiftPt x0 z) ∈ B := by
    intro z hz e
    have h := section16GoodDomain_vertex_mem B H Y x0 hz e
    rw [translatedVertex_point] at h
    exact h
  have hvert_true : ∀ z ∈ B1, shiftPt x0 z ∈ B := by
    intro z hz
    have h := hvert z hz (fun _ => true)
    have hsel : selectPt (Fin.snoc (fun _ : Fin k => true) true) (Fin.snoc x0 0) (shiftPt x0 z) =
        shiftPt x0 z := by
      funext m
      refine Fin.lastCases ?_ (fun j => ?_) m <;> simp [selectPt]
    rwa [hsel] at h
  have hcover : B1 ⊆ D ∪ X1 ∪ XF ∪ X5 := by
    intro z hz
    by_cases h1 : section16Init (shiftPt x0 z) ∈ JT
    · by_cases h2 : ∀ e ∈ otherVertices k, dropAt (vertexDrop e) (shiftPt x0 z) ∈ JF e
      · by_cases h5 : section16Init z + x0 ∈ Cs (section16Last z)
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨hz, h1, h2, h5⟩)))
        · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, h5⟩)
          rw [← shiftPt_eq_append]
          exact hvert_true z hz
      · obtain ⟨e, he, hne⟩ : ∃ e ∈ otherVertices k, dropAt (vertexDrop e) (shiftPt x0 z) ∉ JF e := by
          by_contra hcon
          exact h2 fun e he => by
            by_contra hn
            exact hcon ⟨e, he, hn⟩
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨e, he, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)))
  have hDcard : a ≤ D.card := by
    have hc := Finset.card_le_card hcover
    have hu1 := Finset.card_union_le (D ∪ X1 ∪ XF) X5
    have hu2 := Finset.card_union_le (D ∪ X1) XF
    have hu3 := Finset.card_union_le D X1
    have h' : (B1.card : Real) ≤ (D.card : Real) + X1.card + XF.card + X5.card := by
      have h := (hc.trans hu1).trans (Nat.add_le_add_right (hu2.trans
        (Nat.add_le_add_right hu3 _)) _)
      exact_mod_cast h
    have hB : 4 * 2 ^ k * a ≤ (B1.card : Real) := by
      rw [hθ₂eq] at hB1card
      calc 4 * 2 ^ k * a = 2 ^ (k + 2) * θ' * (N : Real) ^ (k + 1) := by
            rw [hadef, pow_add]; ring
        _ ≤ _ := hB1card
    have h2k : (1 : Real) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  -- 6. the original frame
  set D' := D.image (shiftPt x0)
  have hD'card : D'.card = D.card := Finset.card_image_of_injective _ (shiftPt_injective x0)
  have hDmem : ∀ z ∈ D, z ∈ B1 ∧ section16Init (shiftPt x0 z) ∈ JT ∧
      (∀ e ∈ otherVertices k, dropAt (vertexDrop e) (shiftPt x0 z) ∈ JF e) ∧
      section16Init z + x0 ∈ Cs (section16Last z) := fun z hz => Finset.mem_filter.mp hz
  let H1' := (H.filter fun h => h + x0 ∈ JT).image fun h => h + x0
  let K' : Point N k → Finset (ZMod N) := fun x => section16LargeSpectrum B (x - x0) δ
  let A' : Point N k → Finset (ZMod N) := fun x =>
    Finset.univ.filter fun y => (x - x0, y) ∈ section16InducedDomain B H Y
  let f' : Point N k → ZMod N → ZMod N := fun x y => phiPrime (x - x0) y
  let G' : (Fin k → Bool) → Point N k → ZMod N := fun e => classFace phi x0 e
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
    linear := ?_
    dom := ?_
    G := G'
    ident := ?_
    spec_U := ?_
    face_U := ?_
    slice_U := ?_ }⟩
  · -- graph inside Gamma
    intro p hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    exact hBG (Finset.mem_image.mpr ⟨shiftPt x0 z, hvert_true z (hDmem z hz).1, rfl⟩)
  · rw [hD'card]; exact hDcard
  · -- Bohr linearity
    intro x hx v hv J hJ hd
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hx
    have hhH : h ∈ H := (Finset.mem_filter.mp hh).1
    have hsh : h + x0 - x0 = h := add_sub_cancel_right h x0
    have hd' : J.step ∈ bohr (section16LargeSpectrum B h δ) (zeta / v) := by
      simpa only [K', hsh] using hd
    have hlin := hselection.2 h hhH v hv J.step hd' J rfl hJ
    simpa only [A', f', hsh, Finset.inter_filter, Finset.inter_univ] using hlin
  · -- domains
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hzB1, hzT, -, -⟩ := hDmem z hz
    have hzG' : appendCoordinate (section16Init z) (section16Last z) ∈
        section16GoodDomain B H Y x0 := by
      rw [appendCoordinate_init_last]; exact hzB1
    obtain ⟨hhH1, hdom⟩ := section16GoodDomain_fibre_mem B H H Y x0
      (section16Init z) (section16Last z) hHsub hzG'
    rw [shiftPt_init, shiftPt_last]
    rw [shiftPt_init] at hzT
    refine ⟨Finset.mem_image.mpr ⟨section16Init z, Finset.mem_filter.mpr ⟨hhH1, hzT⟩, rfl⟩, ?_⟩
    simp only [A', Finset.mem_filter, Finset.mem_univ, true_and, add_sub_cancel_right]
    exact hdom
  · -- the identity
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hzB1, -, -, -⟩ := hDmem z hz
    have hidz := hid z hzB1
    rw [phiOne_eq_shiftPt] at hidz
    rw [hidz]
    simp only [section16PhiPrimeLift, f', shiftPt_init, shiftPt_last, add_sub_cancel_right]
    congr 1
    unfold section16PhiRemainder classRem
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    have he' : e ≠ fun _ => true := (Finset.mem_filter.mp he).2
    rw [translatedVertex_eq_classFace phi x0 he']
  · -- the spectrum
    refine C.mono N θ' δ _ _ ?_ hUT
    intro p hp
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
  · -- the faces
    intro e he
    have he' : e ≠ fun _ => true := (Finset.mem_filter.mp he).2
    refine C.mono N θ' gamma _ _ ?_ (hUF e he')
    intro p hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hzB1, -, hzF, -⟩ := hDmem z hz
    unfold restrictRelation
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨dropAt (vertexDrop e) (shiftPt x0 z),
      mem_classFaceDomain he' (hvert z hzB1 e), rfl⟩, hzF e he⟩
  · -- the slices
    intro s
    refine C.mono N θ' gamma _ _ ?_ (hUS s)
    unfold partialGraph
    refine Finset.image_subset_image ?_
    intro h hh
    unfold section16FinalCoordinateSection at hh
    obtain ⟨-, hhD⟩ := Finset.mem_filter.mp hh
    obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp hhD
    obtain ⟨-, -, -, hz5⟩ := hDmem z hz
    have hi := congrArg section16Init hzeq
    have hl := congrArg section16Last hzeq
    rw [shiftPt_init, section16Init_appendCoordinate] at hi
    rw [shiftPt_last, section16Last_appendCoordinate] at hl
    rw [← hi, ← hl]
    exact hz5
end LeanProofs.GowersSzemeredi
