import GowersSzemeredi.Proofs16PowerUniformClass
import GowersSzemeredi.Proofs16CoordinateSelections
import GowersSzemeredi.Proofs16PolyPieceThreeData
import GowersSzemeredi.Proofs16ProductTranslate
import GowersSzemeredi.Proofs16ThreeSlices

/-! Pieces over a uniform class, in every dimension (Notes L.6, E3).

Let `C` be a uniform class of `k`-dimensional relations. A `ClassPiece C Γ`
is a `(k+1)`-dimensional partial function inside `Γ` with Gowers's data:
* the Bohr-linear functions `f(x, ·)` on `H₁` (Lemma 16.5);
* the identity `φ = (-1)^k f(init, last) + classRem G` with one face function
  `G e` for each vertex `e ≠ 1`, read through `dropAt (vertexDrop e)`;
* the spectrum relation, every face relation and every slice are members of
  `C` (at `(θ′, δ)`, `(θ′, γ)` and `(θ′, γ)` respectively).

`class_piece_data` builds one from Lemma 15.6's arrangements at dimension
`k` and the product property. It is the construction of
`section16_poly_piece_three_data` in every dimension. The five deletions of
dimension three become `2^k + 1`: the spectrum, one per vertex `e ≠ 1`
(`card_dropAt_shift_bad_le`), and the slices. Each costs at most `θ′N^(k+1)`,
with `θ′ = θ₂/2^(k+2)` (`classBudget`). So the piece keeps mass `θ′`.

`classBudgetW`, `classPieceThrW` and `class_piece_data_with` take `(t1, ζ)` as
parameters (Notes L.16d); at the printed values the budgets are the printed
ones by `rfl`, and `class_piece_data` is the instance.

`classBudget_pos_le`, `classDelta`, `classPieceThr`, `classPieceThreshold` and
`class_piece_data` are in `Proofs16ClassPiecesSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### Vertices, faces and the remainder -/

/-- The coordinate dropped for vertex `e`: one where `e` is false. -/
def vertexDrop {k : Nat} (e : Fin k → Bool) : Fin (k + 1) :=
  if h : ∃ i, e i = false then (Classical.choose h).castSucc else Fin.last k

theorem vertexDrop_spec {k : Nat} {e : Fin k → Bool} (he : e ≠ fun _ => true) :
    ∃ i, vertexDrop e = i.castSucc ∧ e i = false := by
  have h := exists_false_of_ne_one he
  refine ⟨Classical.choose h, ?_, Classical.choose_spec h⟩
  unfold vertexDrop
  rw [dif_pos h]

/-- The face function of vertex `e`, a function of `k` coordinates. -/
def classFace {N k : Nat} (phi : Point N (k + 1) → ZMod N) (x0 : Point N k) (e : Fin k → Bool)
    (y : Point N k) : ZMod N :=
  phi (selectPt (Fin.snoc e true) (Fin.snoc x0 0) (Fin.insertNth (vertexDrop e) 0 y))

/-- The domain of the face function of vertex `e` inside `B`. -/
def classFaceDomain {N k : Nat} [NeZero N] (B : Finset (Point N (k + 1))) (x0 : Point N k)
    (e : Fin k → Bool) : Finset (Point N k) := by
  classical
  exact Finset.univ.filter fun y =>
    selectPt (Fin.snoc e true) (Fin.snoc x0 0) (Fin.insertNth (vertexDrop e) 0 y) ∈ B

theorem classFace_eq_faceSel {N k : Nat} (phi : Point N (k + 1) → ZMod N) (x0 : Point N k)
    {e : Fin k → Bool} {i : Fin k} (hp : vertexDrop e = i.castSucc) :
    classFace phi x0 e = faceSel phi x0 e i := by
  funext y
  unfold classFace faceSel
  rw [hp]

theorem classFaceDomain_eq {N k : Nat} [NeZero N] (B : Finset (Point N (k + 1))) (x0 : Point N k)
    {e : Fin k → Bool} {i : Fin k} (hp : vertexDrop e = i.castSucc) :
    classFaceDomain B x0 e = faceSelDomain B x0 e i := by
  unfold classFaceDomain faceSelDomain
  rw [hp]

theorem mem_classFaceDomain {N k : Nat} [NeZero N] {B : Finset (Point N (k + 1))} {x0 : Point N k}
    {e : Fin k → Bool} (he : e ≠ fun _ => true) {w : Point N (k + 1)}
    (hw : selectPt (Fin.snoc e true) (Fin.snoc x0 0) w ∈ B) :
    dropAt (vertexDrop e) w ∈ classFaceDomain B x0 e := by
  obtain ⟨i, hp, hi⟩ := vertexDrop_spec he
  rw [classFaceDomain_eq B x0 hp, hp]
  exact mem_faceSelDomain hi hw

theorem classFace_product {N k : Nat} [NeZero N] {B : Finset (Point N (k + 1))}
    {phi : Point N (k + 1) → ZMod N} {gamma : Real} (h : HasProductProperty B phi gamma)
    (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1) (x0 : Point N k) {e : Fin k → Bool}
    (he : e ≠ fun _ => true) :
    HasProductProperty (classFaceDomain B x0 e) (classFace phi x0 e) gamma := by
  obtain ⟨i, hp, -⟩ := vertexDrop_spec he
  rw [classFaceDomain_eq B x0 hp, classFace_eq_faceSel phi x0 hp]
  exact faceSel_product h hg0 hg1 x0 e i

/-- The vertices other than the all-ones one. -/
def otherVertices (k : Nat) : Finset (Fin k → Bool) :=
  Finset.univ.filter fun e : Fin k → Bool => e ≠ fun _ => true

/-- The remainder of Gowers's identity, from face functions. -/
def classRem {N k : Nat} (G : (Fin k → Bool) → Point N k → ZMod N) (w : Point N (k + 1)) :
    ZMod N :=
  -∑ e ∈ otherVertices k, (-1 : ZMod N) ^ (k + boolWeight e) * G e (dropAt (vertexDrop e) w)

/-- The spectrum relation of member data. -/
def pieceSpecRel {N k : Nat} [NeZero N] (H1 : Finset (Point N k))
    (K : Point N k → Finset (ZMod N)) : Finset (Point N k × ZMod N) := by
  classical
  exact (H1 ×ˢ (Finset.univ : Finset (ZMod N))).filter fun z => z.2 ∈ K z.1

/-- The face relation of a domain. -/
def pieceFaceRel {N k : Nat} [NeZero N] (D : Finset (Point N (k + 1)))
    (G : (Fin k → Bool) → Point N k → ZMod N) (e : Fin k → Bool) :
    Finset (Point N k × ZMod N) :=
  D.image fun z => (dropAt (vertexDrop e) z, G e (dropAt (vertexDrop e) z))

/-! ### The pieces -/

/-- **A `(k+1)`-dimensional piece over a uniform class.** -/
structure ClassPiece {k : Nat} {Thr : Real → Real → Real} {Cnt Exp : Real → Real → Nat → Real → Real}
    (C : UniformClassWith k Thr Cnt Exp)
    {N : Nat} [NeZero N] (Gamma : Finset (Point N (k + 1) × ZMod N))
    (zeta mass thS gS thF gF : Real) where
  D : Finset (Point N (k + 1))
  phi : Point N (k + 1) → ZMod N
  graph_sub : partialGraph D phi ⊆ Gamma
  card_ge : mass * (N : Real) ^ (k + 1) ≤ D.card
  H1 : Finset (Point N k)
  K : Point N k → Finset (ZMod N)
  A : Point N k → Finset (ZMod N)
  f : Point N k → ZMod N → ZMod N
  linear : ∀ x ∈ H1, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
    J.step ∈ bohr (K x) (zeta / v) → LinearOn (J.carrier ∩ A x) (f x)
  dom : ∀ z ∈ D, section16Init z ∈ H1 ∧ section16Last z ∈ A (section16Init z)
  G : (Fin k → Bool) → Point N k → ZMod N
  ident : ∀ z ∈ D,
    phi z = (-1 : ZMod N) ^ k * f (section16Init z) (section16Last z) + classRem G z
  spec_U : C.U N thS gS (pieceSpecRel H1 K)
  face_U : ∀ e ∈ otherVertices k, C.U N thF gF (pieceFaceRel D G e)
  slice_U : ∀ t, C.U N thF gF
    (partialGraph (section16FinalCoordinateSection D t) (section16FinalCoordinateRestriction phi t))

/-! ### Parameters -/

/-- The deletion budget of a `(k+1)`-dimensional piece: `θ₂/2^(k+2)`. -/
def classBudget (theta gamma : Real) (k : Nat) : Real :=
  section16ThetaTwo (section16ThetaOne theta gamma k) / 2 ^ (k + 2)

/-! ### Deletions -/

/-- The original frame `w = z + (x₀, 0)`. -/
def shiftPt {N k : Nat} (x0 : Point N k) (z : Point N (k + 1)) : Point N (k + 1) :=
  z + appendCoordinate x0 0

theorem shiftPt_injective {N k : Nat} (x0 : Point N k) : Function.Injective (shiftPt x0) := by
  intro z z' h
  exact add_right_cancel h

theorem shiftPt_init {N k : Nat} (x0 : Point N k) (z : Point N (k + 1)) :
    section16Init (shiftPt x0 z) = section16Init z + x0 := by
  funext i
  simp [shiftPt, section16Init, appendCoordinate_eq_snoc]

theorem shiftPt_last {N k : Nat} (x0 : Point N k) (z : Point N (k + 1)) :
    section16Last (shiftPt x0 z) = section16Last z := by
  simp [shiftPt, section16Last, appendCoordinate_eq_snoc]

theorem shiftPt_eq_append {N k : Nat} (x0 : Point N k) (z : Point N (k + 1)) :
    shiftPt x0 z = appendCoordinate (section16Init z + x0) (section16Last z) := by
  rw [← shiftPt_init, ← shiftPt_last, appendCoordinate_init_last]

theorem card_shift_init_bad_le {N k : Nat} [NeZero N] {theta : Real} (x0 : Point N k)
    (J : Finset (Point N k)) (hJ : (1 - theta) * (N : Real) ^ k ≤ J.card) :
    (((Finset.univ : Finset (Point N (k + 1))).filter fun z =>
      section16Init (shiftPt x0 z) ∉ J).card : Real) ≤ theta * (N : Real) ^ (k + 1) := by
  have h := card_filter_selected_not_mem_le (n := k + 1) (l := k)
    ⟨Fin.castSucc, Fin.castSucc_injective k⟩ x0 J hJ (by omega)
  have hset : ((Finset.univ : Finset (Point N (k + 1))).filter fun z =>
      section16Init (shiftPt x0 z) ∉ J) =
      (Finset.univ.filter fun z : Point N (k + 1) =>
        (fun i => z ((⟨Fin.castSucc, Fin.castSucc_injective k⟩ : Fin k ↪ Fin (k + 1)) i) + x0 i)
          ∉ J) :=
    Finset.filter_congr fun z _ => by rw [shiftPt_init]; rfl
  rw [hset]
  exact h

theorem card_dropAt_shift_bad_le {N k : Nat} [NeZero N] {theta : Real} (x0 : Point N k)
    (p : Fin (k + 1)) (J : Finset (Point N k)) (hJ : (1 - theta) * (N : Real) ^ k ≤ J.card) :
    (((Finset.univ : Finset (Point N (k + 1))).filter fun z =>
      dropAt p (shiftPt x0 z) ∉ J).card : Real) ≤ theta * (N : Real) ^ (k + 1) := by
  have h := card_filter_selected_not_mem_le (n := k + 1) (l := k)
    ⟨p.succAbove, Fin.succAbove_right_injective⟩ (dropAt p (appendCoordinate x0 0)) J hJ
    (by omega)
  have hset : ((Finset.univ : Finset (Point N (k + 1))).filter fun z =>
      dropAt p (shiftPt x0 z) ∉ J) =
      (Finset.univ.filter fun z : Point N (k + 1) =>
        (fun i => z ((⟨p.succAbove, Fin.succAbove_right_injective⟩ : Fin k ↪ Fin (k + 1)) i) +
          dropAt p (appendCoordinate x0 0) i) ∉ J) :=
    Finset.filter_congr fun z _ => Iff.rfl
  rw [hset]
  exact h

/-! ### Slices -/

/-- **Every section restricts to a class member on a dense subset.** -/
theorem class_slice_decomposition {k : Nat} {Thr : Real → Real → Real}
    {Cnt Exp : Real → Real → Nat → Real → Real} (C : UniformClassWith k Thr Cnt Exp)
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] (hN : Thr theta gamma ≤ (N : Real))
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (hprod : HasProductProperty B phi gamma) :
    ∃ Cs : ZMod N → Finset (Point N k),
      (∀ t, Cs t ⊆ section16FinalCoordinateSection B t) ∧
      (∀ t, ((section16FinalCoordinateSection B t).card : Real) - theta * (N : Real) ^ k ≤
        (Cs t).card) ∧
      ∀ t, C.U N theta gamma
        (partialGraph (Cs t) (section16FinalCoordinateRestriction phi t)) := by
  choose J hJ hU using fun t : ZMod N => C.decomp theta gamma ht ht1 hg hg1 N hN _ (by
    rw [partialGraph_card]
    exact (card_point_le_pow k _).trans (le_mul_of_one_le_left (by positivity)
      (one_le_gamma_inv_sq hg hg1))) (partialGraph_relationProductProperty (hprod.final_section t))
  refine ⟨fun t => section16FinalCoordinateSection B t ∩ J t, fun t => Finset.inter_subset_left,
    fun t => ?_, fun t => C.mono N theta gamma _ _ (fun p hp => ?_) (hU t)⟩
  · have h := Finset.card_union_add_card_inter (section16FinalCoordinateSection B t) (J t)
    have hu := card_point_le_pow k (section16FinalCoordinateSection B t ∪ J t)
    have h' : ((section16FinalCoordinateSection B t ∪ J t).card : Real) +
        (section16FinalCoordinateSection B t ∩ J t).card =
        (section16FinalCoordinateSection B t).card + (J t).card := by exact_mod_cast h
    linarith [hJ t]
  · obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hhS, hhJ⟩ := Finset.mem_inter.mp hh
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨h, hhS, rfl⟩, hhJ⟩

/-! ### One piece -/

theorem phiOne_eq_shiftPt {N k : Nat} (phi : Point N (k + 1) → ZMod N) (x0 : Point N k)
    (z : Point N (k + 1)) : section16PhiOne phi x0 z = phi (shiftPt x0 z) := by
  unfold section16PhiOne
  rw [shiftPt_eq_append]
  congr 2
  funext i
  simp [add_comm]

theorem translatedVertex_eq_classFace {N k : Nat} (phi : Point N (k + 1) → ZMod N)
    (x0 : Point N k) {e : Fin k → Bool} (he : e ≠ fun _ => true) (z : Point N (k + 1)) :
    section16TranslatedVertex phi x0 e z =
      classFace phi x0 e (dropAt (vertexDrop e) (shiftPt x0 z)) := by
  unfold section16TranslatedVertex
  rw [translatedVertex_point]
  obtain ⟨i, hp, hi⟩ := vertexDrop_spec he
  rw [classFace_eq_faceSel phi x0 hp, hp]
  exact selectPt_vertex_eq_face phi x0 hi _

/-- The class budget `θ₂(t1)/2^(k+2)` at density `t1`. -/
def classBudgetW (t1 : Real) (k : Nat) : Real := section16ThetaTwo t1 / 2 ^ (k + 2)

/-- The class thresholds a piece needs, at density `t1`. -/
def classPieceThrW (Thr : Real → Real → Real) (t1 gamma : Real) (k : Nat) : Real :=
  max (Thr (classBudgetW t1 k) (section16Delta t1)) (Thr (classBudgetW t1 k) gamma)

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
  obtain ⟨x0, hgood, hidentity⟩ := lemma_16_7_with t1 zeta hθ₁pos.le B phi H Y phiPrime
    (le_trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) hH) hcube hselected
    hselection
  have hid := section16_phi_one_identity_of_common_base B phi H Y x0 phiPrime hidentity
  set B1 := section16GoodDomain B H Y x0 with hB1def
  have hB1card : section16ThetaTwo t1 * (N : Real) ^ (k + 1) ≤ B1.card := by
    rw [hB1def, section16GoodDomain_card]; exact hgood
  -- 2. the spectrum, translated to the original frame
  obtain ⟨JT, hJT, hUT⟩ := C.decomp θ' δ hθ'pos hθ'le hδpos hδle N hN1
    ((section16SpectrumRelation B δ).image fun z => (z.1 + x0, z.2))
    (le_trans (by exact_mod_cast Finset.card_image_le) (section16_spectrum_relation_card B hδpos))
    ((section16_spectrum_relation_product B hδpos).translate x0)
  -- 3. the faces
  choose! JF hJF hUF using fun e (he : e ∈ otherVertices k) =>
    C.decomp θ' gamma hθ'pos hθ'le hg hg1 N hN2 _ (by
      rw [partialGraph_card]
      exact (card_point_le_pow k _).trans (le_mul_of_one_le_left (by positivity)
        (one_le_gamma_inv_sq hg hg1)))
      (partialGraph_relationProductProperty
        (classFace_product hprodB hg.le hg1 x0 (Finset.mem_filter.mp he).2))
  -- 4. the slices
  obtain ⟨Cs, hCsub, hCcard, hUS⟩ := class_slice_decomposition C hθ'pos hθ'le hg hg1 hN2 B phi
    hprodB
  -- 5. the domain in the shifted frame, and the deletions
  have hvert : ∀ z ∈ B1, ∀ e : Fin k → Bool,
      selectPt (Fin.snoc e true) (Fin.snoc x0 0) (shiftPt x0 z) ∈ B := fun z hz e => by
    simpa only [translatedVertex_point, shiftPt] using
      section16GoodDomain_vertex_mem B H Y x0 hz e
  have hvert_true : ∀ z ∈ B1, shiftPt x0 z ∈ B := fun z hz => by
    have h := section16GoodDomain_vertex_mem B H Y x0 hz (fun _ => true)
    simp only [if_true] at h
    rw [shiftPt_eq_append, add_comm (section16Init z) x0]; exact h
  set D := B1.filter fun z => section16Init (shiftPt x0 z) ∈ JT ∧
    (∀ e ∈ otherVertices k, dropAt (vertexDrop e) (shiftPt x0 z) ∈ JF e) ∧
    section16Init z + x0 ∈ Cs (section16Last z)
  set X1 := Finset.univ.filter fun z : Point N (k + 1) => section16Init (shiftPt x0 z) ∉ JT
  set bad := fun e => Finset.univ.filter fun z : Point N (k + 1) =>
    dropAt (vertexDrop e) (shiftPt x0 z) ∉ JF e
  set XF := (otherVertices k).biUnion bad
  set X5 := Finset.univ.filter fun z : Point N (k + 1) =>
    appendCoordinate (section16Init z + x0) (section16Last z) ∈ B ∧
      section16Init z + x0 ∉ Cs (section16Last z)
  set a := θ' * (N : Real) ^ (k + 1) with hadef
  have hX1 : (X1.card : Real) ≤ a := card_shift_init_bad_le x0 JT hJT
  have hXF : (XF.card : Real) ≤ 2 ^ k * a := by
    calc (XF.card : Real) ≤ ∑ e ∈ otherVertices k, ((bad e).card : Real) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ (otherVertices k).card • a := Finset.sum_le_card_nsmul _ _ _ fun e he =>
          card_dropAt_shift_bad_le x0 (vertexDrop e) (JF e) (hJF e he)
      _ ≤ 2 ^ k * a := by
          rw [nsmul_eq_mul]; gcongr
          exact_mod_cast (Finset.card_filter_le _ _).trans (by simp [Finset.card_univ])
  have hX5 : (X5.card : Real) ≤ a :=
    card_translated_slice_bad_le_succ (k := k) B Cs hCsub hCcard x0
  have hcover : B1 ⊆ D ∪ X1 ∪ XF ∪ X5 := fun z hz => by
    simp only [D, X1, XF, X5, bad, Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion,
      Finset.mem_univ, true_and, ← shiftPt_eq_append, hvert_true z hz, hz]
    by_cases h2 : ∀ e ∈ otherVertices k, dropAt (vertexDrop e) (shiftPt x0 z) ∈ JF e
    · tauto
    · push Not at h2; exact Or.inl (Or.inr h2)
  have hDcard : a ≤ D.card := by
    have h : B1.card ≤ D.card + X1.card + XF.card + X5.card :=
      (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_right
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _))
    have h' : (B1.card : Real) ≤ D.card + X1.card + XF.card + X5.card := by exact_mod_cast h
    have e : section16ThetaTwo t1 * (N : Real) ^ (k + 1) = 4 * 2 ^ k * a := by
      rw [hθ₂eq, hadef]; ring
    have h2k : a ≤ 2 ^ k * a := le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
    linarith
  -- 6. the original frame
  let H1' := (H.filter fun h => h + x0 ∈ JT).image fun h => h + x0
  let K' : Point N k → Finset (ZMod N) := fun x => section16LargeSpectrum B (x - x0) δ
  let A' : Point N k → Finset (ZMod N) := fun x =>
    Finset.univ.filter fun y => (x - x0, y) ∈ section16InducedDomain B H Y
  let f' : Point N k → ZMod N → ZMod N := fun x y => phiPrime (x - x0) y
  refine ⟨{
    D := D.image (shiftPt x0), phi := phi, H1 := H1', K := K', A := A', f := f',
    G := classFace phi x0, graph_sub := ?_, card_ge := ?_, linear := ?_, dom := ?_, ident := ?_,
    spec_U := ?_, face_U := ?_, slice_U := ?_ }⟩
  · -- graph inside Gamma
    intro p hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    exact hBG (Finset.mem_image.mpr ⟨shiftPt x0 z, hvert_true z (Finset.mem_filter.mp hz).1, rfl⟩)
  · rw [Finset.card_image_of_injective _ (shiftPt_injective x0)]; exact hDcard
  · -- Bohr linearity
    intro x hx v hv J hJ hd
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hx
    simp only [K', A', f', add_sub_cancel_right, Finset.inter_filter, Finset.inter_univ] at hd ⊢
    exact hselection.2 h (Finset.mem_filter.mp hh).1 v hv J.step hd J rfl hJ
  · -- domains
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hzB1, hzT, -, -⟩ := Finset.mem_filter.mp hz
    obtain ⟨hhH, hdom⟩ := section16GoodDomain_fibre_mem B H H Y x0 (section16Init z)
      (section16Last z) (Finset.Subset.refl _) ((appendCoordinate_init_last z).symm ▸ hzB1)
    simp only [shiftPt_init, shiftPt_last] at hzT ⊢
    exact ⟨Finset.mem_image.mpr ⟨_, Finset.mem_filter.mpr ⟨hhH, hzT⟩, rfl⟩,
      by simpa [A'] using hdom⟩
  · -- the identity
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    rw [← phiOne_eq_shiftPt phi x0 z, hid z (Finset.mem_filter.mp hz).1]
    simp only [section16PhiPrimeLift, f', shiftPt_init, shiftPt_last, add_sub_cancel_right,
      section16PhiRemainder, classRem]
    congr 2
    exact Finset.sum_congr rfl fun e he => by
      rw [translatedVertex_eq_classFace phi x0 (Finset.mem_filter.mp he).2]
  · -- the spectrum
    refine C.mono N θ' δ _ _ (fun p hp => ?_) hUT
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    obtain ⟨h, hh, hx⟩ := Finset.mem_image.mp (Finset.mem_product.mp hp1).1
    have hr : p.2 ∈ section16LargeSpectrum B h δ := by
      simpa only [K', ← hx, add_sub_cancel_right] using hp2
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(h, p.2), ?_, by rw [hx]⟩, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩
    · rw [← hx]; exact (Finset.mem_filter.mp hh).2
  · -- the faces
    refine fun e he => C.mono N θ' gamma _ _ (fun p hp => ?_) (hUF e he)
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hzB1, -, hzF, -⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨dropAt (vertexDrop e) (shiftPt x0 z),
      mem_classFaceDomain (Finset.mem_filter.mp he).2 (hvert z hzB1 e), rfl⟩, hzF e he⟩
  · -- the slices
    refine fun s => C.mono N θ' gamma _ _ (Finset.image_subset_image fun h hh => ?_) (hUS s)
    obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hh).2
    have hi := congrArg section16Init hzeq
    have hl := congrArg section16Last hzeq
    simp only [shiftPt_init, shiftPt_last, section16Init_appendCoordinate,
      section16Last_appendCoordinate] at hi hl
    rw [← hi, ← hl]
    exact (Finset.mem_filter.mp hz).2.2.2

end LeanProofs.GowersSzemeredi
