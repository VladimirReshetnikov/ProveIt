import Lib.DiscreteSeries.Bruhat.BigCell
import New.Spanning.Unfolding.Terms

/-!
# Links of isometries, the link isometry Υ_γ, and invariance under `besselU`

Let `γ` be an isometry of the form `T.splitGram`, which is made of `ϱ` hyperbolic planes and a
middle space with Gram matrix `T`. Let `A` be the span of the first `ϱ` basis vectors, and let
`New.frameImage γ` be the image of the frame `(e₁, …, e_ϱ, z)`. The link of `γ` is the set of pairs
of middle coordinates of `t` and `γ⁻¹ t`, for `t` orthogonal to `A` and `γ A`.

A filling `S` over a CM field `E` provides a prime `N = S.N`. Its middle space is `X₀ ⊥ E z_N`,
where `X₀` has an orthonormal basis indexed by `𝔰.κ` and `z = z_N` has the norm `-N`. The positive
space `X₀ ⊥ E z⁺` has the same coordinates, and `z⁺` has the norm `N`. After an exchange of the
`z_N`-coordinates of the two members of each pair (`linkSource`, `linkTarget`), the link is the
graph of an isometry `Υ_γ` (`linkIsometry`) of the positive space. The quantity `termDisc γ`
vanishes if and only if the spans of the frame and of its image under `γ` share a nonzero vector.

## Main definitions and results

* `New.Filling.link_inv_mul_mul_of_mem_besselU`,
  `New.Filling.frameDisc_frameGram_inv_mul_mul_of_mem_besselU`: the link and `New.frameDisc` are
  unchanged under `γ ↦ u⁻¹ γ u'` with `u`, `u'` in `besselU`.
* `New.NormOnePairOccursFrom.besselU_mul`, `New.NormOnePairOccursFrom.inv`: the norm-one pair
  condition is preserved by left multiplication by `besselU` and by inversion. With the invariance
  of the minors and of `termDisc`, this makes the cells stable (`New.Filling.isStable_hasCellRank`).
* `New.Filling.frameDisc_weylElem_mul`, `New.Filling.link_weylElem_mul_eq_iff`: values on the big
  cell, at `weylElem 𝔰.ϱ p * σ` with `σ` an isometry of the middle space. There the link determines
  `σ`.
* `New.Filling.linkIsometry`, `New.Filling.mem_link_iff_linkIsometry`: the isometry `Υ_γ`, and the
  link as its graph.
* `New.Filling.linkIsometry_frameImage_mulVec`, `New.Filling.mul_dotProduct_comp_indexX₀_eq_sub`:
  the link on combinations of the second frame, and the norm identity that follows.
* `New.Filling.termDisc_eq_zero_iff`: the criterion for the vanishing of `termDisc γ`.

Notions from other files:
* `New.Shape.Form.splitGram`: the Gram matrix of `ϱ` hyperbolic planes and a middle space with Gram
  matrix `T`. The basis is `e₁, …, e_ϱ`, the middle vectors, `e*₁, …, e*_ϱ` (indices `New.eStar`).
* `New.Shape.Form.besselU`: the isometries that are block upper unitriangular for this basis.
* `New.Shape.Form.frameGram`: the `(ϱ + 1) × (ϱ + 1)` matrix of the products `h(f_j, γ f_l)` of the
  frame `f` with its image under `γ`, where `h` is the form `T.splitGram`.
* `New.Filling`: arithmetic data over a CM field `E`, among them the prime `S.N`. The matrix
  `S.ratMiddle E` is the Gram matrix of `X₀ ⊥ E z_N`, `S.ratGram` is its `splitGram`, `S.G E` is the
  group of isometries of `S.ratGram`, and `S.frameProducts γ` is the frame Gram matrix of `γ`.
* `New.frameDisc`: for a matrix of size `ϱ + 1` with leading minors `D_l`, the quantity
  `|D_{ϱ+1}|² - N² |D_ϱ|²`. Its value at `S.N` and the frame Gram matrix of `γ` is
  `New.Filling.termDisc γ`.
* `New.NormOnePairOccursFrom j γ`, the condition that a norm-one pair occurs from `j`: there is a
  `c` with `c c̄ = 1` such that, for every frame index `a ≥ j` (counted from `0`), the flags of `f`
  and `γ f` share a vector with leading coefficients `c` and `1` at `a`.
-/

noncomputable section

/-!
## Invariance of links and cells under the unipotent group

A vector `t` is orthogonal to `A` and `γ A` iff the coordinates at the `e*_a` of `t` and `γ⁻¹ t`
vanish. This describes the link in coordinates and gives its invariance under `besselU`.
-/

section StableCells
open Matrix Fin Fintype New.Floors FloorGroups Sum Function

namespace New

variable {F : Type*} [CommRing F] [StarRing F] {𝔰 : Shape} {T : Shape.Form 𝔰 F}

omit [StarRing F] in
/-- The form `T.splitGram` exchanges the first and last blocks of coordinates of `v` and applies `T`
to the middle block. -/
lemma splitGram_mulVec (v : 𝔰.BesselIndex → F) :
    T.splitGram *ᵥ v = (fun a : Fin 𝔰.ϱ ↦ v (eStar a)) ⊕ᵥ
      (T *ᵥ (fun b : 𝔰.MiddleIndex ↦ v (inr (inl b))) ⊕ᵥ fun a : Fin 𝔰.ϱ ↦ v (inl a)) := by
  simp [funext_iff, splitGram, fromBlocks_mulVec, comp_def]

/-- The matrix `linkMatrix γ` sends `t` to the pair of the middle blocks of `t` and of `γ⁻¹ t`. -/
@[simp ↓]
lemma linkMatrix_mulVec {γ : T.G} (t : 𝔰.BesselIndex → F) :
    linkMatrix γ *ᵥ t = (fun b : 𝔰.MiddleIndex ↦ t (inr (inl b))) ⊕ᵥ
      fun b : 𝔰.MiddleIndex ↦ (γ⁻¹.val.val *ᵥ t) (inr (inl b)) := by
  ext (b | b) <;> simp [mulVec_eq_sum, linkMatrix, Matrix.one_apply]

/-- A vector `t` is orthogonal to `A = ⟨e₁, …, e_ϱ⟩` and to `γ A` (so to the span `A + γ A` of the
columns of `isotropicFramePair γ`) iff the last `ϱ` coordinates, those at the `e*_a`, of both `t`
and `γ⁻¹ t` vanish. -/
@[simp ↓]
lemma orthogonal_isotropicFramePair_iff {γ : T.G} {t : 𝔰.BesselIndex → F} :
    t ∈ ((isotropicFramePair γ)ᴴ * T.splitGram).mulVecLin.ker ↔
      (∀ a : Fin 𝔰.ϱ, t (eStar a) = 0) ∧ ∀ a : Fin 𝔰.ϱ, (γ⁻¹.val.val *ᵥ t) (eStar a) = 0 := by
  -- The products of `t` with the `e_a`, then with the `γ e_a`.
  have h_rows : ((isotropicFramePair γ)ᴴ * T.splitGram) *ᵥ t =
      (fun a : Fin 𝔰.ϱ ↦ (T.splitGram *ᵥ t) (inl a)) ⊕ᵥ
        fun a : Fin 𝔰.ϱ ↦ ((γ.val.valᴴ * T.splitGram) *ᵥ t) (inl a) := by
    simp only [← mulVec_mulVec]
    ext (a | a) <;> simp [mulVec_apply_eq_sum, Matrix.one_apply, apply_ite star]
  -- As `γ` is unitary, `γᴴ` moves onto `t` as `γ⁻¹`; the form then picks the coordinates `eStar a`.
  rw [LinearMap.mem_ker, mulVecLin_apply, h_rows, ← U.form_mul_inv_eq γ, ← mulVec_mulVec]
  simp [-mulVec_mulVec, splitGram_mulVec, funext_iff]

/-- The link in coordinates: a pair `p = (y, y')` of middle vectors is in the link of `γ` iff,
for some `a`, `γ` maps the vector with blocks `(a, y', 0)` to a vector with last two blocks
`(y, 0)`. -/
lemma mem_link {γ : T.G} {p : 𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → F} :
    p ∈ link γ ↔ ∃ a : Fin 𝔰.ϱ → F, (γ.val.val *ᵥ (a ⊕ᵥ (p ∘ inr ⊕ᵥ 0))) ∘ inr = p ∘ inl ⊕ᵥ 0 := by
  constructor
  · rintro ⟨t, h_orth, rfl⟩
    obtain ⟨ht, hγt⟩ := orthogonal_isotropicFramePair_iff.1 h_orth
    -- The blocks of `γ⁻¹ t` are a free one, the second member of the pair, and `0`.
    have h_blocks : (fun a : Fin 𝔰.ϱ ↦ (γ⁻¹.val.val *ᵥ t) (inl a)) ⊕ᵥ
        ((linkMatrix γ *ᵥ t) ∘ inr ⊕ᵥ 0) = γ⁻¹.val.val *ᵥ t := by
      ext (a | b | a)
      exacts [rfl, by simp, (hγt a).symm]
    refine ⟨fun a ↦ (γ⁻¹.val.val *ᵥ t) (inl a), ?_⟩
    rw [mulVecLin_apply, h_blocks]
    ext (b | a) <;> simp [ht]
  · rintro ⟨a, ha⟩
    refine ⟨γ.val.val *ᵥ (a ⊕ᵥ (p ∘ inr ⊕ᵥ 0)), orthogonal_isotropicFramePair_iff.2
      ⟨fun a' ↦ congrFun ha (inr a'), by simp⟩, ?_⟩
    ext (b | b)
    exacts [by simpa using congrFun ha (inl b), by simp]

/-- Let `f = (e₁, …, e_ϱ, z)` be the frame. The condition `NormOnePairOccursFrom j γ` says that, for
some `c` with `c c̄ = 1` and every index `a ≥ j`, there are combinations of `f` and of `γ f` that
are equal, have no coefficients above `a`, and have the coefficients `c` and `1` at `a`. If it holds
for `γ`, then it holds for `γ⁻¹`. -/
lemma NormOnePairOccursFrom.inv {j : ℕ} {γ : T.G} (h_occurs : NormOnePairOccursFrom j γ) :
    NormOnePairOccursFrom j γ⁻¹ := by
  -- Apply `γ⁻¹` to the shared vector, exchange the two sides and scale by `star c = c⁻¹`.
  obtain ⟨c, hc, h_shared⟩ := h_occurs
  refine ⟨star c, by simpa [mul_comm] using hc, fun a ha ↦ ?_⟩
  obtain ⟨x, y, hxy, hx_lead, hy_lead, h_above⟩ := h_shared a ha
  have hyx : frameImage 1 *ᵥ y = frameImage γ⁻¹.val.val *ᵥ x := by
    simp [frameImage_mulVec γ.val.val⁻¹, hxy, frameImage_mulVec γ.val.val]
  refine ⟨star c • y, star c • x, ?_, by simp [hy_lead], ?_, fun b hb ↦ by simp [h_above b hb]⟩
  · rw [mulVec_smul, mulVec_smul, hyx]
  · simp [hx_lead, mul_comm, hc]

/-- Let `f = frameImage 1` be the frame `(e₁, …, e_ϱ, z)`, and let `frameImage γ` be its image
`γ f`. Suppose `PairOccursAt γ c 1 a` holds for each index `a ≥ j`: some combination of `f` equals
some combination of `γ f`, with no coefficients above `a` and with coefficients `c` and `1` at `a`.
Then for every `y` there are `x` and `y'` with `frameImage 1 *ᵥ x = frameImage γ *ᵥ y'` and
`y' a = y a` for all `a ≥ j`. -/
lemma Filling.exists_frameImage_eq_of_pairOccursAt {γ : T.G} {j : Fin (𝔰.ϱ + 2)} {c : F}
    (h_shared : ∀ a : Fin (𝔰.ϱ + 1), j.val ≤ a.val → PairOccursAt γ c 1 a) (y : Fin (𝔰.ϱ + 1) → F) :
    ∃ x y' : Fin (𝔰.ϱ + 1) → F, (∀ a : Fin (𝔰.ϱ + 1), j.val ≤ a.val → y' a = y a) ∧
      frameImage 1 *ᵥ x = frameImage γ.val.val *ᵥ y' := by
  -- Descending induction on `j`: the coefficients `Y` of a vector shared at `j` are `1` at `j` and
  -- `0` above, so a multiple of them corrects the entry at `j` and leaves the later ones alone.
  induction j using reverseInduction with
  | last => exact ⟨0, 0, fun a ha ↦ absurd a.is_lt (not_lt.2 ha), by simp⟩
  | cast j ih =>
    obtain ⟨x, z, hzy, hxz⟩ : ∃ x z : Fin (𝔰.ϱ + 1) → F,
        (∀ a : Fin (𝔰.ϱ + 1), j.succ.val ≤ a.val → z a = y a) ∧
        frameImage 1 *ᵥ x = frameImage γ.val.val *ᵥ z :=
      ih fun a ha ↦ h_shared a (le_of_lt ha)
    obtain ⟨X, Y, hXY, -, hY_one, h_above⟩ : ∃ X Y : Fin (𝔰.ϱ + 1) → F,
        frameImage 1 *ᵥ X = frameImage γ.val.val *ᵥ Y ∧ X j = c ∧ Y j = 1 ∧
          ∀ b > j, X b = 0 ∧ Y b = 0 := h_shared j le_rfl
    refine ⟨x + (y - z) j • X, z + (y - z) j • Y, fun a ha ↦ ?_, ?_⟩
    · obtain rfl | hlt : j = a ∨ j < a := eq_or_lt_of_le ha
      · simp [hY_one]
      · simp [h_above a hlt, hzy a hlt]
    · simp [mulVec_add, mulVec_smul, hxz, hXY]

/-- Let `γ` satisfy the norm-one pair condition from some `j ≤ ϱ + 1` (for some `c` of norm `1`, the
flags of the frame `f = (e₁, …, e_ϱ, z)` and of `γ f` share a vector with leading coefficients `c`
and `1` at each index `a ≥ j`). Then for every `y` the spans of `f` and `γ f` share a vector whose
coefficients `y'` in `γ f` agree with `y` at the indices `a ≥ j`. -/
lemma Filling.exists_frameImage_eq_of_normOnePairOccursFrom {γ : T.G} {j : Fin (𝔰.ϱ + 2)}
    (h_occurs : NormOnePairOccursFrom j γ) (y : Fin (𝔰.ϱ + 1) → F) :
    ∃ x y' : Fin (𝔰.ϱ + 1) → F, (∀ a : Fin (𝔰.ϱ + 1), j.val ≤ a.val → y' a = y a) ∧
      frameImage 1 *ᵥ x = frameImage γ.val.val *ᵥ y' :=
  let ⟨_, _, h_shared⟩ := h_occurs
  exists_frameImage_eq_of_pairOccursAt h_shared y

/-- Let `f = (e₁, …, e_ϱ, z)` be the frame. The norm-one pair condition from `j` says that there is
one `c` with `c c̄ = 1` such that, for every index `a ≥ j`, some combination of `f` equals some
combination of `γ f`, both with no coefficients above `a` and with the coefficients `c` and `1` at
`a`. If it holds for `γ` and `u` is in `besselU`, the group of the isometries that are block upper
unitriangular for the basis `e₁, …, e_ϱ`, middle vectors, `e*₁, …, e*_ϱ`, then it holds for
`u γ`. -/
lemma NormOnePairOccursFrom.besselU_mul {j : ℕ} {γ u : T.G} (hu : u ∈ besselU)
    (h_occurs : NormOnePairOccursFrom j γ) :
    NormOnePairOccursFrom j (u * γ) := by
  -- `u` acts on the span of the frame by the unitriangular matrix `frameMatrix u`.
  obtain ⟨c, hc, h_shared⟩ := h_occurs
  refine ⟨c, hc, fun a ha ↦ ?_⟩
  obtain ⟨x, y, hxy, hx_lead, hy_lead, h_above⟩ : ∃ x y : Fin (𝔰.ϱ + 1) → F,
      frameImage 1 *ᵥ x = frameImage γ.val.val *ᵥ y ∧ x a = c ∧ y a = 1 ∧
        ∀ b > a, x b = 0 ∧ y b = 0 := h_shared a ha
  -- `x` vanishes above `a`, so `frameMatrix u *ᵥ x` has the same entries as `x` at `a` and above.
  have h_entry (b : Fin (𝔰.ϱ + 1)) (hb : a ≤ b) : (frameMatrix u *ᵥ x) b = x b := by
    have h_off (i : Fin (𝔰.ϱ + 1)) (hi : i ≠ b) : frameMatrix u b i * x i = 0 := by
      obtain h_lt | h_gt := lt_or_gt_of_ne hi
      · simp [frameMatrix_unitriangular hu b i h_lt.le, hi.symm]
      · simp [h_above i (hb.trans_lt h_gt)]
    simp [mulVec_apply_eq_sum, sum_eq_single b h_off, frameMatrix_unitriangular hu b b le_rfl]
  refine ⟨frameMatrix u *ᵥ x, y, ?_, (h_entry a le_rfl).trans hx_lead, hy_lead,
    fun b hb ↦ by simpa only [h_entry b hb.le] using h_above b hb⟩
  calc frameImage 1 *ᵥ frameMatrix u *ᵥ x
    _ = u.val.val *ᵥ frameImage 1 *ᵥ x := by
      simp [← submatrix_mul_besselFrame, frameImage_mulVec u.val.val, hu]
    _ = u.val.val *ᵥ frameImage γ.val.val *ᵥ y := by rw [hxy]
    _ = frameImage (u * γ).val.val *ᵥ y := by
      simp [frameImage_mulVec γ.val.val, frameImage_mulVec (u.val.val * _), Matrix.mul_assoc]

/-- An element of the unipotent group `besselU` fixes the last two blocks of coordinates of a vector
whose last block vanishes. -/
lemma mulVec_apply_inr_of_mem_besselU {u : T.G} (hu : u ∈ besselU) {t : 𝔰.BesselIndex → F}
    (ht : ∀ a : Fin 𝔰.ϱ, t (eStar a) = 0) (i : 𝔰.MiddleIndex ⊕ Fin 𝔰.ϱ) :
    (u.val.val *ᵥ t) (inr i) = t (inr i) := by
  rcases i with b | a <;> simp [mulVec_apply_eq_sum, apply_inr_of_mem_besselU hu, ht]

/-- Let `u` and `u'` lie in `besselU`, the group of the isometries that are block upper
unitriangular for the basis `e₁, …, e_ϱ`, middle vectors, `e*₁, …, e*_ϱ`, and so induce the identity
on the middle space. Then the link of `u⁻¹ γ u'` is the link of `γ`. -/
lemma Filling.link_inv_mul_mul_of_mem_besselU {γ u u' : T.G} (hu : u ∈ besselU)
    (hu' : u' ∈ besselU) : link (u⁻¹ * γ * u') = link γ := by
  -- `t ↦ v *ᵥ t` carries the vectors that define one link to those that define the other.
  have h_le {v w g : T.G} (hv : v ∈ besselU) (hw : w ∈ besselU) : link g ≤ link (v * g * w⁻¹) := by
    rintro _ ⟨t, h_orth, rfl⟩
    obtain ⟨ht, hgt⟩ : (∀ a : Fin 𝔰.ϱ, t (eStar a) = 0) ∧
        ∀ a : Fin 𝔰.ϱ, (g⁻¹.val.val *ᵥ t) (eStar a) = 0 :=
      orthogonal_isotropicFramePair_iff.1 h_orth
    have h_inv : (v * g * w⁻¹)⁻¹.val.val *ᵥ v.val.val *ᵥ t = w.val.val *ᵥ g⁻¹.val.val *ᵥ t := by
      simp [← mulVec_mulVec, inv_mulVec_eq_vec rfl]
    refine ⟨v.val.val *ᵥ t, orthogonal_isotropicFramePair_iff.2 ⟨fun a ↦ ?_, fun a ↦ ?_⟩, ?_⟩
    · rw [mulVec_apply_inr_of_mem_besselU hv ht, ht]
    · rw [h_inv, mulVec_apply_inr_of_mem_besselU hw hgt, hgt]
    · simp only [mulVecLin_apply, linkMatrix_mulVec, h_inv,
        mulVec_apply_inr_of_mem_besselU hv ht, mulVec_apply_inr_of_mem_besselU hw hgt]
  exact le_antisymm (by simpa [mul_assoc] using h_le (g := u⁻¹ * γ * u') hu hu')
    (by simpa using h_le (g := γ) (inv_mem hu) (inv_mem hu'))

/-- For `u` and `u'` in the unipotent group `besselU`, the quantity `New.frameDisc N`, that is
`|D_{ϱ+1}|² - N² |D_ϱ|²` in the leading minors `D_l`, of the frame Gram matrix is the same for
`u⁻¹ γ u'` as for `γ`. -/
lemma Filling.frameDisc_frameGram_inv_mul_mul_of_mem_besselU {F : Type} [CommRing F] [StarRing F]
    {T : 𝔰.Form F} {γ u u' : T.G} (hu : u ∈ besselU) (hu' : u' ∈ besselU) (N : F) :
    frameDisc N (T.frameGram (u⁻¹ * γ * u').val) = frameDisc N (T.frameGram γ) := by
  -- The determinant is the last of the leading minors.
  have h_det : det (T.frameGram (u⁻¹ * γ * u').val) = det (T.frameGram γ) :=
    leadingMinor_frameGram_besselU_mul hu hu' ⊤
  simp only [frameDisc, h_det, leadingMinor_frameGram_besselU_mul hu hu']

/-- Let `D_l` be the leading minors of the frame Gram matrix `S.frameProducts γ`, the matrix of the
products `h(f_b, γ f_l)` of the frame `f = (e₁, …, e_ϱ, z_N)` with its image under `γ`, so that
`S.termDisc γ = |D_{ϱ+1}|² - N² |D_ϱ|²`. The cell of rank `j` consists of the `γ` in `S.G E` such
that: for some `c` with `c c̄ = 1` and every index `a ≥ j`, a combination of `f` equals one of
`γ f`, both with no coefficients above `a` and with `c`, `1` at `a`; `D_j ≠ 0`; and
`S.termDisc γ ≠ 0` exactly if `j = ϱ + 1`. This cell is stable: for `u`, `u'` in the unipotent group
`besselU`, it contains `u⁻¹ γ u'` if and only if it contains `γ`. -/
lemma Filling.isStable_hasCellRank {E : Type} [Field E] [CMType E] {S : Filling E 𝔰}
    (j : Fin (𝔰.ϱ + 1 + 1)) : S.IsStable {γ : S.G E | S.HasCellRank j γ} := by
  intro u hu u' hu' γ
  -- The norm-one pair condition survives inversion and left multiplication by `besselU`, hence also
  -- right multiplication; the minors and `termDisc` do not change.
  have h_occurs : NormOnePairOccursFrom j.val (u⁻¹ * γ * u') ↔ NormOnePairOccursFrom j.val γ :=
    ⟨fun h ↦ by simpa [mul_assoc] using ((h.besselU_mul hu).inv.besselU_mul hu').inv, fun h ↦ by
      simpa [mul_assoc] using ((h.besselU_mul (inv_mem hu)).inv.besselU_mul (inv_mem hu')).inv⟩
  have h_minor : leadingMinor (S.frameProducts (u⁻¹ * γ * u')) j =
      leadingMinor (S.frameProducts γ) j := leadingMinor_frameGram_besselU_mul hu hu' j
  have h_disc : S.termDisc (u⁻¹ * γ * u') = S.termDisc γ :=
    frameDisc_frameGram_inv_mul_mul_of_mem_besselU hu hu' _
  simp only [Set.mem_ofPred_eq, hasCellRank_iff, h_occurs, h_minor, h_disc]

/-! ### The big cell -/

/-- Over a field `A` with involution, let `T.splitGram` be hermitian and invertible, with isometry
group `T.G`. Let `σ` fix the hyperbolic planes, and let `w_p = weylElem 𝔰.ϱ p` send `e_a` to
`p a • e*_a`. Let `t = T.frameGram σ 𝔰.top 𝔰.top` be the product of the last frame vector `z` with
`σ z`, and let `d` be the product of the first `ϱ` units of `p`. Let `T.frameGram (w_p σ)` be the
matrix of products of the frame `(e₁, …, e_ϱ, z)` with its image under `w_p σ`. Then `frameDisc N`
of this matrix, that is `|D_{ϱ+1}|² - N² |D_ϱ|²` in its leading minors `D_l`, equals
`d d̄ (t t̄ - N²)`. -/
theorem Filling.frameDisc_weylElem_mul {A : Type} [Field A] [StarRing A] {T : 𝔰.Form A}
    [IsHermitianUnit T.splitGram] {σ : T.G} {p : ℕ → Aˣ} (hσ : σ ∈ floorGroup 𝔰.ϱ) (N : A) :
    let t : A := T.frameGram σ 𝔰.top 𝔰.top
    let d : A := ∏ a : Fin 𝔰.ϱ, (p a).val
    frameDisc N (T.frameGram (weylElem 𝔰.ϱ p * σ).val) = d * star d * (t * star t - N ^ 2) := by
  intro t d
  -- The matrix is diagonal, with entries `p a` and `t`.
  have h_det : (T.frameGram (weylElem 𝔰.ϱ p * σ).val).det = d * t := by
    rw [frameGram_weylElem_mul hσ]
    simp [prod_univ_castSucc, d, t]
  have h_minor : leadingMinor (T.frameGram (weylElem 𝔰.ϱ p * σ).val) 𝔰.top.castSucc = d := by
    rw [frameGram_weylElem_mul hσ]
    simp [leadingMinor, submatrix_diagonal, castLE_injective, snoc, d]
  rw [frameDisc, h_det, h_minor, star_mul']
  ring

/-- Over a field with involution, let `T.splitGram` be hermitian and invertible. Let `ρ` fix the
hyperbolic planes, and let `w_r = weylElem 𝔰.ϱ r` send `e_a` to `r a • e*_a`. The link of `w_r ρ` is
the graph of the middle block of `ρ`: a pair lies in it if and only if its first member is the image
of the second under this block. -/
lemma Filling.mem_link_weylElem_mul_iff {A : Type} [Field A] [StarRing A] {T : 𝔰.Form A}
    [IsHermitianUnit T.splitGram] {ρ : T.G} (hρ : ρ ∈ floorGroup 𝔰.ϱ) (r : ℕ → Aˣ)
    {v : 𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → A} :
    v ∈ link (weylElem 𝔰.ϱ r * ρ) ↔ ρ.val.val.toBlocks₂₂.toBlocks₁₁ *ᵥ (v ∘ inr) = v ∘ inl := by
  -- `mem_link` asks for an `a` with one block of `w_r ρ` sending it to `0`: `a = 0` will do.
  have h_ker (M : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) A) : ∃ a, M *ᵥ a = 0 := ⟨0, mulVec_zero M⟩
  rw [mem_link, coe_weylElem_mul hρ]
  simp [← elim_add_add, elim_eq_iff, h_ker, fromBlocks_mulVec]

/-- Over a field with involution, let `T.splitGram` be hermitian and invertible. Let `σ`, `τ` fix
the hyperbolic planes, and let `w_p = weylElem 𝔰.ϱ p` send `e_a` to `p a • e*_a`. Then `w_p σ` and
`w_q τ` have the same link exactly when `σ = τ`. -/
theorem Filling.link_weylElem_mul_eq_iff {A : Type} [Field A] [StarRing A] {T : 𝔰.Form A}
    [IsHermitianUnit T.splitGram] {σ τ : T.G} {p q : ℕ → Aˣ} (hσ : σ ∈ floorGroup 𝔰.ϱ)
    (hτ : τ ∈ floorGroup 𝔰.ϱ) :
    link (weylElem 𝔰.ϱ p * σ) = link (weylElem 𝔰.ϱ q * τ) ↔ σ = τ := by
  -- The link of `w_p σ` is the graph of the middle block of `σ`, and this block determines `σ`.
  constructor
  · intro h_link
    have h_mid : σ.val.val.toBlocks₂₂.toBlocks₁₁ = τ.val.val.toBlocks₂₂.toBlocks₁₁ := by
      refine ext_iff_mulVec.2 fun b ↦ ?_
      -- The pair of `τ b` and `b` lies in the link of `w_q τ`, hence in that of `w_p σ`.
      have h_mem : (τ.val.val.toBlocks₂₂.toBlocks₁₁ *ᵥ b) ⊕ᵥ b ∈ link (weylElem 𝔰.ϱ p * σ) := by
        simp [h_link, mem_link_weylElem_mul_iff hτ]
      simpa using (mem_link_weylElem_mul_iff hσ p).1 h_mem
    refine mul_left_cancel (a := weylElem 𝔰.ϱ p) (Subtype.ext (Units.ext ?_))
    rw [coe_weylElem_mul hσ, coe_weylElem_mul hτ, h_mid]
  · rintro rfl
    ext v
    simp [mem_link_weylElem_mul_iff, hσ]

end New

end StableCells

/-!
## The link as an isometry

The middle form is that of `X₀ ⊥ E z_N`, where `z_N` has the norm `-N`.

A vector `y` orthogonal to `A` and `γ A` gives two classes in `A^⊥ / A = X₀ ⊥ E z_N`, those of `y`
and of `γ⁻¹ y`.
-/

section LinkIsometry

open Matrix Module Fin Sum Function

namespace New

/-- Over a field with involution a matrix and its conjugate transpose have the same rank. -/
lemma rank_conjTranspose_eq {F m n : Type} [Field F] [StarRing F] [Fintype m] [Fintype n]
    (A : Matrix m n F) : Aᴴ.rank = A.rank := by
  -- `Aᴴ` is the transpose of `A.map star`, and `star` is a semilinear bijection that carries the
  -- span of the columns of `A` onto the span of those of `A.map star`, so keeps its dimension.
  let e : (m → F) ≃ₗ⋆[F] (m → F) := starLinearEquiv F
  let W : Submodule F (m → F) := Submodule.span F (Set.range A.col)
  have h_span : Submodule.span F (Set.range (A.map star).col) = W.map e.toLinearMap := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have h_rank : Module.rank F W = Module.rank F (W.map e.toLinearMap) :=
    rank_eq_of_equiv_equiv star (e.submoduleMap W).toAddEquiv star_involutive.bijective
      (e.submoduleMap W).map_smulₛₗ
  calc Aᴴ.rank = (A.map star).rank := rank_transpose (A.map star)
    _ = finrank F (W.map e.toLinearMap) := by rw [rank_eq_finrank_span_cols, h_span]
    _ = finrank F W := (congrArg Cardinal.toNat h_rank).symm
    _ = A.rank := (rank_eq_finrank_span_cols A).symm

/-- The columns of two matrices set side by side span the sum of the two column spaces. -/
lemma colSpan_fromCols {K m n₁ n₂ : Type*} [CommRing K] [Fintype n₁] [Fintype n₂]
    (A : Matrix m n₁ K) (B : Matrix m n₂ K) : colSpan (A.fromCols B) = colSpan A ⊔ colSpan B := by
  ext v
  simp only [Submodule.mem_sup, LinearMap.mem_range, mulVecLin_apply, exists_exists_eq_and]
  exact ⟨fun ⟨c, hc⟩ ↦ ⟨c ∘ inl, c ∘ inr, by rw [← hc, fromCols_mulVec]⟩,
    fun ⟨a, b, hab⟩ ↦ ⟨a ⊕ᵥ b, (fromCols_mulVec_sumElim A B a b).trans hab⟩⟩

namespace Filling

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}

/-- The space `M A` spanned by the columns `M e_1, …, M e_ϱ`, where `A = ⟨e_1, …, e_ϱ⟩`. -/
def isotropicSpan (M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) : Submodule E (𝔰.BesselIndex → E) :=
  colSpan ((frameImage M).submatrix id castSucc)

/-- The space `I_γ = A ∩ γ A`, where `A = ⟨e_1, …, e_ϱ⟩`. -/
def commonIsotropic (γ : S.G E) : Submodule E (𝔰.BesselIndex → E) :=
  isotropicSpan 1 ⊓ isotropicSpan γ.val.val

/-- The orthogonal complement `(A + γ A)^⊥`, where `A = ⟨e_1, …, e_ϱ⟩`, for the form
`S.ratGram = (S.ratMiddle E).splitGram` of `ϱ` hyperbolic planes and the space `X₀ ⊥ E z_N`. -/
def isotropicPerp (γ : S.G E) : Submodule E (𝔰.BesselIndex → E) :=
  ((isotropicFramePair γ)ᴴ * S.ratGram).mulVecLin.ker

variable (S) in
/-- The Gram matrix of the positive space `X₀ ⊥ E z⁺`, where `X₀` has an orthonormal basis and `z⁺`
has the norm `S.N`, the prime of the filling `S`. -/
def positiveGram : 𝔰.Form E := diagonal (1 ⊕ᵥ fun _ : Unit ↦ S.N)

variable (E 𝔰) in
/-- The map that sends the pair of classes `(y₀ + λ' z_N, y₀' + λ z_N)` to `y₀ + λ z⁺`. -/
def linkSource : (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E) →ₗ[E] (𝔰.MiddleIndex → E) :=
  .funLeft E E (Sum.elim (inl ∘ inl) (inr ∘ inr))

variable (E 𝔰) in
/-- The map that sends the pair of classes `(y₀ + λ' z_N, y₀' + λ z_N)` to `y₀' + λ' z⁺`. -/
def linkTarget : (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E) →ₗ[E] (𝔰.MiddleIndex → E) :=
  .funLeft E E (Sum.elim (inr ∘ inl) (inl ∘ inr))

omit [CMType E] in
/-- A pair `p` of classes (a function on `𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex`) is determined by its two
images `linkSource E 𝔰 p` and `linkTarget E 𝔰 p` in `X₀ ⊥ E z⁺`. -/
lemma eq_of_linkSource_eq_of_linkTarget_eq {p q : 𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E}
    (h_source : linkSource E 𝔰 p = linkSource E 𝔰 q)
    (h_target : linkTarget E 𝔰 p = linkTarget E 𝔰 q) : p = q := by
  ext ((j | z) | (j | z))
  exacts [congrFun h_source (inl j), congrFun h_target (inr z), congrFun h_target (inl j),
    congrFun h_source (inr z)]

/-- The form `S.positiveGram` of `X₀ ⊥ E z⁺` in coordinates: `𝔰.κ` indexes an orthonormal basis of
`X₀`, and `z⁺`, at the index `inr ()`, has the norm `S.N`. -/
lemma dotProduct_positiveGram_mulVec_eq_sum_add (a b : 𝔰.MiddleIndex → E) :
    star a ⬝ᵥ S.positiveGram *ᵥ b =
      ∑ j : 𝔰.κ, star (a (inl j)) * b (inl j) + S.N * (star (a (inr ())) * b (inr ())) := by
  simp [positiveGram, dotProduct, mulVec_diagonal, mul_left_comm]

/-- The form `S.ratMiddle E` of `X₀ ⊥ E z_N` in coordinates: `𝔰.κ` indexes an orthonormal basis of
`X₀`, and `z_N`, at the index `inr ()`, has the norm `-S.N`. -/
lemma dotProduct_ratMiddle_mulVec_eq_sum_sub (a b : 𝔰.MiddleIndex → E) :
    star a ⬝ᵥ S.ratMiddle E *ᵥ b =
      ∑ j : 𝔰.κ, star (a (inl j)) * b (inl j) - S.N * (star (a (inr ())) * b (inr ())) := by
  simp [Shape.middleGram, dotProduct, mulVec, mul_left_comm, sub_eq_add_neg,
    Matrix.one_apply]

/-- The form of the space `X₀ ⊥ E z⁺` is anisotropic: only the zero vector has norm `0`. -/
lemma eq_zero_of_positiveGram_form_eq_zero {a : 𝔰.MiddleIndex → E}
    (h_norm : star a ⬝ᵥ S.positiveGram *ᵥ a = 0) : a = 0 := by
  let v : NumberField.InfinitePlace E := Classical.ofNonempty
  -- At an infinite place the norm is a sum of squares with positive weights.
  have h_sum : ∑ j : 𝔰.κ, ‖Φ v (a (inl j))‖ ^ 2 + S.N * ‖Φ v (a (inr ()))‖ ^ 2 = 0 := by
    simpa [dotProduct_positiveGram_mulVec_eq_sum_add, ← Complex.ofReal_inj, Complex.conj_mul'] using
      congrArg (Φ v) h_norm
  rw [add_eq_zero_iff_of_nonneg (by positivity) (by positivity),
    Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _] at h_sum
  simpa [funext_iff, Unique.forall_iff, S.N_prime.ne_zero] using h_sum

/-! ### The rank of the link and the link isometry -/

/-- A vector `y` is orthogonal to `A` and `γ A`, where `A` is the span of `e_1, …, e_ϱ`, if and only
if the coordinates of `y` and of `γ⁻¹ y` at the dual basis vectors `e*_a` vanish. -/
lemma mem_isotropicPerp {γ : S.G E} {y : 𝔰.BesselIndex → E} : y ∈ isotropicPerp γ ↔
    (∀ a : Fin 𝔰.ϱ, y (eStar a) = 0) ∧ ∀ a : Fin 𝔰.ϱ, (γ⁻¹.val.val *ᵥ y) (eStar a) = 0 :=
  orthogonal_isotropicFramePair_iff

/-- The link of `γ` is the image of `(A + γ A)^⊥` under the map `linkMatrix γ`, which sends `y` to
the pair of the middle coordinates of `y` and of `γ⁻¹ y`. -/
lemma link_eq_map (γ : S.G E) : link γ = (isotropicPerp γ).map (linkMatrix γ).mulVecLin := rfl

/-- A pair lies in the link of `γ` if and only if it consists of the middle coordinates of `y` and
of `γ⁻¹ y` for some `y` in `(A + γ A)^⊥`. -/
lemma mem_link_iff_exists_mem_isotropicPerp {γ : S.G E} {p : 𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E} :
    p ∈ link γ ↔ ∃ y ∈ isotropicPerp γ, linkMatrix γ *ᵥ y = p := Submodule.mem_map

/-- The classes in `X₀ ⊥ E z_N` of `y` and `γ⁻¹ y`, for `y` orthogonal to `A` and `γ A`, form a
pair in the link of `γ`. -/
lemma linkMatrix_mulVec_mem_link {γ : S.G E} {y : 𝔰.BesselIndex → E} (hy : y ∈ isotropicPerp γ) :
    linkMatrix γ *ᵥ y ∈ link γ := ⟨y, hy, rfl⟩

/-- The map `linkSource` sends the pair `linkMatrix γ *ᵥ y` of middle blocks of `y` and `γ⁻¹ y` to
`y₀ + λ z⁺`, where `y₀` are the coordinates of `y` in `X₀` (indices `𝔰.indexX₀`) and `λ` is the
coordinate of `γ⁻¹ y` at `z_N` (index `𝔰.z`). -/
lemma linkSource_linkMatrix_mulVec {γ : S.G E} (y : 𝔰.BesselIndex → E) :
    linkSource E 𝔰 (linkMatrix γ *ᵥ y) =
      (y ∘ 𝔰.indexX₀) ⊕ᵥ fun _ : Unit ↦ (γ⁻¹.val.val *ᵥ y) 𝔰.z := by
  rw [linkMatrix_mulVec]
  ext (i | i) <;> rfl

/-- The map `linkTarget` sends the pair `linkMatrix γ *ᵥ y` of middle blocks of `y` and `γ⁻¹ y` to
`y₀' + λ' z⁺`, where `y₀'` are the coordinates of `γ⁻¹ y` in `X₀` (indices `𝔰.indexX₀`) and `λ'`
is the coordinate of `y` at `z_N` (index `𝔰.z`). -/
lemma linkTarget_linkMatrix_mulVec {γ : S.G E} (y : 𝔰.BesselIndex → E) :
    linkTarget E 𝔰 (linkMatrix γ *ᵥ y) =
      ((γ⁻¹.val.val *ᵥ y) ∘ 𝔰.indexX₀) ⊕ᵥ fun _ : Unit ↦ y 𝔰.z := by
  rw [linkMatrix_mulVec]
  ext (i | i) <;> rfl

/-- If `y` and `y'` lie in `A^⊥`, that is, their coordinates at the `e*_a` vanish, then their
product for the form `S.ratGram` of the whole space is the product of their middle coordinates for
the form `S.ratMiddle E` of `A^⊥ / A = X₀ ⊥ E z_N`. -/
lemma ratGram_form_of_eStar_eq_zero {y y' : 𝔰.BesselIndex → E}
    (hy : ∀ a : Fin 𝔰.ϱ, y (eStar a) = 0) (hy' : ∀ a : Fin 𝔰.ϱ, y' (eStar a) = 0) :
    star y ⬝ᵥ S.ratGram *ᵥ y' =
      star (fun b : 𝔰.MiddleIndex ↦ y (inr (inl b))) ⬝ᵥ
        S.ratMiddle E *ᵥ fun b : 𝔰.MiddleIndex ↦ y' (inr (inl b)) := by
  simp [splitGram_mulVec, dotProduct, hy, hy']

/-- For pairs `p`, `q` in the link of `γ`, the product in the positive space `X₀ ⊥ E z⁺` of their
images under `linkSource` equals that of their images under `linkTarget`. -/
lemma form_linkSource_eq_form_linkTarget {γ : S.G E} {p q : 𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E}
    (hp : p ∈ link γ) (hq : q ∈ link γ) :
    star (linkSource E 𝔰 p) ⬝ᵥ S.positiveGram *ᵥ linkSource E 𝔰 q =
      star (linkTarget E 𝔰 p) ⬝ᵥ S.positiveGram *ᵥ linkTarget E 𝔰 q := by
  obtain ⟨y, hy_perp, rfl⟩ : ∃ y ∈ isotropicPerp γ, linkMatrix γ *ᵥ y = p :=
    mem_link_iff_exists_mem_isotropicPerp.1 hp
  obtain ⟨hy, hγy⟩ : (∀ a : Fin 𝔰.ϱ, y (eStar a) = 0) ∧
      ∀ a : Fin 𝔰.ϱ, (γ⁻¹.val.val *ᵥ y) (eStar a) = 0 := mem_isotropicPerp.1 hy_perp
  -- Likewise `q` comes from some `y'`.
  obtain ⟨y', hy'_perp, rfl⟩ := mem_link_iff_exists_mem_isotropicPerp.1 hq
  obtain ⟨hy', hγy'⟩ := mem_isotropicPerp.1 hy'_perp
  -- Compare the product of `y`, `y'` with that of `γ⁻¹ y`, `γ⁻¹ y'`, and move the terms in `z_N`.
  have h_unitary : star (γ⁻¹.val.val *ᵥ y) ⬝ᵥ S.ratGram *ᵥ γ⁻¹.val.val *ᵥ y' =
      star y ⬝ᵥ S.ratGram *ᵥ y' := U.form_mulVec_mulVec γ⁻¹ y y'
  rw [ratGram_form_of_eStar_eq_zero hγy hγy', ratGram_form_of_eStar_eq_zero hy hy',
    dotProduct_ratMiddle_mulVec_eq_sum_sub, dotProduct_ratMiddle_mulVec_eq_sum_sub] at h_unitary
  simp only [dotProduct_positiveGram_mulVec_eq_sum_add, linkMatrix_mulVec, linkSource, linkTarget,
    LinearMap.funLeft_apply, elim_inl, elim_inr, Function.comp_apply]
  linear_combination -h_unitary

/-- A pair `p = (y₀ + λ' z_N, y₀' + λ z_N)` in the link vanishes as soon as one of its images
`linkSource p = y₀ + λ z⁺` and `linkTarget p = y₀' + λ' z⁺` in the positive space `X₀ ⊥ E z⁺`
vanishes. -/
lemma eq_zero_of_linkSource_or_linkTarget_eq_zero {γ : S.G E}
    {p : 𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E}
    (hp : p ∈ link γ) (h_zero : linkSource E 𝔰 p = 0 ∨ linkTarget E 𝔰 p = 0) : p = 0 := by
  -- The two images have the same norm in a positive space, so they vanish together.
  have h_norm := form_linkSource_eq_form_linkTarget hp hp
  obtain ⟨h_source, h_target⟩ : linkSource E 𝔰 p = 0 ∧ linkTarget E 𝔰 p = 0 := by
    obtain h | h := h_zero
    · exact ⟨h, eq_zero_of_positiveGram_form_eq_zero (S := S) (by simp [← h_norm, h])⟩
    · exact ⟨eq_zero_of_positiveGram_form_eq_zero (S := S) (by simp [h_norm, h]), h⟩
  exact eq_of_linkSource_eq_of_linkTarget_eq (by simp [h_source]) (by simp [h_target])

omit [CMType E] in
/-- A vector lies in the span `A` of `e_1, …, e_ϱ` if and only if its coordinates outside the first
block vanish. -/
lemma mem_isotropicSpan_one {y : 𝔰.BesselIndex → E} :
    y ∈ isotropicSpan (𝔰 := 𝔰) 1 ↔ ∀ i : 𝔰.MiddleIndex ⊕ Fin 𝔰.ϱ, y (inr i) = 0 := by
  constructor
  · rintro ⟨c, rfl⟩ i
    simp [mulVec, dotProduct]
  · intro hy
    refine ⟨fun a ↦ y (inl a), funext fun i ↦ ?_⟩
    rcases i with a | i <;> simp [mulVec, dotProduct, Matrix.one_apply, hy]

omit [CMType E] in
/-- The span of `M e_1, …, M e_ϱ` is the image under `M` of the span `A` of `e_1, …, e_ϱ`. -/
lemma isotropicSpan_eq_map (M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) :
    isotropicSpan M = (isotropicSpan 1).map M.mulVecLin := by
  rw [isotropicSpan, isotropicSpan, colSpan, colSpan, ← LinearMap.range_comp, ← mulVecLin_mul]
  congr 2
  ext i a
  simp [Matrix.mul_apply, Matrix.one_apply]

/-- A vector `y` lies in `γ A` if and only if `γ⁻¹ y` lies in `A`, the span of `e_1, …, e_ϱ`. -/
lemma mem_isotropicSpan_coe {γ : S.G E} {y : 𝔰.BesselIndex → E} :
    y ∈ isotropicSpan γ ↔ γ⁻¹.val.val *ᵥ y ∈ isotropicSpan 1 := by
  rw [isotropicSpan_eq_map, Submodule.mem_map]
  refine ⟨?_, fun hy ↦ ⟨γ⁻¹.val.val *ᵥ y, hy, by simp⟩⟩
  rintro ⟨x, hx, rfl⟩
  simpa using hx

/-- A vector `y` lies in `commonIsotropic γ` if and only if it lies in `isotropicPerp γ` and
`linkMatrix γ *ᵥ y = 0`. -/
lemma mem_commonIsotropic {γ : S.G E} {y : 𝔰.BesselIndex → E} :
    y ∈ commonIsotropic γ ↔ y ∈ isotropicPerp γ ∧ linkMatrix γ *ᵥ y = 0 := by
  rw [commonIsotropic, Submodule.mem_inf, mem_isotropicSpan_coe, mem_isotropicSpan_one,
    mem_isotropicSpan_one, mem_isotropicPerp, linkMatrix_mulVec]
  -- Both sides say that the middle and the last block of `y` and of `γ⁻¹ y` vanish.
  simp only [funext_iff, Sum.forall (α := 𝔰.MiddleIndex), elim_inl, elim_inr, Pi.zero_apply]
  rw [and_and_and_comm, and_comm]

/-- The space `γ A`, spanned by `γ e_1, …, γ e_ϱ`, has rank `ϱ`. -/
lemma finrank_isotropicSpan_coe (γ : S.G E) : finrank E (isotropicSpan γ.val.val) = 𝔰.ϱ := by
  -- The first `ϱ` rows of `γ⁻¹` are a left inverse of the first `ϱ` columns of `γ`.
  have h_inj : Injective ((frameImage γ.val.val).submatrix id castSucc).mulVecLin :=
    HasLeftInv.injective_mulVec ⟨γ⁻¹.val.val.submatrix inl id, Matrix.ext fun a b ↦ by
      simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun₂ γ.val.inv_mul (inl a) (inl b)⟩
  rw [isotropicSpan, LinearMap.finrank_range_of_inj h_inj, finrank_fin_fun]
/-- The columns `e_1, …, e_ϱ, γ e_1, …, γ e_ϱ` of `isotropicFramePair γ` span `A + γ A`, where `A`
is the span of `e_1, …, e_ϱ`. -/
lemma colSpan_isotropicFramePair (γ : S.G E) :
    colSpan (isotropicFramePair γ) = isotropicSpan 1 ⊔ isotropicSpan γ.val.val := by
  rw [isotropicSpan, isotropicSpan, ← colSpan_fromCols]
  congr 1
  ext i (a | a) <;> rfl

/-- Let `A` be the span of `e_1, …, e_ϱ`. The rank of `A + γ A`, the column space of
`isotropicFramePair γ`, and the rank of `commonIsotropic γ = A ∩ γ A` add up to `2 ϱ`. -/
lemma rank_isotropicFramePair_add_finrank_commonIsotropic (γ : S.G E) :
    (isotropicFramePair γ).rank + finrank E (commonIsotropic γ) = 2 * 𝔰.ϱ := by
  have h_one : finrank E (isotropicSpan (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)) = 𝔰.ϱ :=
    finrank_isotropicSpan_coe (1 : S.G E)
  rw [rank, ← colSpan, colSpan_isotropicFramePair, commonIsotropic,
    Submodule.finrank_sup_add_finrank_inf_eq, h_one, finrank_isotropicSpan_coe, two_mul]

/-- Let `A = ⟨e_1, …, e_ϱ⟩`. The rank of `A + γ A`, which is the column space of
`isotropicFramePair γ`, plus the rank of its orthogonal complement `isotropicPerp γ` equals the rank
`𝔰.r` of the whole space. -/
lemma rank_add_finrank_isotropicPerp (γ : S.G E) :
    (isotropicFramePair γ).rank + finrank E (isotropicPerp γ) = 𝔰.r := by
  have h_unit : IsUnit S.ratGram.det := (isUnit_iff_isUnit_det _).1 Floors.IsHermitianUnit.isUnit
  have h_rank : ((isotropicFramePair γ)ᴴ * S.ratGram).rank = (isotropicFramePair γ).rank := by
    rw [rank_mul_eq_left_of_isUnit_det _ _ h_unit, rank_conjTranspose_eq]
  rw [← h_rank, Shape.r, ← finrank_fintype_fun_eq_card E]
  exact ((isotropicFramePair γ)ᴴ * S.ratGram).mulVecLin.finrank_range_add_finrank_ker

/-- The rank of `link γ` plus the rank of `commonIsotropic γ` (the space `I_γ = A ∩ γ A`, with
`A = ⟨e_1, …, e_ϱ⟩`) equals the rank of `isotropicPerp γ = (A + γ A)^⊥`. So the link has the rank of
`(A + γ A)^⊥ / I_γ`. -/
lemma finrank_link_add_finrank_commonIsotropic (γ : S.G E) :
    finrank E (link γ) + finrank E (commonIsotropic γ) = finrank E (isotropicPerp γ) := by
  have h_ker : commonIsotropic γ = isotropicPerp γ ⊓ (linkMatrix γ).mulVecLin.ker :=
    Submodule.ext fun _ ↦ mem_commonIsotropic
  -- This is the rank-nullity formula for `linkMatrix γ` restricted to `(A + γ A)^⊥`.
  rw [← ((linkMatrix γ).mulVecLin.domRestrict (isotropicPerp γ)).finrank_range_add_finrank_ker,
    LinearMap.range_domRestrict, LinearMap.ker_domRestrict, ← Submodule.finrank_map_subtype_eq,
    Submodule.map_comap_subtype, ← h_ker, link_eq_map]

/-- The link `link γ` consists of the pairs of middle blocks of `y` and `γ⁻¹ y`, for `y` orthogonal
to `A = ⟨e_1, …, e_ϱ⟩` and to `γ A`. It has rank `𝔰.k + 1`, where `𝔰.k` is the rank of `X₀`. -/
lemma finrank_link (γ : S.G E) : finrank E (link γ) = 𝔰.k + 1 := by
  -- The rank is that of `(A + γ A)^⊥ / I_γ`, which is `r - 2 ϱ`.
  have h_quot : finrank E (link γ) + finrank E (commonIsotropic γ) = finrank E (isotropicPerp γ) :=
    finrank_link_add_finrank_commonIsotropic γ
  have h_sum : (isotropicFramePair γ).rank + finrank E (commonIsotropic γ) = 2 * 𝔰.ϱ :=
    rank_isotropicFramePair_add_finrank_commonIsotropic γ
  have h_perp : (isotropicFramePair γ).rank + finrank E (isotropicPerp γ) = 𝔰.r :=
    rank_add_finrank_isotropicPerp γ
  have h_r : 𝔰.r = 𝔰.ϱ + (𝔰.k + 1 + 𝔰.ϱ) := by simp [Shape.r]
  lia

/-- A linear map from pairs of middle coordinate vectors to middle coordinate vectors that is
injective on the link of `γ` is a bijection from the link onto the middle coordinate vectors. -/
lemma bijective_domRestrict_link {γ : S.G E}
    {f : (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E) →ₗ[E] (𝔰.MiddleIndex → E)}
    (h_inj : ∀ p ∈ link γ, f p = 0 → p = 0) : Bijective (f.domRestrict (link γ)) := by
  have h_injective : Injective (f.domRestrict (link γ)) :=
    (injective_iff_map_eq_zero _).2 fun ⟨p, hp⟩ h ↦ Subtype.ext (h_inj p hp h)
  exact ⟨h_injective, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simp [finrank_link])).1 h_injective⟩

/-- The bijection `(y₀ + λ' z_N, y₀' + λ z_N) ↦ y₀ + λ z⁺` from the link onto `X₀ ⊥ E z⁺`. -/
def linkSourceEquiv (γ : S.G E) : link γ ≃ₗ[E] (𝔰.MiddleIndex → E) :=
  .ofBijective ((linkSource E 𝔰).domRestrict (link γ))
    (bijective_domRestrict_link fun _ hp h ↦
      eq_zero_of_linkSource_or_linkTarget_eq_zero hp (.inl h))

/-- The bijection `(y₀ + λ' z_N, y₀' + λ z_N) ↦ y₀' + λ' z⁺` from the link onto `X₀ ⊥ E z⁺`. -/
def linkTargetEquiv (γ : S.G E) : link γ ≃ₗ[E] (𝔰.MiddleIndex → E) :=
  .ofBijective ((linkTarget E 𝔰).domRestrict (link γ))
    (bijective_domRestrict_link fun _ hp h ↦
      eq_zero_of_linkSource_or_linkTarget_eq_zero hp (.inr h))

lemma linkSourceEquiv_apply (γ : S.G E) (p : link γ) : linkSourceEquiv γ p = linkSource E 𝔰 p :=
  rfl

lemma linkTargetEquiv_apply (γ : S.G E) (p : link γ) : linkTargetEquiv γ p = linkTarget E 𝔰 p :=
  rfl

/-- The link isometry `Υ_γ` of `X₀ ⊥ E z⁺`: for a pair `(y₀ + λ' z_N, y₀' + λ z_N)` in the link of
`γ`, it sends `y₀ + λ z⁺` to `y₀' + λ' z⁺`. Here `z_N` has the norm `-N` and `z⁺` the norm `N`,
for the prime `N = S.N` of the filling `S`. -/
def linkIsometry (γ : S.G E) : (𝔰.MiddleIndex → E) ≃ₗ[E] (𝔰.MiddleIndex → E) :=
  (linkSourceEquiv γ).symm ≪≫ₗ linkTargetEquiv γ

/-- For `p = (y₀ + λ' z_N, y₀' + λ z_N)` in the link of `γ`, the isometry `Υ_γ` sends
`linkSource p = y₀ + λ z⁺` to `linkTarget p = y₀' + λ' z⁺`. -/
lemma linkIsometry_linkSource {γ : S.G E} {p : 𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E}
    (hp : p ∈ link γ) : linkIsometry γ (linkSource E 𝔰 p) = linkTarget E 𝔰 p := by
  rw [← linkSourceEquiv_apply γ ⟨p, hp⟩, ← linkTargetEquiv_apply γ ⟨p, hp⟩, linkIsometry,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

/-- The map `linkSource` sends the link of `γ` onto `X₀ ⊥ E z⁺`. -/
lemma exists_mem_link_linkSource_eq (γ : S.G E) (a : 𝔰.MiddleIndex → E) :
    ∃ p ∈ link γ, linkSource E 𝔰 p = a := by
  obtain ⟨p, hpa⟩ := (linkSourceEquiv γ).surjective a
  exact ⟨p, p.property, (linkSourceEquiv_apply γ p).symm.trans hpa⟩

/-- The map `Υ_γ = linkIsometry γ` preserves the form of the positive space `X₀ ⊥ E z⁺`, whose Gram
matrix is `S.positiveGram`. -/
theorem dotProduct_positiveGram_mulVec_linkIsometry (γ : S.G E) (a b : 𝔰.MiddleIndex → E) :
    star (linkIsometry γ a) ⬝ᵥ S.positiveGram *ᵥ linkIsometry γ b =
      star a ⬝ᵥ S.positiveGram *ᵥ b := by
  obtain ⟨p, hp, rfl⟩ := exists_mem_link_linkSource_eq γ a
  obtain ⟨q, hq, rfl⟩ := exists_mem_link_linkSource_eq γ b
  rw [linkIsometry_linkSource hp, linkIsometry_linkSource hq,
    form_linkSource_eq_form_linkTarget hp hq]

/-- The map `y ↦ y₀ + λ z⁺` on `(A + γ A)^⊥`, where `y₀` is the `X₀`-part of `y` and `λ` is the
`z_N`-coordinate of `γ⁻¹ y`. -/
def perpToPositive (γ : S.G E) : isotropicPerp γ →ₗ[E] (𝔰.MiddleIndex → E) :=
  (linkSource E 𝔰 ∘ₗ (linkMatrix γ).mulVecLin).domRestrict (isotropicPerp γ)

lemma perpToPositive_apply (γ : S.G E) (y : isotropicPerp γ) :
    perpToPositive γ y = linkSource E 𝔰 (linkMatrix γ *ᵥ y) :=
  rfl

/-- Let `A` be the span of `e_1, …, e_ϱ`. The space `commonIsotropic γ = A ∩ γ A` lies in
`isotropicPerp γ = (A + γ A)^⊥`. -/
lemma commonIsotropic_le_isotropicPerp (γ : S.G E) : commonIsotropic γ ≤ isotropicPerp γ :=
  fun _ hy ↦ (mem_commonIsotropic.1 hy).1

/-- Let `A` be the span of `e_1, …, e_ϱ`, and let `γ` lie in the unitary group `S.G E`. The map
`perpToPositive γ` sends `y` in `isotropicPerp γ = (A + γ A)^⊥` to `y₀ + λ z⁺` in the positive space
`X₀ ⊥ E z⁺`. Here `z⁺` is a vector of norm `S.N`, `y₀` is the `X₀`-part of `y`, and `λ` is the
`z_N`-coordinate of `γ⁻¹ y`. The kernel of `perpToPositive γ` is `commonIsotropic γ = A ∩ γ A`,
viewed inside `isotropicPerp γ`. -/
lemma ker_perpToPositive (γ : S.G E) :
    (perpToPositive γ).ker = (commonIsotropic γ).submoduleOf (isotropicPerp γ) := by
  ext ⟨y, hy⟩
  -- A pair in the link vanishes exactly when its image under `linkSource` vanishes.
  have h_zero : linkSource E 𝔰 (linkMatrix γ *ᵥ y) = 0 ↔ linkMatrix γ *ᵥ y = 0 :=
    ⟨fun h ↦ eq_zero_of_linkSource_or_linkTarget_eq_zero (linkMatrix_mulVec_mem_link hy) (.inl h),
      fun h ↦ by rw [h, map_zero]⟩
  calc (⟨y, hy⟩ : isotropicPerp γ) ∈ (perpToPositive γ).ker
    _ ↔ linkMatrix γ *ᵥ y = 0 := by rw [LinearMap.mem_ker, perpToPositive_apply, h_zero]
    _ ↔ y ∈ commonIsotropic γ := by rw [mem_commonIsotropic, and_iff_right hy]
    _ ↔ (⟨y, hy⟩ : isotropicPerp γ) ∈ (commonIsotropic γ).submoduleOf (isotropicPerp γ) := Iff.rfl

/-- The map `perpToPositive γ`, `y ↦ y₀ + λ z⁺`, sends `isotropicPerp γ = (A + γ A)^⊥` onto
`X₀ ⊥ E z⁺`, where `A` is the span of `e_1, …, e_ϱ`. -/
lemma perpToPositive_surjective (γ : S.G E) : Surjective (perpToPositive γ) := by
  intro a
  obtain ⟨p, hp, rfl⟩ := exists_mem_link_linkSource_eq γ a
  obtain ⟨y, hy, rfl⟩ := mem_link_iff_exists_mem_isotropicPerp.1 hp
  exact ⟨⟨y, hy⟩, perpToPositive_apply γ ⟨y, hy⟩⟩

/-- The space `commonIsotropic γ = A ∩ γ A`, for `A` the span of `e_1, …, e_ϱ`, lies in
`isotropicPerp γ = (A + γ A)^⊥`. The map `perpToPositive γ`, `y ↦ y₀ + λ z⁺`, sends `y` to its
`X₀`-part `y₀` plus `λ z⁺`, where `λ` is the `z_N`-coordinate of `γ⁻¹ y`. It has kernel `A ∩ γ A`
and is surjective, so it induces a bijection from `(A + γ A)^⊥ / (A ∩ γ A)` onto `X₀ ⊥ E z⁺`. -/
theorem ker_perpToPositive_and_surjective (γ : S.G E) :
    commonIsotropic γ ≤ isotropicPerp γ ∧
    (perpToPositive γ).ker = (commonIsotropic γ).submoduleOf (isotropicPerp γ) ∧
    Surjective (perpToPositive γ) :=
  ⟨commonIsotropic_le_isotropicPerp γ, ker_perpToPositive γ, perpToPositive_surjective γ⟩

/-- The link of `γ` is the graph of `Υ_γ`: a pair `p` lies in it if and only if `Υ_γ` sends
`linkSource p` to `linkTarget p`. -/
lemma mem_link_iff_linkIsometry {γ : S.G E} {p : 𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E} :
    p ∈ link γ ↔ linkIsometry γ (linkSource E 𝔰 p) = linkTarget E 𝔰 p := by
  refine ⟨linkIsometry_linkSource, fun h ↦ ?_⟩
  obtain ⟨q, hq, h_source⟩ := exists_mem_link_linkSource_eq γ (linkSource E 𝔰 p)
  have h_target : linkTarget E 𝔰 q = linkTarget E 𝔰 p := by
    rw [← linkIsometry_linkSource hq, h_source, h]
  rwa [← eq_of_linkSource_eq_of_linkTarget_eq h_source h_target]

/-- Two elements of `S.G E` have the same link isometry if and only if they have the same link. -/
theorem linkIsometry_eq_iff {γ γ' : S.G E} :
    linkIsometry γ = linkIsometry γ' ↔ link γ = link γ' := by
  refine ⟨fun h ↦ Submodule.ext fun p ↦ ?_, fun h ↦ LinearEquiv.ext fun a ↦ ?_⟩
  · rw [mem_link_iff_linkIsometry, mem_link_iff_linkIsometry, h]
  · obtain ⟨p, hp, rfl⟩ := exists_mem_link_linkSource_eq γ a
    rw [linkIsometry_linkSource hp, linkIsometry_linkSource (h.le hp)]

/-- The link isometry is the same for `u⁻¹ γ u'` as for `γ`, when `u` and `u'` lie in the Bessel
unipotent group `besselU`, because the two links are equal. -/
theorem linkIsometry_inv_mul_mul_of_mem_besselU {γ u u' : S.G E} (hu : u ∈ besselU)
    (hu' : u' ∈ besselU) :
    linkIsometry (u⁻¹ * γ * u') = linkIsometry γ :=
  linkIsometry_eq_iff.2 (link_inv_mul_mul_of_mem_besselU hu hu')

/-- The product of two pairs `p`, `q` for the form `S.linkForm = T ⊕ -T`, where `T` is the form of
`X₀ ⊥ E z_N`, is the difference of the products, in the positive space `X₀ ⊥ E z⁺` with Gram matrix
`S.positiveGram`, of their images under `linkSource` and of their images under `linkTarget`. -/
lemma dotProduct_linkForm_mulVec_eq_sub (S : Filling E 𝔰)
    (p q : 𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E) :
    star p ⬝ᵥ S.linkForm *ᵥ q =
      star (linkSource E 𝔰 p) ⬝ᵥ S.positiveGram *ᵥ linkSource E 𝔰 q -
        star (linkTarget E 𝔰 p) ⬝ᵥ S.positiveGram *ᵥ linkTarget E 𝔰 q := by
  have h_split : star p ⬝ᵥ S.linkForm *ᵥ q = star (p ∘ inl) ⬝ᵥ S.ratMiddle E *ᵥ (q ∘ inl) -
      star (p ∘ inr) ⬝ᵥ S.ratMiddle E *ᵥ (q ∘ inr) := by
    simp [fromBlocks_mulVec, neg_mulVec, dotProduct, sub_eq_add_neg]
  simp only [h_split, dotProduct_ratMiddle_mulVec_eq_sum_sub,
    dotProduct_positiveGram_mulVec_eq_sum_add, linkSource, linkTarget,
    LinearMap.funLeft_apply, elim_inl, elim_inr, Function.comp_apply]
  ring

/-- The link of `γ` consists of the pairs of middle blocks of `y` and `γ⁻¹ y`, for `y` orthogonal to
`A = ⟨e_1, …, e_ϱ⟩` and to `γ A`. It is its own orthogonal complement for the form `S.linkForm` on
pairs of middle vectors, which is `S.ratMiddle E` on the first member minus `S.ratMiddle E` on the
second. -/
lemma _root_.New.mem_link_iff_orthogonal {γ : S.G E} {p : 𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E} :
    p ∈ link γ ↔ ∀ q ∈ link γ, star q ⬝ᵥ S.linkForm *ᵥ p = 0 := by
  simp only [dotProduct_linkForm_mulVec_eq_sub, sub_eq_zero]
  refine ⟨fun hp q hq ↦ form_linkSource_eq_form_linkTarget hq hp, fun h_orth ↦ ?_⟩
  -- The difference `d` of `Υ_γ (linkSource p)` and `linkTarget p` is `linkTarget q` for some `q` in
  -- the link, and the hypothesis at `q` says that `d` has norm `0`.
  rw [mem_link_iff_linkIsometry, ← sub_eq_zero]
  set d : 𝔰.MiddleIndex → E := linkIsometry γ (linkSource E 𝔰 p) - linkTarget E 𝔰 p with hd
  obtain ⟨q, hq, h_source⟩ := exists_mem_link_linkSource_eq γ ((linkIsometry γ).symm d)
  have h_target : linkTarget E 𝔰 q = d := by
    rw [← linkIsometry_linkSource hq, h_source, LinearEquiv.apply_symm_apply]
  refine eq_zero_of_positiveGram_form_eq_zero (S := S) ?_
  calc star d ⬝ᵥ S.positiveGram *ᵥ d
      = star (linkTarget E 𝔰 q) ⬝ᵥ S.positiveGram *ᵥ linkIsometry γ (linkSource E 𝔰 p) -
          star (linkTarget E 𝔰 q) ⬝ᵥ S.positiveGram *ᵥ linkTarget E 𝔰 p := by
        rw [← dotProduct_sub, ← mulVec_sub, h_target]
    _ = 0 := by rw [← h_orth q hq, ← linkIsometry_linkSource hq,
      dotProduct_positiveGram_mulVec_linkIsometry, sub_self]

/-! ### The link on the second frame, and the vanishing of `termDisc` -/

/-- Let `S` be a filling over the CM field `E`, with the prime `N = S.N`, and let `γ` lie in
`S.G E`. The columns of `frameImage γ` are the images under `γ` of the frame
`f = (e_1, …, e_ϱ, z_N)`. Let their combination `y = γ f · c` have the products `(0, …, 0, c')` with
`f`. Let `y₀` be the `X₀`-part of `y` and `c_z = c 𝔰.top` the last coefficient. Then
`linkIsometry γ`, the isometry of `X₀ ⊥ E z⁺` read off from the link of `γ`, where `z⁺` has the norm
`N`, sends `y₀ + c_z z⁺` to `-(c' / N) z⁺`. -/
theorem linkIsometry_frameImage_mulVec {γ : S.G E} {c : Fin (𝔰.ϱ + 1) → E} {c' : E}
    (h_products : S.frameProducts γ *ᵥ c = Pi.single 𝔰.top c') :
    linkIsometry γ (((frameImage γ *ᵥ c) ∘ 𝔰.indexX₀) ⊕ᵥ fun _ : Unit ↦ c 𝔰.top) =
      (0 : 𝔰.κ → E) ⊕ᵥ fun _ : Unit ↦ -(c' / S.N) := by
  -- The classes of `y` and `γ⁻¹ y = f · c` are `y₀ - (c' / N) z_N` and `c_z z_N`.
  set y : 𝔰.BesselIndex → E := frameImage γ *ᵥ c with hy
  have h_coord : y 𝔰.z = -(c' / S.N) := by
    simp [← neg_mul_frameImage_mulVec_z_eq h_products, hy, neg_div, S.N_prime.ne_zero]
  have h_inv : γ⁻¹.val.val *ᵥ y = init c ⊕ᵥ ((0 ⊕ᵥ fun _ : Unit ↦ c 𝔰.top) ⊕ᵥ 0) := by
    simp [← frameImage_one_mulVec, hy, frameImage_mulVec γ.val.val]
  have h_perp : y ∈ isotropicPerp γ := mem_isotropicPerp.2
    ⟨frameImage_mulVec_eStar_eq_zero h_products, fun a ↦ congrFun h_inv (eStar a)⟩
  have h_image := linkIsometry_linkSource (linkMatrix_mulVec_mem_link h_perp)
  rwa [linkSource_linkMatrix_mulVec, linkTarget_linkMatrix_mulVec, h_inv, h_coord] at h_image

/-- Let `S` be a filling over the CM field `E`, with the prime `N = S.N`, and let `γ ∈ S.G E`. Let
`y = frameImage γ *ᵥ c` be a combination of the image `γ f` of the frame `f = (e_1, …, e_ϱ, z)`
whose products with `f`, the vector `S.frameProducts γ *ᵥ c`, are `(0, …, 0, c')`. Let
`y₀ = y ∘ 𝔰.indexX₀` be the part of `y` in the definite summand `X₀`, and `c_z = c 𝔰.top` the
coefficient at `z`. Then `N ⟨y₀, y₀⟩ = c' c̄' - N² c_z c̄_z`. -/
theorem mul_dotProduct_comp_indexX₀_eq_sub {γ : S.G E} {c : Fin (𝔰.ϱ + 1) → E} {c' : E}
    (h_products : S.frameProducts γ *ᵥ c = Pi.single 𝔰.top c') :
    S.N * (star ((frameImage γ *ᵥ c) ∘ 𝔰.indexX₀) ⬝ᵥ (frameImage γ *ᵥ c) ∘ 𝔰.indexX₀) =
      c' * star c' - S.N ^ 2 * (c 𝔰.top * star (c 𝔰.top)) := by
  set y₀ : 𝔰.κ → E := (frameImage γ *ᵥ c) ∘ 𝔰.indexX₀
  have hN : (S.N : E) ≠ 0 := Nat.cast_ne_zero.2 S.N_prime.ne_zero
  have h_norm : S.N * (star (c' / S.N) * (c' / S.N)) =
      star y₀ ⬝ᵥ y₀ + S.N * (star (c 𝔰.top) * c 𝔰.top) := by
    let a : 𝔰.MiddleIndex → E := y₀ ⊕ᵥ fun _ : Unit ↦ c 𝔰.top
    have h_form : star (linkIsometry γ a) ⬝ᵥ S.positiveGram *ᵥ linkIsometry γ a =
        star a ⬝ᵥ S.positiveGram *ᵥ a := dotProduct_positiveGram_mulVec_linkIsometry γ a a
    rw [linkIsometry_frameImage_mulVec h_products, dotProduct_positiveGram_mulVec_eq_sum_add,
      dotProduct_positiveGram_mulVec_eq_sum_add] at h_form
    simpa [a, dotProduct] using h_form
  rw [star_div₀, star_natCast] at h_norm
  field_simp at h_norm
  linear_combination -h_norm

/-- Let `f = (e_1, …, e_ϱ, z)` be the frame and let `y = γ f · c` have the products
`S.frameProducts γ *ᵥ c = (0, …, 0, c')` with `f`. Then `y` is a combination of `f` if and only if
its `X₀`-part vanishes. -/
lemma exists_frameImage_eq_iff {γ : S.G E} {c : Fin (𝔰.ϱ + 1) → E} {c' : E}
    (h_products : S.frameProducts γ *ᵥ c = Pi.single 𝔰.top c') :
    (∃ x : Fin (𝔰.ϱ + 1) → E, frameImage 1 *ᵥ x = frameImage γ *ᵥ c) ↔
      (frameImage γ *ᵥ c) ∘ 𝔰.indexX₀ = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    simp [← hx, ↓frameImage_one_mulVec, funext_iff]
  · intro h_zero
    refine ⟨(frameImage γ *ᵥ c) ∘ 𝔰.besselFrame, ?_⟩
    have h_middle (i : 𝔰.κ) : (frameImage γ *ᵥ c) (𝔰.indexX₀ i) = 0 := congrFun h_zero i
    simp [↓frameImage_one_mulVec, init, frameImage_mulVec_eStar_eq_zero h_products, h_middle,
      funext_iff]

/-- Let `f = (e_1, …, e_ϱ, z)` be the frame. If `y = frameImage γ *ᵥ c` is orthogonal to the whole
frame `f`, that is `S.frameProducts γ *ᵥ c = 0`, then `y` equals `frameImage 1 *ᵥ x` for some `x`,
so it is a combination of `f`. -/
lemma exists_frameImage_eq_of_frameProducts_mulVec_eq_zero {γ : S.G E} {c : Fin (𝔰.ϱ + 1) → E}
    (h_ker : S.frameProducts γ *ᵥ c = 0) :
    ∃ x : Fin (𝔰.ϱ + 1) → E, frameImage 1 *ᵥ x = frameImage γ *ᵥ c := by
  have h_products : S.frameProducts γ *ᵥ c = Pi.single 𝔰.top 0 := by rw [h_ker, Pi.single_zero]
  -- The link isometry sends `y₀ + c_z z⁺` to `0`, so this vector and its `X₀`-part `y₀` vanish.
  have h_zero : (((frameImage γ *ᵥ c) ∘ 𝔰.indexX₀) ⊕ᵥ fun _ : Unit ↦ c 𝔰.top) = 0 :=
    (linkIsometry γ).map_eq_zero_iff.1
      (by simp [linkIsometry_frameImage_mulVec h_products, funext_iff])
  exact (exists_frameImage_eq_iff h_products).2 (funext fun i ↦ congrFun h_zero (inl i))

/-- Let `S` be a filling over the CM field `E`, with the prime `N = S.N`. Let `f = frameImage 1` be
the frame `(e_1, …, e_ϱ, z)`, and let `frameImage γ` be its image `γ f`. Let `δ` be the determinant
of the matrix of products of `f` with `γ f`, and `δ'` its leading minor of size `ϱ`. Then
`S.termDisc γ = |δ|² - N² |δ'|²` vanishes if and only if there are coefficient vectors `x` and
`y ≠ 0` with `frameImage 1 *ᵥ x = frameImage γ *ᵥ y`. -/
lemma termDisc_eq_zero_iff_exists {γ : S.G E} :
    S.termDisc γ = 0 ↔
      ∃ x y : Fin (𝔰.ϱ + 1) → E, y ≠ 0 ∧ frameImage 1 *ᵥ x = frameImage γ *ᵥ y := by
  by_cases h_det : (S.frameProducts γ).det = 0
  · -- Here `termDisc γ = 0`, and a nonzero vector of the kernel is shared.
    obtain ⟨y, hy, h_ker⟩ := exists_mulVec_eq_zero_iff.2 h_det
    obtain ⟨x, hxy⟩ := exists_frameImage_eq_of_frameProducts_mulVec_eq_zero h_ker
    exact iff_of_true ((termDisc_pos_or_eq_zero γ).resolve_left fun h ↦ h.2 h_det) ⟨x, y, hy, hxy⟩
  -- The last column `c` of the adjugate has the products `(0, …, 0, δ)` and the last entry `δ'`,
  -- so `termDisc γ` is `N ⟨y₀, y₀⟩` for the `X₀`-part `y₀` of `γ f · c`.
  obtain ⟨c, h_products, hc_top⟩ := exists_mulVec_eq_single_det (S.frameProducts γ)
  have h_disc : S.termDisc γ = 0 ↔ (frameImage γ *ᵥ c) ∘ 𝔰.indexX₀ = 0 := by
    rw [termDisc, frameDisc, ← hc_top, ← mul_dotProduct_comp_indexX₀_eq_sub h_products,
      mul_eq_zero_iff_left (Nat.cast_ne_zero.2 S.N_prime.ne_zero)]
    refine ⟨fun h_norm ↦ funext fun i ↦ ?_, fun h ↦ by rw [h, dotProduct_zero]⟩
    -- The space `X₀` is positive.
    have h_zero : (((frameImage γ *ᵥ c) ∘ 𝔰.indexX₀) ⊕ᵥ 0 : 𝔰.MiddleIndex → E) = 0 := by
      refine eq_zero_of_positiveGram_form_eq_zero (S := S) ?_
      rw [dotProduct_positiveGram_mulVec_eq_sum_add]
      simpa [dotProduct] using h_norm
    exact congrFun h_zero (inl i)
  rw [h_disc]
  constructor
  · intro h_zero
    obtain ⟨x, hx⟩ := (exists_frameImage_eq_iff h_products).2 h_zero
    exact ⟨x, c, fun h ↦ h_det (by simpa [h, eq_comm] using h_products), hx⟩
  · -- The coefficients `y` of a shared vector are a multiple of `c`.
    rintro ⟨x, y, hy, hxy⟩
    have h_products' := frameProducts_mulVec_of_frameImage_eq hxy
    let t : E := -S.N * x 𝔰.top / (S.frameProducts γ).det
    have h_multiple : y = t • c := by
      apply mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).2 (Ne.isUnit h_det))
      rw [h_products', mulVec_smul, h_products, ← Pi.single_smul, smul_eq_mul,
        div_mul_cancel₀ _ h_det]
    have h_zero : (frameImage γ *ᵥ y) ∘ 𝔰.indexX₀ = 0 :=
      (exists_frameImage_eq_iff h_products').1 ⟨x, hxy⟩
    rwa [h_multiple, mulVec_smul, Pi.smul_comp,
      smul_eq_zero_iff_right fun ht ↦ hy (by rw [h_multiple, ht, zero_smul])] at h_zero

/-- The vectors `γ e_1, …, γ e_ϱ, γ z`, the columns of `frameImage γ`, are linearly independent. -/
lemma frameImage_mulVec_eq_zero_iff {γ : S.G E} {y : Fin (𝔰.ϱ + 1) → E} :
    frameImage (𝔰 := 𝔰) γ *ᵥ y = 0 ↔ y = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, mulVec_zero]⟩
  have h_one : frameImage 1 *ᵥ y = 0 :=
    mulVec_injective_of_isUnit γ.val.isUnit (by rw [← frameImage_mulVec, h, mulVec_zero])
  -- The columns of `frameImage 1` are distinct standard basis vectors.
  exact funext fun a ↦ by simpa [mulVec, dotProduct, Matrix.one_apply,
    besselFrame_injective.eq_iff] using congrFun h_one (𝔰.besselFrame a)

/-- The quantity `S.termDisc γ`, formed from the last two leading minors of the matrix of products
of the frame `f = (e_1, …, e_ϱ, z)` with `γ f`, vanishes if and only if the spans of `f` and of
`γ f` have a nonzero intersection. -/
theorem termDisc_eq_zero_iff {γ : S.G E} :
    S.termDisc γ = 0 ↔ colSpan (frameImage 1) ⊓ colSpan (frameImage γ.val.val) ≠ ⊥ := by
  rw [termDisc_eq_zero_iff_exists, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨x, y, hy, hxy⟩
    exact ⟨frameImage γ *ᵥ y, ⟨⟨x, hxy⟩, ⟨y, rfl⟩⟩, frameImage_mulVec_eq_zero_iff.not.2 hy⟩
  · rintro ⟨t, ⟨⟨x, hxy⟩, ⟨y, rfl⟩⟩, h_ne⟩
    exact ⟨x, y, frameImage_mulVec_eq_zero_iff.not.1 h_ne, hxy⟩

end Filling

end New

end LinkIsometry

end
