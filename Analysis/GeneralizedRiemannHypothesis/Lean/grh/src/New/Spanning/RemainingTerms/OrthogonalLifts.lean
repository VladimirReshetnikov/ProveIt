import New.Spanning.RemainingTerms.BorderedDeterminant

/-!
# Orthogonal lifts and the two isotropic lists of a link

Let `γ` have cell rank `j`, let `Λ` be the lattice of a class, `A` the span of `e₁, …, e_ϱ`,
`I = A ∩ γ A`, and let `z` be the last vector of the frame, of norm `-N`. This file defines
orthogonal lifts of a basis `v` of the link of `γ`. These are vectors orthogonal to `A` and `γ A`
over the columns of `(0 | v)`, whose first columns form a basis of `I`. It proves that such lifts
exist and that they are isometric to `v` for `S.linkMetric` after a correction by their products
with `z` and `γ z`. It then adjoins two vectors `z'`, `z''` of norm `N` and computes the
discriminant of the isotropic lists `(e_a, z + z')` and `(γ e_a, γ z + z'')`, `a < j`. It also
shows that `torsionIndex k` divides the index of the classes of the `e_a` and `k e_a` in the
integral vectors of their span, for finite-adelic `k`.

Notions from other files:
* `framePair γ` has the columns `e₁, …, e_ϱ, z` and their images under `γ`;
  `isotropicFramePair γ` leaves out `z` and `γ z`.
* `linkMatrix γ` sends `t` to the middle coordinates of `t` and `γ⁻¹ t`; `link γ` is its image of
  the orthogonal complement of `A + γ A`.
* `HasCellRank j γ` says that `γ` has cell rank `j`: `NormOnePairOccursFrom j γ`, the leading
  `j`-minor of the products of the two frames is nonzero, and `S.termDisc γ ≠ 0` exactly when
  `j = ϱ + 1`.
* `isotropicRowsIndex j k` is the index, among the products of `Λ ∩ A` with the frame of `k`, of
  those from the `e_a`, `a < j`; `torsionIndex k` is the index of the lattice spanned by the
  `e_a` and `k e_a` in the integral vectors of their span.

## Main definitions and results

* `New.Filling.IsOrthogonalLift`, `New.Filling.exists_orthogonal_lift`: orthogonal lifts of a basis
  of the link, and their existence for `γ` of cell rank `j`.
* `New.Filling.abs_norm_det_gram_eq_abs_norm_subframeMinor_sq`,
  `New.Filling.isotropicRowsIndex_mul_dvd_submoduleIndex`: the discriminant of the two lists, and
  a divisor of the index attached to the classes of the `e_a` and `k e_a`, `a < j`.
-/

namespace New.Filling

open Matrix Fintype Equiv Fin Algebra Sum Submodule RingHom Pointwise

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {τ : Type}
  {S : Filling E 𝔰} {c c' : S.Classes} {j : Fin (𝔰.ϱ + 2)} {γ : S.G E}

/-! ### A basis of `I` and lifts of a basis of the link -/

/-- The indices `b ≥ j` of the basis vectors `e_b` of `A`. -/
abbrev IndexNotBelow (j : Fin (𝔰.ϱ + 2)) : Type := {a : Fin 𝔰.ϱ // ¬a.1 < j}

/-- The vectors `z` and `k z`, as columns. -/
abbrev lastPair {R : Type} [CommRing R] [StarRing R] {T : 𝔰.Form R} (k : T.G) :
    Matrix 𝔰.BesselIndex (Unit ⊕ Unit) R :=
  (framePair k).submatrix id (.map (fun _ ↦ 𝔰.top) fun _ ↦ 𝔰.top)

/-- The matrix whose columns are the basis vectors `e*_b` with `b ≥ j`. -/
noncomputable def eStarCols (R : Type) [CommRing R] (j : Fin (𝔰.ϱ + 2)) :
    Matrix 𝔰.BesselIndex (IndexNotBelow j) R :=
  (diagonal 1).submatrix id (inr ∘ inr ∘ sumCompl (fun a : Fin 𝔰.ϱ ↦ a.1 < j) ∘ inr)

/-- An orthogonal lift of `v` at cell rank `j`. The columns of `u` are orthogonal to the isotropic
space `A = ⟨e₁, …, e_ϱ⟩` and to `γ A`. The first ones, one for each index `b ≥ j`, are dual to the
vectors `e*_b` and are sent to zero by `linkMatrix γ` (the map to the middle coordinates of `t` and
`γ⁻¹ t`). The others are orthogonal to the `e*_b` and are sent to the columns of `v`. -/
structure IsOrthogonalLift (j : Fin (𝔰.ϱ + 2)) (γ : S.G E)
    (v : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) τ E)
    (u : Matrix 𝔰.BesselIndex (IndexNotBelow j ⊕ τ) E) : Prop where
  /-- The columns of `u` are orthogonal to `A` and `γ A`. -/
  orthogonal : (isotropicFramePair γ)ᴴ * S.ratGram * u = 0
  /-- The map `linkMatrix γ` kills the first columns of `u` and sends the others to those of `v`. -/
  linkMatrix_mul : linkMatrix γ * u = fromCols 0 v
  /-- The first columns of `u` are dual to the `e*_b` with `b ≥ j`, the others are orthogonal to
  them. -/
  dual : (eStarCols E j)ᴴ * S.ratGram * u = fromCols 1 0

/-- Let `γ` have cell rank `j`. For any `d`, some vector of `A ∩ γ A`, where `A` is the span of the
isotropic `e_a`, has the coordinates `d a` at the indices `a ≥ j`. It is given by its coefficients
`x` in the frame `e₁, …, e_ϱ, z` (the columns of `frameImage 1`, `z` at the index `𝔰.top`), those of
its image under `γ⁻¹` being `y`. -/
lemma HasCellRank.exists_isotropic_inter_vector (hj : S.HasCellRank j γ) (d : Fin 𝔰.ϱ → E) :
    ∃ x y : Fin (𝔰.ϱ + 1) → E, x 𝔰.top = 0 ∧ y 𝔰.top = 0 ∧
      (∀ a : Fin 𝔰.ϱ, j.val ≤ a.val → x a.castSucc = d a) ∧
      γ⁻¹.val.val *ᵥ frameImage 1 *ᵥ x = frameImage 1 *ᵥ y := by
  by_cases h_low : j.val ≤ 𝔰.ϱ
  · obtain ⟨h_form, -, -⟩ := hj
    obtain ⟨y, x, hx, hxy⟩ := exists_frameImage_eq_of_normOnePairOccursFrom h_form.inv (snoc d 0)
    have hx_top : x 𝔰.top = 0 := (hx 𝔰.top h_low).trans (snoc_last ..)
    have h_last : star (y 𝔰.top) * y 𝔰.top = star (x 𝔰.top) * x 𝔰.top :=
      star_mul_last_eq_of_frameImage_eq hxy
    have hy_top : y 𝔰.top = 0 := by simpa [hx_top] using h_last
    have h_frame : γ⁻¹.val.val *ᵥ frameImage 1 *ᵥ x = frameImage 1 *ᵥ y :=
      (frameImage_mulVec _ x).symm.trans hxy.symm
    refine ⟨x, y, hx_top, hy_top, fun a ha ↦ ?_, h_frame⟩
    simpa using hx a.castSucc ha
  · exact ⟨0, 0, rfl, rfl, fun a ha ↦ by omega, by simp⟩

/-- Let `A` be the span of the isotropic basis vectors `e₁, …, e_ϱ`, and let `e*_b` be the isotropic
basis vector dual to `e_b`. If `γ` has cell rank `j` and the columns of `v` span its link, then `v`
has an orthogonal lift `u`: its columns are orthogonal to `A` and `γ A`, their images in the link
are the columns of `(0 | v)`, and their products with the `e*_b`, `b ≥ j`, form the matrix
`(1 | 0)`. -/
lemma exists_orthogonal_lift [Fintype τ] [DecidableEq τ] (hj : S.HasCellRank j γ)
    {v : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) τ E} (hL : colSpan v = link γ) :
    ∃ u : Matrix 𝔰.BesselIndex (IndexNotBelow j ⊕ τ) E, IsOrthogonalLift j γ v u := by
  let r : IndexBelow j ⊕ IndexNotBelow j ≃ Fin 𝔰.ϱ := sumCompl fun a : Fin 𝔰.ϱ ↦ a.1 < j
  let m : Matrix 𝔰.BesselIndex (Fin 𝔰.ϱ ⊕ Fin 𝔰.ϱ) E := isotropicFramePair γ
  let s : Matrix 𝔰.BesselIndex (IndexNotBelow j) E := eStarCols E j
  -- The three conditions form one linear system, solved column by column.
  have hcol (b : IndexNotBelow j ⊕ τ) :
      ((fromRows 0 (fromCols 0 v)).fromRows (fromCols (diagonal 1) 0)).col b ∈
        colSpan (((mᴴ * S.ratGram).fromRows (linkMatrix γ)).fromRows (sᴴ * S.ratGram)) := by
    have hv_col : (fromCols 0 v).col b ∈ colSpan v := by
      rcases b with b | b
      · exact zero_mem (colSpan v)
      · exact ⟨Pi.single b 1, v.mulVec_single_one b⟩
    -- A vector `t` meets the first two conditions, as the column of `(0 | v)` lies in the link.
    obtain ⟨t, ht, ht_link⟩ : ∃ t : 𝔰.BesselIndex → E,
        t ∈ ((isotropicFramePair γ)ᴴ * S.ratGram).mulVecLin.ker ∧
          linkMatrix γ *ᵥ t = (fromCols 0 v).col b :=
      mem_map.1 (hL.le hv_col)
    obtain ⟨ht_eStar, ht_inv_eStar⟩ := orthogonal_isotropicFramePair_iff.1 ht
    let target : Fin 𝔰.ϱ → E := fun a ↦
      fromRows (0 : Matrix (IndexBelow j) (IndexNotBelow j ⊕ τ) E) (fromCols 1 0) (r.symm a) b
    -- A vector of `A ∩ γ A` corrects the coordinates at the indices `≥ j`.
    obtain ⟨x, y, hx_top, hy_top, hx, hframe⟩ : ∃ x y : Fin (𝔰.ϱ + 1) → E,
        x 𝔰.top = 0 ∧ y 𝔰.top = 0 ∧
          (∀ a : Fin 𝔰.ϱ, j.val ≤ a.val → x a.castSucc = target a - t (inl a)) ∧
          γ⁻¹.val.val *ᵥ frameImage 1 *ᵥ x = frameImage 1 *ᵥ y :=
      hj.exists_isotropic_inter_vector (target - t ∘ inl)
    use t + frameImage 1 *ᵥ x
    have h_orth : (mᴴ * S.ratGram) *ᵥ (t + frameImage 1 *ᵥ x) = 0 := by
      refine LinearMap.mem_ker.1 (orthogonal_isotropicFramePair_iff.2 ?_)
      rw [mulVec_add, hframe]
      simpa [frameImage_one_mulVec, ht_eStar] using ht_inv_eStar
    have h_link_zero : linkMatrix γ *ᵥ (frameImage 1 *ᵥ x) = 0 := by
      rw [linkMatrix, fromRows_mulVec]
      ext (i | i)
      · change ((1 : S.G E).val.val *ᵥ frameImage 1 *ᵥ x) (inr (inl i)) = 0
        rcases i with i | i <;> simp [frameImage_one_mulVec, hx_top]
      · change (γ⁻¹.val.val *ᵥ frameImage 1 *ᵥ x) (inr (inl i)) = 0
        rw [hframe]
        rcases i with i | i <;> simp [frameImage_one_mulVec, hy_top]
    have h_dual : (sᴴ * S.ratGram) *ᵥ (t + frameImage 1 *ᵥ x) =
        (fromCols (diagonal 1) 0).col b := by
      ext a
      -- The product with `e*_a` reads off the coordinate at `e_a`, where `x` is `target - t`.
      simpa [s, r, target, eStarCols, frameImage_one_mulVec, init, mulVec, dotProduct,
        Matrix.mul_apply, Matrix.one_apply, eq_sub_iff_add_eq'] using hx a.1 (not_lt.1 a.2)
    rw [mulVecLin_apply, fromRows_mulVec, fromRows_mulVec, h_orth,
      mulVec_add, h_link_zero, ht_link, add_zero, h_dual]
    ext ((a | a) | a) <;> rfl
  obtain ⟨u, hu⟩ : ∃ u : Matrix 𝔰.BesselIndex (IndexNotBelow j ⊕ τ) E,
      ((mᴴ * S.ratGram).fromRows (linkMatrix γ)).fromRows (sᴴ * S.ratGram) * u =
        (fromRows 0 (fromCols 0 v)).fromRows (fromCols (diagonal 1) 0) :=
    exists_mul_eq_of_col_mem_range hcol
  obtain ⟨⟨h_orth, h_link⟩, h_dual⟩ :
      (mᴴ * S.ratGram * u = 0 ∧ linkMatrix γ * u = fromCols 0 v) ∧
        sᴴ * S.ratGram * u = fromCols (diagonal 1) 0 := by
    simpa only [fromRows_mul, fromRows_ext_iff] using hu
  exact ⟨u, h_orth, h_link, h_dual⟩

section OrthogonalLift

variable {τ : Type} {v : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) τ E}
  {u : Matrix 𝔰.BesselIndex (IndexNotBelow j ⊕ τ) E}

/-- Let `u` be an orthogonal lift. In its row of the isotropic basis vector `e_i`, `i ≥ j`, it has
the identity in its first block of columns and zero in the second. -/
lemma IsOrthogonalLift.apply_inl (hu : IsOrthogonalLift j γ v u) (i : IndexNotBelow j) :
    (∀ a : IndexNotBelow j, u (inl i.val) (inl a) = if i = a then 1 else 0) ∧
      ∀ b : τ, u (inl i.val) (inr b) = 0 := by
  have h_entry (x : IndexNotBelow j ⊕ τ) : u (inl i.val) x =
      fromCols (1 : Matrix (IndexNotBelow j) (IndexNotBelow j) E) 0 i x := by
    simpa [eStarCols, -Subtype.forall, Matrix.mul_apply, Matrix.one_apply] using
      congrFun₂ hu.dual i x
  exact ⟨fun a ↦ by simpa [Matrix.one_apply] using h_entry (inl a),
    fun b ↦ by simpa using h_entry (inr b)⟩

/-- If `u` is an orthogonal lift (`IsOrthogonalLift j γ v u`), its first columns `u.toCols₁` are
orthogonal, for the form `S.ratGram`, to the columns of `isotropicFramePair γ`, which span `A` and
`γ A`. -/
lemma IsOrthogonalLift.orthogonal_toCols₁ (hu : IsOrthogonalLift j γ v u) :
    (isotropicFramePair γ)ᴴ * S.ratGram * u.toCols₁ = 0 :=
  congrArg toCols₁ hu.orthogonal

/-- The map `linkMatrix γ` kills the first columns of an orthogonal lift. -/
lemma IsOrthogonalLift.linkMatrix_mul_toCols₁ (hu : IsOrthogonalLift j γ v u) :
    linkMatrix γ * u.toCols₁ = 0 :=
  congrArg toCols₁ hu.linkMatrix_mul

/-- The first columns of an orthogonal lift lie in `A`. -/
lemma IsOrthogonalLift.toCols₁_eq_fromRows (hu : IsOrthogonalLift j γ v u) :
    u.toCols₁ = fromRows u.toCols₁.toRows₁ 0 := by
  ext (a | a | a) y
  · rfl
  · simpa [linkMatrix, Matrix.mul_apply, Matrix.one_apply] using
      congrFun₂ hu.linkMatrix_mul_toCols₁ (inl a) y
  · simpa [Matrix.mul_apply, Matrix.one_apply, splitGram, apply_ite star] using
      congrFun₂ hu.orthogonal_toCols₁ (inl a) y

/-- The first columns of an orthogonal lift are orthogonal to the frame `γ e_a`, `γ z`. This is
stated for their coordinates in `A` and the products of the `e_a` with that frame. -/
lemma IsOrthogonalLift.conjTranspose_isotropicRows_mul_eq_zero (hu : IsOrthogonalLift j γ v u) :
    (isotropicRows (S.frameProducts γ))ᴴ * u.toCols₁.toRows₁ = 0 := by
  have h_last : zRowBlockDiagonal (S.ratMiddle E) * linkMatrix γ * u.toCols₁ = 0 := by
    rw [Matrix.mul_assoc, hu.linkMatrix_mul_toCols₁, Matrix.mul_zero]
  have h_middle : u.toCols₁.toRows₂.toRows₁ = 0 :=
    congrArg (fun M ↦ M.toRows₂.toRows₁) hu.toCols₁_eq_fromRows
  rw [← neg_eq_zero, ← Matrix.mul_neg,
    isotropicRows_conjTranspose_mul_eq hu.orthogonal_toCols₁ h_last, h_middle, Matrix.mul_zero]

/-- The first columns of an orthogonal lift are orthogonal to both frames `e_a`, `z` and `γ e_a`,
`γ z`. -/
lemma IsOrthogonalLift.toCols₁_mul_framePair (hu : IsOrthogonalLift j γ v u) :
    u.toCols₁ᴴ * S.ratGram * framePair γ = 0 := by
  have h_image : u.toCols₁.toRows₁ᴴ * isotropicRows (S.frameProducts γ) = 0 := by
    simpa using congrArg conjTranspose hu.conjTranspose_isotropicRows_mul_eq_zero
  rw [hu.toCols₁_eq_fromRows]
  ext a (b | b)
  · cases b using lastCases <;> simp [Matrix.mul_apply, Matrix.one_apply, splitGram]
  · simpa [Matrix.mul_apply, Matrix.one_apply, frameGram, splitGram, mul_comm] using
      congrFun₂ h_image a b

/-- The first columns of an orthogonal lift are orthogonal to all its columns. -/
lemma IsOrthogonalLift.toCols₁_mul_self (hu : IsOrthogonalLift j γ v u) :
    u.toCols₁ᴴ * S.ratGram * u = 0 := by
  have h_row (a : Fin 𝔰.ϱ) (b : IndexNotBelow j ⊕ τ) : u (inr (inr a)) b = 0 := by
    simpa [Matrix.mul_apply, Matrix.one_apply, splitGram, apply_ite star] using
      congrFun₂ hu.orthogonal (inl a) b
  conv_lhs => rw [hu.toCols₁_eq_fromRows]
  ext a b
  simp [Matrix.mul_apply, Matrix.one_apply, splitGram, h_row]

/-- The isometry: the Gram matrix of the lifts of `v`, corrected by `N⁻¹` times their products with
`z` and `γ z`, is the Gram matrix of `v` for the positive form `S.linkMetric` on pairs of middle
coordinates. -/
lemma IsOrthogonalLift.gram_add_border (hu : IsOrthogonalLift j γ v u) :
    u.toCols₂ᴴ * S.ratGram * u.toCols₂ + (S.N⁻¹ : E) •
        (((lastPair γ)ᴴ * S.ratGram * u.toCols₂)ᴴ * ((lastPair γ)ᴴ * S.ratGram * u.toCols₂)) =
      vᴴ * S.linkMetric * v := by
  -- On vectors orthogonal to `A` and `γ A` the form factors through `linkMatrix γ`.
  classical
  have h_orth : (isotropicFramePair γ)ᴴ * S.ratGram * u.toCols₂ = 0 :=
    congrArg toCols₂ hu.orthogonal
  have h_link : linkMatrix γ * u.toCols₂ = v := congrArg toCols₂ hu.linkMatrix_mul
  have h_half : vᴴ * fromBlocks ((2⁻¹ : E) • S.ratMiddle E) 0 0 ((2⁻¹ : E) • S.ratMiddle E) * v =
      u.toCols₂ᴴ * S.ratGram * u.toCols₂ := by
    -- the product formula for `linkMatrix γ`, with the scalars `2⁻¹` and `-2⁻¹`
    have h := gram_linkMatrix_mul h_orth h_orth 2⁻¹ (-2⁻¹)
    rw [neg_neg, mul_inv_cancel, OneMemClass.coe_one, Units.val_one, Matrix.one_mul, ← sub_smul,
      show (2⁻¹ - -2⁻¹ : E) = 1 by norm_num, one_smul, h_link] at h
    exact h
  have h_last :
      (lastPair γ)ᴴ * S.ratGram * u.toCols₂ = zRowBlockDiagonal (S.ratMiddle E) * v := by
    rw [framePair_last_eq_zRowBlockDiagonal_mul, Matrix.mul_assoc, h_link]
  rw [← h_half, h_last, linkMetric]
  simp [fromBlocks_smul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]

end OrthogonalLift

/-! ### The two lists and their index -/

/-- The vectors `e_a` and `k e_a` with `a < j`, as columns. -/
abbrev listPair {R : Type} [CommRing R] [StarRing R] {T : 𝔰.Form R} (j : Fin (𝔰.ϱ + 2)) (k : T.G) :
    Matrix 𝔰.BesselIndex (IndexBelow j ⊕ IndexBelow j) R :=
  (isotropicFramePair k).submatrix id (.map Subtype.val Subtype.val)

/-- Take the Gram matrix of the vectors `e_a`, `γ e_a` (`a < j`), `z`, `γ z`, and add `N` to the
diagonal entries of `z` and `γ z`. The norm to `ℚ` of its determinant has the absolute value
`(Nm δ_*)²`, where `δ_* = S.subframeMinor j γ` is the determinant of the products of the subframe
`(e_a, z)`, `a < j`, with its image under `γ`. -/
lemma abs_norm_det_gram_eq_abs_norm_subframeMinor_sq :
    |(norm ℚ ((fromCols (listPair j γ) (lastPair γ))ᴴ * S.ratGram *
        fromCols (listPair j γ) (lastPair γ) + fromBlocks 0 0 0 ((S.N : E) • 1)).det : ℝ)| =
      |(norm ℚ (S.subframeMinor j γ) : ℝ)| ^ 2 := by
  set G : Matrix ((IndexBelow j ⊕ IndexBelow j) ⊕ Unit ⊕ Unit)
    ((IndexBelow j ⊕ IndexBelow j) ⊕ Unit ⊕ Unit) E :=
    (fromCols (listPair j γ) (lastPair γ))ᴴ * S.ratGram *
    fromCols (listPair j γ) (lastPair γ) + fromBlocks 0 0 0 ((S.N : E) • 1)
  let index : IndexBelow j ⊕ Unit → Fin (𝔰.ϱ + 1) := Sum.elim (·.1.castSucc) fun _ ↦ 𝔰.top
  let position : (IndexBelow j ⊕ IndexBelow j) ⊕ Unit ⊕ Unit → Fin (𝔰.ϱ + 1) ⊕ Fin (𝔰.ϱ + 1) :=
    Sum.elim (.map (·.1.castSucc) (·.1.castSucc)) (.map (fun _ ↦ 𝔰.top) fun _ ↦ 𝔰.top)
  let C : Matrix (IndexBelow j ⊕ Unit) (IndexBelow j ⊕ Unit) E :=
    (S.frameProducts γ).submatrix index index
  have h_mem (x : IndexBelow j ⊕ Unit) : index x ∈ subframeIndices j := by
    rcases x with x | x
    · simp [index, x.2]
    · simp [index]
  have h_bijective : Function.Bijective fun x ↦ (⟨index x, h_mem x⟩ : subframeIndices j) := by
    refine ⟨?_, fun ⟨a, ha⟩ ↦ ?_⟩
    · -- The index of `e_a` is never the last one, that of `z`.
      rintro (x | x) (x' | x') h <;>
        simp_all [index, Subtype.ext_iff, (castSucc_lt_last _).ne, (castSucc_lt_last _).ne']
    · cases a using lastCases with
      | last => exact ⟨inr (), rfl⟩
      | cast a => exact ⟨inl ⟨a, by simpa using ha⟩, rfl⟩
  have hC : C.det = S.subframeMinor j γ :=
    det_submatrix_equiv_self (.ofBijective _ h_bijective)
      ((S.frameProducts γ).submatrix Subtype.val Subtype.val)
  -- Order the vectors list by list, and exchange the two halves of the rows.
  let e : (IndexBelow j ⊕ Unit) ⊕ (IndexBelow j ⊕ Unit) ≃
      (IndexBelow j ⊕ IndexBelow j) ⊕ Unit ⊕ Unit :=
    sumSumSumComm (IndexBelow j) Unit (IndexBelow j) Unit
  let swap : Perm ((IndexBelow j ⊕ Unit) ⊕ (IndexBelow j ⊕ Unit)) :=
    sumComm (IndexBelow j ⊕ Unit) (IndexBelow j ⊕ Unit)
  have h_blocks : (G.submatrix e e).submatrix swap id = fromBlocks Cᴴ 0 0 C := by
    have h_gram : (framePair γ)ᴴ * S.ratGram * framePair γ =
        fromBlocks (single 𝔰.top 𝔰.top (-S.N : E)) (S.frameProducts γ) (S.frameProducts γ)ᴴ
          (single 𝔰.top 𝔰.top (-S.N : E)) := gram_framePair _ (by simp) γ
    have h_entry (x y : (IndexBelow j ⊕ IndexBelow j) ⊕ Unit ⊕ Unit) : G x y =
        ((framePair γ)ᴴ * S.ratGram * framePair γ) (position x) (position y) +
          fromBlocks 0 0 0 ((S.N : E) • 1) x y := by
      rcases x with (x | x) | (x | x) <;> rcases y with (y | y) | (y | y) <;> rfl
    ext ((a | a) | (a | a)) ((b | b) | (b | b)) <;>
      simp [h_entry, h_gram, C, e, swap, index, position, (castSucc_lt_last _).ne']
  have h_det : Perm.sign swap * G.det = star C.det * C.det := by
    rw [← det_submatrix_equiv_self e G, ← det_permute, h_blocks, det_fromBlocks_zero₂₁,
      det_conjTranspose]
  rw [← hC]
  simpa [sq, abs_norm_eq_prod_norm_sq, abs_unit_intCast] using
    congrArg (fun x : E ↦ |(norm ℚ x : ℝ)|) h_det

section Index

variable {k : S.GFin} {σ μ : Type} [Fintype σ] [Fintype μ] [DecidableEq μ]
  {ι : Matrix 𝔰.BesselIndex σ (𝔸f E)} {B : Matrix 𝔰.BesselIndex μ (𝔸f E)}
  {q : Matrix μ 𝔰.BesselIndex (𝔸f E)}

/-- Let `M` and `P` be matrices over the finite adeles `𝔸f E`, and call a vector integral if its
entries lie in the ring `Ô E` of integral finite adeles. Suppose that the columns of `P` lie in the
`𝔸f E`-span of those of `M`. Then the index of the `Ô E`-span `colLattice M` of the columns of `M`
in the integral vectors of the span of `P` divides the index of the integral vectors in the module
`preimageLattice M` of the `y` with `M y` integral. -/
lemma submoduleIndex_colLattice_dvd_preimageLattice {μ : Type} [Fintype μ] [DecidableEq μ]
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    {M : Matrix μ α (𝔸f E)} {P : Matrix μ β (𝔸f E)}
    (h_span : ∀ x : β, P.col x ∈ colSpan M) :
    submoduleIndex (colLattice (Ô E) M)
        (intVectors (Ô E) μ ⊓ (colSpan P).restrictScalars (Ô E)) ∣
      submoduleIndex (intVectors (Ô E) α) (preimageLattice (Ô E) M) := by
  refine submoduleIndex_dvd_of_le (M.mulVecLin.restrictScalars (Ô E))
    (fun x hx ↦ ⟨x, hx, rfl⟩) fun x ⟨hx_int, hx_span⟩ ↦ mem_sup_left ?_
  obtain ⟨y, rfl⟩ : x ∈ colSpan M := by
    choose w hw using h_span
    have h_eq : M * (of w)ᵀ = P := ext_col hw
    obtain ⟨y, rfl⟩ := hx_span
    exact ⟨(of w)ᵀ *ᵥ y, by rw [mulVecLin_apply, mulVec_mulVec, h_eq, mulVecLin_apply]⟩
  exact ⟨y, hx_int, rfl⟩

/-- Let `k` be finite-adelic, acting on the standard lattice with Gram matrix
`latticeMiddle.splitGram`. The products of the vectors `k e₁, …, k e_ϱ, k z` with the `e_a` form the
conjugate transpose of the rows `isotropicRows` of the `e_a` in the matrix `frameGram k` of frame
products, and those with the `k e_a` vanish. -/
lemma toRows₂_gram_framePair_isotropicFramePair (k : S.GFin) :
    ((framePair k)ᴴ * (S.latticeMiddle (𝔸f E)).splitGram * isotropicFramePair k).toRows₂ =
      fromCols (isotropicRows ((S.latticeMiddle (𝔸f E)).frameGram k))ᴴ 0 := by
  refine Matrix.ext fun a b ↦ ?_
  rcases b with b | b
  · simp [frameGram, splitGram, Matrix.mul_apply, Matrix.one_apply, apply_ite star]
  · have h_form : k.val.valᴴ * (S.latticeMiddle (𝔸f E)).splitGram * k.val.val =
        (S.latticeMiddle (𝔸f E)).splitGram := k.2
    refine (congrFun₂ h_form _ _).trans ?_
    cases a using lastCases <;> simp

/-- Let `k` be finite-adelic. The products of the vectors `e₁, …, e_ϱ, z` with the `e_a` vanish,
and those with the `k e_a` form the conjugate transpose of the rows `isotropicRows` of the `e_a` in
the matrix of frame products of `k⁻¹`. -/
lemma toRows₁_gram_framePair_isotropicFramePair (k : S.GFin) :
    ((framePair k)ᴴ * (S.latticeMiddle (𝔸f E)).splitGram * isotropicFramePair k).toRows₁ =
      fromCols 0 (isotropicRows ((S.latticeMiddle (𝔸f E)).frameGram k⁻¹.val.val))ᴴ := by
  refine Matrix.ext fun a b ↦ ?_
  rcases b with b | b
  · cases a using lastCases <;>
      simp [splitGram, Matrix.mul_apply, Matrix.one_apply, apply_ite star]
  · rw [frameGram_inv]
    simp [frameGram, Matrix.mul_apply, Matrix.one_apply, apply_ite star]

/-- Let `(ι, B, q)` be a basis of `(Λ ∩ I^⊥)/(Λ ∩ I)`, with `B` indexed by `μ`. Suppose `Λ ∩ I` lies
in the lattice of the columns `e_a`, `k e_a` of `isotropicFramePair k` and is orthogonal to them.
Then the torsion index `S.torsionIndex k` divides the index of the classes `q e_a`, `q k e_a` in
the integral vectors of their span. Here `Λ` is the standard lattice of integral vectors, `I` is the
span of the columns of `ι`, and the vectors `k e_a` are assumed integral. -/
lemma torsionIndex_dvd_submoduleIndex
    (hq : IsQuotientBasis (Ô E) (S.latticeMiddle (𝔸f E)).splitGram ι B q)
    (hk : IsIntMatrix (Ô E) (isotropicFramePair k))
    (h_orth : ιᴴ * (S.latticeMiddle (𝔸f E)).splitGram * isotropicFramePair k = 0)
    (hι : ∀ x : σ, ι.col x ∈ colLattice (Ô E) (isotropicFramePair k)) :
    S.torsionIndex k ∣ submoduleIndex (colLattice (Ô E) (q * isotropicFramePair k))
      (intVectors (Ô E) μ ⊓ (colSpan (q * isotropicFramePair k)).restrictScalars (Ô E)) := by
  classical
  obtain ⟨l, hl_int, hl⟩ := hq.exists_eq_add
  let P : Matrix μ (Fin 𝔰.ϱ ⊕ Fin 𝔰.ϱ) (𝔸f E) := q * isotropicFramePair k
  -- A vector in the span of the `e_a` and `k e_a` differs from the representative of its class by
  -- a vector of `I`.
  have h_class (y : Fin 𝔰.ϱ ⊕ Fin 𝔰.ϱ → 𝔸f E) : isotropicFramePair k *ᵥ y =
      ι *ᵥ l *ᵥ isotropicFramePair k *ᵥ y + B *ᵥ P *ᵥ y := by
    simp only [mulVec_mulVec, ← add_mulVec]
    rw [← hl h_orth]
  -- For `y` with `isotropicFramePair k *ᵥ y` integral, the correction in `I` is in the lattice of
  -- the `e_a` and `k e_a`.
  have h_correction {y : Fin 𝔰.ϱ ⊕ Fin 𝔰.ϱ → 𝔸f E}
      (hy : isotropicFramePair k *ᵥ y ∈ intVectors (Ô E) 𝔰.BesselIndex) :
      ι *ᵥ l *ᵥ isotropicFramePair k *ᵥ y ∈ colLattice (Ô E) (isotropicFramePair k) :=
    colLattice_le hι ⟨_, hl_int.mulVec hy, rfl⟩
  -- `B` maps the classes to representatives, which are congruent to the vectors modulo `ι`.
  refine submoduleIndex_dvd_of_le (B.mulVecLin.restrictScalars (Ô E)) ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    change B *ᵥ P *ᵥ y ∈ colLattice (Ô E) (isotropicFramePair k)
    rw [eq_sub_of_add_eq' (h_class y).symm]
    exact sub_mem ⟨y, hy, rfl⟩ (h_correction (hk.mulVec hy))
  · rintro _ ⟨hx, y, rfl⟩
    rw [mulVecLin_apply, h_class y]
    refine add_mem (mem_sup_right (h_correction hx))
      (mem_sup_left ⟨P *ᵥ y, ⟨?_, y, rfl⟩, rfl⟩)
    rw [← mulVec_mulVec]
    exact hq.isIntMatrix_coord.mulVec hx

/-- Let `k` be a finite-adelic element such that the frame `e₁, …, e_ϱ, z` and its image under `k`
(`framePair k`) are integral. Let `Λ` be the standard lattice of integral vectors and `I` the span
of the columns of `ι`. Let these columns be a basis of `Λ ∩ I`, orthogonal to the frame and its
image under `k` and in the lattice of the `e_a` and `k e_a`, and let `q` give the classes in
`(Λ ∩ I^⊥)/(Λ ∩ I)`. Suppose that the classes of the `e_a` and `k e_a` with `a < j` span those of
all `e_a` and `k e_a`. Consider the module `preimageLattice` of the coefficient vectors `y` for
which the combination `(q * listPair j k) y` of the classes with `a < j` is integral. Then the index
of the integral coefficient vectors in it (`0` if infinite) is a multiple of the product of
`S.isotropicRowsIndex j k`, `S.isotropicRowsIndex j k⁻¹` and the torsion index
`S.torsionIndex k`. -/
lemma isotropicRowsIndex_mul_dvd_submoduleIndex
    (hq : IsQuotientBasis (Ô E) (S.latticeMiddle (𝔸f E)).splitGram ι B q)
    (hk : IsIntMatrix (Ô E) (framePair k))
    (h_orth : ιᴴ * (S.latticeMiddle (𝔸f E)).splitGram * framePair k = 0)
    (hι : ∀ x : σ, ι.col x ∈ colLattice (Ô E) (isotropicFramePair k))
    (h_span : ∀ x : Fin 𝔰.ϱ ⊕ Fin 𝔰.ϱ,
      (q * isotropicFramePair k).col x ∈ colSpan (q * listPair j k)) :
    S.isotropicRowsIndex j k * S.isotropicRowsIndex j k⁻¹ * S.torsionIndex k ∣
      submoduleIndex (intVectors (Ô E) (IndexBelow j ⊕ IndexBelow j))
        (preimageLattice (Ô E) (q * listPair j k)) := by
  -- The chain `L₁ ⊆ L₂ ⊆ L₃ ⊆ L₄` adds in turn the classes of the `e_a`, those of the `k e_a`, and
  -- the integral vectors of their span. Each step has an index divisible by one of the factors.
  classical
  set J : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E) := (S.latticeMiddle (𝔸f E)).splitGram
  let P : Matrix μ (Fin 𝔰.ϱ ⊕ Fin 𝔰.ϱ) (𝔸f E) := q * isotropicFramePair k
  let L₁ : Submodule (Ô E) (μ → 𝔸f E) := colLattice (Ô E) (q * listPair j k)
  let L₂ : Submodule (Ô E) (μ → 𝔸f E) :=
    colLattice (Ô E) (P.submatrix id (.map id (Subtype.val : IndexBelow j → Fin 𝔰.ϱ)))
  let L₃ : Submodule (Ô E) (μ → 𝔸f E) := colLattice (Ô E) P
  let L₄ : Submodule (Ô E) (μ → 𝔸f E) :=
    intVectors (Ô E) μ ⊓ (colSpan P).restrictScalars (Ô E)
  have h_herm : Jᴴ = J := (S.isUnimodular_latticeMiddle.splitGram (R := Ô E)).1
  have h_pair : ιᴴ * J * isotropicFramePair k = 0 :=
    congrArg (fun M ↦ M.submatrix id (Sum.map castSucc castSucc)) h_orth
  -- The products with the two frames are defined on classes.
  have h_products : (framePair k)ᴴ * J * B * P = (framePair k)ᴴ * J * isotropicFramePair k :=
    hq.mul_basis_mul_coord (orthogonal_symm h_herm h_orth) h_pair
  have h_first : S.isotropicRowsIndex j k ∣ submoduleIndex L₁ L₂ := by
    let φ : Matrix (Fin (𝔰.ϱ + 1)) μ (𝔸f E) := ((framePair k)ᴴ * J * B).toRows₂
    have h_image : φ * P = fromCols (isotropicRows ((S.latticeMiddle (𝔸f E)).frameGram k))ᴴ 0 :=
      (congrArg toRows₂ h_products).trans (toRows₂_gram_framePair_isotropicFramePair k)
    have h_col (x : Fin 𝔰.ϱ ⊕ Fin 𝔰.ϱ) : φ *ᵥ P.col x =
        (fromCols (isotropicRows ((S.latticeMiddle (𝔸f E)).frameGram k))ᴴ 0).col x :=
      congrArg (Matrix.col · x) h_image
    refine submoduleIndex_dvd_of_le (mulVecBilin ℕ _ φ) (colLattice_le ?_)
      (colLattice_le fun a ↦ mem_sup_left ⟨_, col_mem_colLattice (inl a), h_col (inl a)⟩)
    rintro (a | a)
    · change φ *ᵥ P.col (inl a.1) ∈ colLattice (Ô E) _
      rw [h_col]
      exact col_mem_colLattice a
    · change φ *ᵥ P.col (inr a.1) ∈ colLattice (Ô E) _
      rw [h_col]
      exact zero_mem _
  have h_second : S.isotropicRowsIndex j k⁻¹ ∣ submoduleIndex L₂ L₃ := by
    let φ : Matrix (Fin (𝔰.ϱ + 1)) μ (𝔸f E) := ((framePair k)ᴴ * J * B).toRows₁
    have h_frame : φ * P =
        fromCols 0 (isotropicRows ((S.latticeMiddle (𝔸f E)).frameGram k⁻¹.val.val))ᴴ :=
      (congrArg toRows₁ h_products).trans (toRows₁_gram_framePair_isotropicFramePair k)
    have h_col (x : Fin 𝔰.ϱ ⊕ Fin 𝔰.ϱ) : φ *ᵥ P.col x =
        (fromCols 0 (isotropicRows ((S.latticeMiddle (𝔸f E)).frameGram k⁻¹.val.val))ᴴ).col x :=
      congrArg (Matrix.col · x) h_frame
    refine submoduleIndex_dvd_of_le (mulVecBilin ℕ _ φ) (colLattice_le ?_)
      (colLattice_le fun a ↦ mem_sup_left ⟨_, col_mem_colLattice (inr a), h_col (inr a)⟩)
    rintro (a | a)
    · change φ *ᵥ P.col (inl a) ∈ colLattice (Ô E) _
      rw [h_col]
      exact zero_mem _
    · change φ *ᵥ P.col (inr a.1) ∈ colLattice (Ô E) _
      rw [h_col]
      exact col_mem_colLattice a
  have hk' : IsIntMatrix (Ô E) (isotropicFramePair k) := fun a b ↦ hk a _
  have h_torsion : S.torsionIndex k ∣ submoduleIndex L₃ L₄ :=
    torsionIndex_dvd_submoduleIndex hq hk' h_pair hι
  have h₁₂ : L₁ ≤ L₂ := colLattice_le fun x ↦ by
    rcases x with a | a
    · exact col_mem_colLattice (inl a.1)
    · exact col_mem_colLattice (inr a)
  have h₂₃ : L₂ ≤ L₃ := colLattice_le fun x ↦ col_mem_colLattice _
  have h₃₄ : L₃ ≤ L₄ :=
    le_inf (colLattice_le fun x a ↦ hq.isIntMatrix_coord.mul hk' a x) LinearMap.map_le_range
  have h_chain : submoduleIndex L₁ L₂ * submoduleIndex L₂ L₃ * submoduleIndex L₃ L₄ =
      submoduleIndex L₁ L₄ := by
    rw [AddSubgroup.relIndex_mul_relIndex _ _ _ h₁₂ h₂₃,
      AddSubgroup.relIndex_mul_relIndex _ _ _ (h₁₂.trans h₂₃) h₃₄]
  exact (mul_dvd_mul (mul_dvd_mul h_first h_second) h_torsion).trans
    (h_chain.dvd.trans (submoduleIndex_colLattice_dvd_preimageLattice h_span))

end Index

end New.Filling
