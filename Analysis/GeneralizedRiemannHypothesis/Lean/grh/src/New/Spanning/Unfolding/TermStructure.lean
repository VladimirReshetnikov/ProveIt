import New.Spanning.Unfolding.Climbing

/-!
# The structure of a term

An element `γ` gives two frames, with the spans `A⁺` and `γ A⁺`, and two isotropic spaces `A` and
`γ A` with the intersection `I_γ`. This file describes `A⁺_γ = A⁺ + γ A⁺`, its radical and its
orthogonal complement, which modulo `I_γ` is isometric to `X₀^γ = X₀ ∩ Υ_γ⁻¹ X₀` by the map
`framePerpToX₀`. For an element that agrees and has `gr(γ) = 0` it proves that `A = A_{≤j} ⊕ I_γ`
and `γ A = γ A_{≤j} ⊕ I_γ` for `j = n - 1 - rk I_γ`, and that `j` is the cell rank of `γ`. It also
shows that `I_{u γ u'} = u I_γ` for `u`, `u'` in the unipotent group `U₀`, and that agreement
depends only on the double coset `U₀ γ U₀`. Finally it defines the set `Γ*` (`remainingTerms`) of
the terms that are left for the estimate of the second moment.

Here `n = ϱ + 1`, the frame is `e_1, …, e_{n-1}, z_N` (indexed from `0` in the code), `A` is spanned
by `e_1, …, e_{n-1}`, `A⁺ = A + E z_N`, and `A_{≤j}` is spanned by the first `j` vectors of the
frame. The space has rank `r` and `A^⊥ / A = X₀ ⊥ E z_N` with `X₀` of rank `k`. For `y` orthogonal
to `A` and `γ A` the classes of `y` and `γ⁻¹ y` are `y₀ + λ' z_N` and `y₀' + λ z_N`. A pair
`(μ, μ')` occurs at an index `a` if the two frames share a vector with coefficients `μ`, `μ'` at `a`
and `0` above `a`. In names, `_one` and `_coe` after a word for a span, as in `isotropicSpan_one`
and `flagSpan_coe`, refer to the frames `e_•` and `γ e_•`. The hypothesis `HasPrimitiveRoot5040 E`
says that `E` contains a primitive root of unity of order `5040`.

Notions from other files:
* `linkIsometry γ` is the link isometry `Υ_γ` of `X₀ ⊥ E z⁺` with `y₀ + λ z⁺ ↦ y₀' + λ' z⁺`.
* `termDisc γ` is `gr(γ) = |δ_n|² - N² |δ_{n-1}|²` for the leading minors `δ_j` of the matrix
  `frameProducts γ` of products of the two frames.
* `CharsAgree γ` (`γ` agrees) says that the character `unipotentChar` takes the same value at
  rational `u`, `u'` in `U₀` whenever `u γ = γ u'`.
* `HasCellRank j γ` says that one pair `(ζ, 1)` with `ζ ζ̄ = 1` occurs at all indices `a ≥ j`
  (`NormOnePairOccursFrom j γ`), that `δ_j ≠ 0`, and that `j = n` exactly when `gr(γ) ≠ 0`.

## Relation to the literature

See `New.Spanning.Unfolding.Climbing` for related work.
-/

noncomputable section

open Matrix Module Fin Sum Function

namespace New

/-- For an injection `e`, a vector `v` is a combination of the columns of `P` with indices in the
range of `e` if and only if it is a combination of all columns of `P` whose coefficients vanish
outside that range. -/
lemma mem_colSpan_submatrix {F m n n' : Type} [Field F] [Fintype n] [Fintype n']
    {P : Matrix m n F} {e : n' → n} (he : Injective e) {v : m → F} :
    v ∈ colSpan (P.submatrix id e) ↔
      ∃ x : n → F, (∀ a : n, a ∉ Set.range e → x a = 0) ∧ P *ᵥ x = v := by
  have h_sum (x : n → F) (hx : ∀ a ∉ Set.range e, x a = 0) :
      P.submatrix id e *ᵥ (x ∘ e) = P *ᵥ x :=
    funext fun i ↦ Fintype.sum_of_injective e he _ _ (fun a ha ↦ by simp [hx a ha]) fun _ ↦ rfl
  refine ⟨?_, fun ⟨x, hx, hv⟩ ↦ ⟨x ∘ e, (h_sum x hx).trans hv⟩⟩
  rintro ⟨c, rfl⟩
  have h_zero (a : n) (ha : a ∉ Set.range e) : extend e c 0 a = 0 := extend_apply' c _ a ha
  exact ⟨extend e c 0, h_zero, by rw [← h_sum _ h_zero, extend_comp he, mulVecLin_apply]⟩

namespace Filling

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰} {γ γ' : S.G E}
  {y : 𝔰.BesselIndex → E} {v : 𝔰.κ → E}

/-! ### The sum of the two frames and its orthogonal complement -/

/-- The space `A⁺_γ = A⁺ + γ A⁺`, where `A⁺` is the span of the frame `e_1, …, e_ϱ, z_N`. -/
def frameSum (γ : S.G E) : Submodule E (𝔰.BesselIndex → E) :=
  colSpan (frameImage 1) ⊔ colSpan (frameImage γ.val.val)

/-- The space `(A⁺_γ)^⊥` of the vectors orthogonal to both frames for the form `S.ratGram`. -/
def framePerp (γ : S.G E) : Submodule E (𝔰.BesselIndex → E) :=
  ((framePair γ)ᴴ * S.ratGram).mulVecLin.ker

variable (E 𝔰) in
/-- The inclusion of `X₀` in `X₀ ⊥ E z⁺`. -/
def inclPositive : (𝔰.κ → E) →ₗ[E] (𝔰.MiddleIndex → E) where
  toFun v := v ⊕ᵥ 0
  map_add' v w := by rw [← elim_add_add, add_zero]
  map_smul' c v := by ext (i | i) <;> simp

/-- The space `X₀^γ = X₀ ∩ Υ_γ⁻¹ X₀` of the vectors of `X₀` that the link maps into `X₀`. -/
def linkedX₀ (γ : S.G E) : Submodule E (𝔰.κ → E) :=
  (inclPositive E 𝔰).range.comap (linkIsometry γ ∘ₗ inclPositive E 𝔰)

/-- The map `y ↦ y₀` from `(A⁺_γ)^⊥` to `X₀`. -/
def framePerpToX₀ (γ : S.G E) : framePerp γ →ₗ[E] (𝔰.κ → E) :=
  (LinearMap.funLeft E E 𝔰.indexX₀).domRestrict (framePerp γ)

lemma framePerpToX₀_apply (y : framePerp γ) : framePerpToX₀ γ y = y.val ∘ 𝔰.indexX₀ := rfl

lemma mem_commonIsotropic_iff :
    y ∈ commonIsotropic γ ↔ y ∈ isotropicSpan 1 ∧ y ∈ isotropicSpan γ.val.val :=
  Submodule.mem_inf

lemma commonIsotropic_le_isotropicSpan_one (γ : S.G E) : commonIsotropic γ ≤ isotropicSpan 1 :=
  inf_le_left

lemma commonIsotropic_le_isotropicSpan_coe (γ : S.G E) :
    commonIsotropic γ ≤ isotropicSpan γ.val.val :=
  inf_le_right

omit [CMType E] in
/-- A vector of `X₀ ⊥ E z⁺` lies in `X₀` if and only if its coefficient at `z⁺` vanishes. -/
lemma mem_range_inclPositive {a : 𝔰.MiddleIndex → E} :
    a ∈ (inclPositive E 𝔰).range ↔ a (inr ()) = 0 := by
  refine ⟨?_, fun ha ↦ ⟨a ∘ inl, ?_⟩⟩
  · rintro ⟨w, rfl⟩
    rfl
  · ext (i | i)
    exacts [rfl, ha.symm]

/-- A vector `v` of `X₀` lies in `X₀^γ` if and only if its image `Υ_γ v` under the link isometry has
the coefficient `0` at `z⁺`. -/
lemma mem_linkedX₀ : v ∈ linkedX₀ γ ↔ linkIsometry γ (v ⊕ᵥ 0) (inr ()) = 0 := by
  rw [linkedX₀, Submodule.mem_comap, mem_range_inclPositive]
  rfl

/-- The columns of `framePair γ`, namely the frame `e_1, …, e_ϱ, z_N` and its image under `γ`, span
`A⁺_γ = A⁺ + γ A⁺` (`frameSum γ`). -/
lemma colSpan_framePair (γ : S.G E) : colSpan (framePair γ) = frameSum γ := by
  rw [frameSum, framePair, colSpan_fromCols]

/-- A vector `y` lies in `framePerp γ` if and only if its product, for the form `S.ratGram`, with
each vector of `frameSum γ = A⁺ + γ A⁺` vanishes. Here `A⁺ = ⟨e_1, …, e_ϱ, z_N⟩`. -/
lemma mem_framePerp_iff_orthogonal :
    y ∈ framePerp γ ↔ ∀ w ∈ frameSum γ, star w ⬝ᵥ S.ratGram *ᵥ y = 0 := by
  have h_form (c : Fin (𝔰.ϱ + 1) ⊕ Fin (𝔰.ϱ + 1) → E) :
      star (framePair γ *ᵥ c) ⬝ᵥ S.ratGram *ᵥ y =
        star c ⬝ᵥ ((framePair γ)ᴴ * S.ratGram) *ᵥ y := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
  rw [← colSpan_framePair, framePerp, LinearMap.mem_ker, mulVecLin_apply]
  refine ⟨?_, fun hy ↦ dotProduct_eq_zero _ fun c ↦ ?_⟩
  · rintro hy _ ⟨c, rfl⟩
    rw [mulVecLin_apply, h_form, hy, dotProduct_zero]
  · rw [dotProduct_comm, ← star_star c, ← h_form]
    exact hy _ ⟨star c, rfl⟩

/-- For the coefficients `x` of a combination of the frame `e_1, …, e_ϱ, z_N`, the product, for the
form `S.ratGram`, of this combination with `y` is the sum of `x̄_a y(e*_a)` over `a ≤ ϱ` minus
`N x̄_z y(z)`, where `x_z` is the last coefficient and `y(·)` are coordinates of `y`. -/
lemma form_frameImage_one (x : Fin (𝔰.ϱ + 1) → E) (y : 𝔰.BesselIndex → E) :
    star (frameImage 1 *ᵥ x) ⬝ᵥ S.ratGram *ᵥ y =
      ∑ a : Fin 𝔰.ϱ, star (x a.castSucc) * y (eStar a) - S.N * (star (x 𝔰.top) * y 𝔰.z) := by
  rw [frameImage_one_mulVec, splitGram_mulVec]
  simp [dotProduct, mulVec, Shape.middleGram, init, sub_eq_add_neg, mul_left_comm]

/-- For the form `S.ratGram`, the product of a combination with coefficients `x` of the frame
`frameImage γ` with `y` equals the product of the same combination of the frame `frameImage 1` with
`γ⁻¹ y`. -/
lemma form_frameImage_coe (x : Fin (𝔰.ϱ + 1) → E) (y : 𝔰.BesselIndex → E) :
    star (frameImage γ.val.val *ᵥ x) ⬝ᵥ S.ratGram *ᵥ y =
      star (frameImage 1 *ᵥ x) ⬝ᵥ S.ratGram *ᵥ γ⁻¹.val.val *ᵥ y := by
  rw [← U.form_mulVec_mulVec γ (frameImage 1 *ᵥ x), frameImage_mulVec γ.val.val]
  simp

/-- A vector `y` is orthogonal, for the form `S.ratGram`, to the span `A⁺` of the frame
`e_1, …, e_ϱ, z_N` (the columns of `frameImage 1`) if and only if its coordinates at the dual
vectors `e*_a` and at `z_N` vanish. -/
lemma orthogonal_frame_iff :
    (∀ x : Fin (𝔰.ϱ + 1) → E, star (frameImage 1 *ᵥ x) ⬝ᵥ S.ratGram *ᵥ y = 0) ↔
      (∀ a : Fin 𝔰.ϱ, y (eStar a) = 0) ∧ y 𝔰.z = 0 := by
  simp only [form_frameImage_one]
  refine ⟨fun h ↦ ⟨fun a ↦ ?_, ?_⟩, fun ⟨h_dual, h_z⟩ x ↦ by simp [h_dual, h_z]⟩
  · -- The vector `e_a` reads off the coordinate at `e*_a`.
    simpa [Pi.single_apply, castSucc_inj, (castSucc_ne_last a).symm, apply_ite star]
      using h (Pi.single a.castSucc 1)
  · -- The vector `z_N` has the norm `-N ≠ 0`.
    simpa [Pi.single_apply, castSucc_ne_last, S.N_prime.ne_zero] using h (Pi.single 𝔰.top 1)

/-- Let `A⁺_γ = A⁺ + γ A⁺`, where `A⁺ = ⟨e_1, …, e_ϱ, z_N⟩`, and take orthogonal complements for the
hermitian form `S.ratGram`. A vector `y` lies in `(A⁺_γ)^⊥` if and only if it is orthogonal to
`A = ⟨e_1, …, e_ϱ⟩` and to `γ A` and both `λ' = 0` and `λ = 0`. -/
lemma mem_framePerp :
    y ∈ framePerp γ ↔ y ∈ isotropicPerp γ ∧ y 𝔰.z = 0 ∧ (γ⁻¹.val.val *ᵥ y) 𝔰.z = 0 := by
  have h_split : y ∈ framePerp γ ↔
      (∀ x : Fin (𝔰.ϱ + 1) → E, star (frameImage 1 *ᵥ x) ⬝ᵥ S.ratGram *ᵥ y = 0) ∧
      ∀ x : Fin (𝔰.ϱ + 1) → E, star (frameImage γ.val.val *ᵥ x) ⬝ᵥ S.ratGram *ᵥ y = 0 := by
    rw [mem_framePerp_iff_orthogonal, frameSum]
    refine ⟨fun h ↦ ⟨fun x ↦ h _ (Submodule.mem_sup_left ⟨x, rfl⟩),
      fun x ↦ h _ (Submodule.mem_sup_right ⟨x, rfl⟩)⟩, fun ⟨h_one, h_coe⟩ w hw ↦ ?_⟩
    obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hw
    simp [add_dotProduct, h_one, h_coe]
  simp only [h_split, form_frameImage_coe, orthogonal_frame_iff, mem_isotropicPerp]
  exact and_and_and_comm

/-- For `y` in `(A⁺_γ)^⊥` the link isometry `Υ_γ` sends the `X₀`-part of `y` to the `X₀`-part of
`γ⁻¹ y`. -/
lemma linkIsometry_comp_indexX₀ (hy : y ∈ framePerp γ) :
    linkIsometry γ ((y ∘ 𝔰.indexX₀) ⊕ᵥ 0) = ((γ⁻¹.val.val *ᵥ y) ∘ 𝔰.indexX₀) ⊕ᵥ 0 := by
  obtain ⟨hy_perp, hy_z, hγy_z⟩ := mem_framePerp.1 hy
  have h_image : linkIsometry γ (linkSource E 𝔰 (linkMatrix γ *ᵥ y)) =
      linkTarget E 𝔰 (linkMatrix γ *ᵥ y) :=
    linkIsometry_linkSource (linkMatrix_mulVec_mem_link hy_perp)
  rwa [linkSource_linkMatrix_mulVec, linkTarget_linkMatrix_mulVec, hy_z, hγy_z] at h_image

/-- Let `Υ_γ` be the link isometry of `X₀ ⊥ E z⁺`, where `z⁺` is a vector of norm `N`: for `y`
orthogonal to `A` and `γ A` it sends `y₀ + λ z⁺` to `y₀' + λ' z⁺`, where `y₀`, `y₀'` are the
`X₀`-parts of `y`, `γ⁻¹ y` and `λ'`, `λ` their coordinates at `z_N`. Then every `v` in `X₀` is the
`X₀`-part of some such `y` with `λ = 0`, and the coefficient of `Υ_γ v` at `z⁺` is `λ'`. -/
lemma exists_mem_isotropicPerp_comp_eq (γ : S.G E) (v : 𝔰.κ → E) :
    ∃ y ∈ isotropicPerp γ, y ∘ 𝔰.indexX₀ = v ∧ (γ⁻¹.val.val *ᵥ y) 𝔰.z = 0 ∧
      linkIsometry γ (v ⊕ᵥ 0) (inr ()) = y 𝔰.z := by
  obtain ⟨⟨y, hy⟩, h_source⟩ : ∃ y : isotropicPerp γ, perpToPositive γ y = v ⊕ᵥ 0 :=
    (ker_perpToPositive_and_surjective γ).2.2 _
  rw [perpToPositive_apply] at h_source
  have h_link : linkIsometry γ (v ⊕ᵥ 0) = linkTarget E 𝔰 (linkMatrix γ *ᵥ y) := by
    rw [← h_source, linkIsometry_linkSource (linkMatrix_mulVec_mem_link hy)]
  rw [linkSource_linkMatrix_mulVec] at h_source
  refine ⟨y, hy, funext fun i ↦ congrFun h_source (inl i), congrFun h_source (inr ()), ?_⟩
  rw [h_link, linkTarget_linkMatrix_mulVec, elim_inr]

/-- The image of the map `framePerpToX₀ γ` (`y ↦ y₀`, taking the coordinates in `X₀`) is
`linkedX₀ γ`. The map is defined on `(A⁺_γ)^⊥`, the vectors orthogonal for `S.ratGram` to the frame
`e_1, …, e_ϱ, z_N` and to its image under `γ`. The space `linkedX₀ γ` = `X₀^γ` consists of the
vectors of `X₀` that the link isometry maps into `X₀`. -/
theorem range_framePerpToX₀ (γ : S.G E) : (framePerpToX₀ γ).range = linkedX₀ γ := by
  ext v
  rw [mem_linkedX₀]
  refine ⟨?_, fun hv ↦ ?_⟩
  · rintro ⟨⟨y, hy⟩, rfl⟩
    rw [framePerpToX₀_apply, linkIsometry_comp_indexX₀ hy, elim_inr, Pi.zero_apply]
  · obtain ⟨y, hy_perp, hy_X₀, hγy_z, h_link⟩ := exists_mem_isotropicPerp_comp_eq γ v
    exact ⟨⟨y, mem_framePerp.2 ⟨hy_perp, h_link.symm.trans hv, hγy_z⟩⟩, hy_X₀⟩

/-- The map `y ↦ y₀` from `(A⁺_γ)^⊥` to `X₀` sends the form `S.ratGram` of the whole space to the
standard hermitian product of `X₀`. -/
theorem form_framePerpToX₀ (y y' : framePerp γ) :
    star (framePerpToX₀ γ y) ⬝ᵥ framePerpToX₀ γ y' = star y.val ⬝ᵥ S.ratGram *ᵥ y'.val := by
  obtain ⟨hy_perp, hy_z, -⟩ := mem_framePerp.1 y.2
  obtain ⟨hy_dual, -⟩ := mem_isotropicPerp.1 hy_perp
  obtain ⟨hy'_dual, -⟩ := mem_isotropicPerp.1 (mem_framePerp.1 y'.2).1
  -- The product of `y` and `y'` is that of their middle blocks, and the `z_N`-part of `y` vanishes.
  rw [ratGram_form_of_eStar_eq_zero hy_dual hy'_dual, dotProduct_ratMiddle_mulVec_eq_sum_sub, hy_z]
  simp [framePerpToX₀_apply, dotProduct]

/-- The space `I_γ = A ∩ γ A` is orthogonal to both frames. -/
lemma commonIsotropic_le_framePerp (γ : S.G E) : commonIsotropic γ ≤ framePerp γ := by
  intro y hy
  obtain ⟨hy_perp, h_zero⟩ := mem_commonIsotropic.1 hy
  simp only [linkMatrix_mulVec, funext_iff] at h_zero
  exact mem_framePerp.2 ⟨hy_perp, h_zero (inl (inr ())), h_zero (inr (inr ()))⟩

/-- For `γ` in the group `S.G E`, the kernel of `framePerpToX₀ γ` is `commonIsotropic γ = A ∩ γ A`,
seen inside `framePerp γ`. -/
theorem ker_framePerpToX₀ (γ : S.G E) :
    (framePerpToX₀ γ).ker = (commonIsotropic γ).submoduleOf (framePerp γ) := by
  ext ⟨y, hy⟩
  obtain ⟨hy_perp, -, hγy_z⟩ := mem_framePerp.1 hy
  obtain ⟨-, h_ker, -⟩ := ker_perpToPositive_and_surjective γ
  -- As `λ = 0`, the image `y₀ + λ z⁺` of `y` vanishes if and only if `y₀` does.
  calc (⟨y, hy⟩ : framePerp γ) ∈ (framePerpToX₀ γ).ker
    _ ↔ (⟨y, hy_perp⟩ : isotropicPerp γ) ∈ (perpToPositive γ).ker := by
      rw [LinearMap.mem_ker, LinearMap.mem_ker, framePerpToX₀_apply, perpToPositive_apply,
        linkSource_linkMatrix_mulVec, hγy_z]
      simp [funext_iff]
    _ ↔ (⟨y, hy⟩ : framePerp γ) ∈ (commonIsotropic γ).submoduleOf (framePerp γ) := by
      simp [h_ker, Submodule.submoduleOf]

/-- A vector `y` of `framePerp γ = (A⁺_γ)^⊥` is isotropic for the form `S.ratGram` if and only if it
lies in `commonIsotropic γ = A ∩ γ A`, where `A = ⟨e_1, …, e_ϱ⟩`. -/
lemma form_self_eq_zero_iff_mem_commonIsotropic (hy : y ∈ framePerp γ) :
    star y ⬝ᵥ S.ratGram *ᵥ y = 0 ↔ y ∈ commonIsotropic γ := by
  have h_ker : framePerpToX₀ γ ⟨y, hy⟩ = 0 ↔ y ∈ commonIsotropic γ := by
    simp [← LinearMap.mem_ker, ker_framePerpToX₀, Submodule.submoduleOf]
  rw [← h_ker, ← form_framePerpToX₀ ⟨y, hy⟩ ⟨y, hy⟩]
  refine ⟨fun h_norm ↦ ?_, fun h ↦ by rw [h, dotProduct_zero]⟩
  -- The form of `X₀ ⊥ E z⁺` has no nonzero isotropic vector, hence neither has that of `X₀`.
  have h_zero : (framePerpToX₀ γ ⟨y, hy⟩ ⊕ᵥ 0 : 𝔰.MiddleIndex → E) = 0 :=
    eq_zero_of_positiveGram_form_eq_zero (S := S)
      (by rw [dotProduct_positiveGram_mulVec_eq_sum_add]; simpa [dotProduct] using h_norm)
  exact funext fun i ↦ congrFun h_zero (inl i)

omit [CMType E] in
/-- The space `M A`, spanned by `M e_1, …, M e_ϱ`, lies in `M A⁺`, the span of the columns of
`frameImage M`, which are the images under `M` of the frame `e_1, …, e_ϱ, z`. -/
lemma isotropicSpan_le_colSpan_frameImage (M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) :
    isotropicSpan M ≤ colSpan (frameImage M) := by
  intro w hw
  exact ((mem_colSpan_submatrix (castSucc_injective 𝔰.ϱ)).1 hw).imp fun x hx ↦ hx.2

lemma commonIsotropic_le_colSpan_frameImage_one (γ : S.G E) :
    commonIsotropic γ ≤ colSpan (frameImage 1) :=
  (commonIsotropic_le_isotropicSpan_one γ).trans (isotropicSpan_le_colSpan_frameImage 1)

lemma commonIsotropic_le_colSpan_frameImage_coe (γ : S.G E) :
    commonIsotropic γ ≤ colSpan (frameImage γ.val.val) :=
  (commonIsotropic_le_isotropicSpan_coe γ).trans (isotropicSpan_le_colSpan_frameImage γ.val.val)

/-- The space `I_γ = A ∩ γ A` is the radical of `A⁺_γ = A⁺ + γ A⁺`, that is, the intersection of
`A⁺_γ` with its orthogonal complement. -/
theorem frameSum_inf_framePerp (γ : S.G E) : frameSum γ ⊓ framePerp γ = commonIsotropic γ := by
  refine le_antisymm ?_ (le_inf ?_ (commonIsotropic_le_framePerp γ))
  · rintro y ⟨h_sum, h_perp⟩
    exact (form_self_eq_zero_iff_mem_commonIsotropic h_perp).1
      (mem_framePerp_iff_orthogonal.1 h_perp y h_sum)
  · exact le_sup_of_le_left (commonIsotropic_le_colSpan_frameImage_one γ)

/-- A vector `p` on two copies of the middle coordinates lies in the kernel of
`zRowBlockDiagonal (S.ratMiddle E)` (two copies of the `z`-row of the Gram matrix) if and only if
both `z`-coordinates of `p` are `0`. -/
lemma mem_ker_zRowBlockDiagonal {p : 𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E} :
    p ∈ (zRowBlockDiagonal (S.ratMiddle E)).mulVecLin.ker ↔
      p (inl (inr ())) = 0 ∧ p (inr (inr ())) = 0 := by
  simp [funext_iff, Shape.middleGram, mulVec, dotProduct, S.N_prime.ne_zero]

/-- For `γ`, `γ'` in the rational unitary group `S.G E` and a vector `v` of the definite space `X₀`,
`v` lies in `commonLink γ γ'` if and only if two conditions hold. The first condition is that `v`
lies in `linkedX₀ γ`, the vectors of `X₀` that `linkIsometry γ` maps into `X₀`. The second is that
the isometries `linkIsometry γ` and `linkIsometry γ'` of `X₀ ⊥ E z⁺` agree at `v ⊕ᵥ 0`, the vector
with `X₀`-part `v` and zero `z⁺`-coordinate. -/
theorem mem_commonLink : v ∈ commonLink γ γ' ↔
    v ∈ linkedX₀ γ ∧ linkIsometry γ (v ⊕ᵥ 0) = linkIsometry γ' (v ⊕ᵥ 0) := by
  -- A pair orthogonal to `z_N` in both links is determined by its image `v` under `linkSource`.
  rw [mem_linkedX₀]
  constructor
  · rintro ⟨p, ⟨⟨hp, hp'⟩, hp_ker⟩, rfl⟩
    obtain ⟨h_left, h_right⟩ := mem_ker_zRowBlockDiagonal.1 hp_ker
    have h_source : LinearMap.funLeft E E (inl ∘ inl) p ⊕ᵥ 0 = linkSource E 𝔰 p := by
      ext (i | i)
      exacts [rfl, h_right.symm]
    rw [h_source, linkIsometry_linkSource hp, linkIsometry_linkSource hp']
    exact ⟨h_left, rfl⟩
  · rintro ⟨hv, h_eq⟩
    obtain ⟨p, hp, h_source⟩ := exists_mem_link_linkSource_eq γ (v ⊕ᵥ 0)
    have h_target : linkIsometry γ (v ⊕ᵥ 0) = linkTarget E 𝔰 p := by
      rw [← h_source, linkIsometry_linkSource hp]
    have hp' : p ∈ link γ' := by rw [mem_link_iff_linkIsometry, h_source, ← h_eq, h_target]
    exact ⟨p, ⟨⟨hp, hp'⟩, mem_ker_zRowBlockDiagonal.2
      ⟨(congrFun h_target (inr ())).symm.trans hv, congrFun h_source (inr ())⟩⟩,
      funext fun i ↦ congrFun h_source (inl i)⟩

/-- For `γ' = γ` the condition `Υ_γ v = Υ_γ' v` always holds, so `commonLink γ γ` is `X₀^γ`. -/
theorem commonLink_self (γ : S.G E) : commonLink γ γ = linkedX₀ γ :=
  Submodule.ext fun _ ↦ mem_commonLink.trans (and_iff_left rfl)

/-- The space `commonLink γ γ'` lies in `X₀^γ ∩ X₀^γ'`. It consists of the `x` in `X₀` that are the
`X₀`-coordinates of the first vector of a pair of middle vectors that are orthogonal to `z` and lie
in the links of both `γ` and `γ'`. -/
lemma commonLink_le_linkedX₀_inf (γ γ' : S.G E) : commonLink γ γ' ≤ linkedX₀ γ ⊓ linkedX₀ γ' := by
  intro v hv
  obtain ⟨hv_mem, h_eq⟩ := mem_commonLink.1 hv
  exact ⟨hv_mem, mem_linkedX₀.2 (by rwa [← h_eq, ← mem_linkedX₀])⟩

/-- The rank of `commonLink γ γ'` equals the rank of the space of pairs that lie in both `link γ`
and `link γ'` and are killed by `zRowBlockDiagonal (S.ratMiddle E)`, that is, whose two vectors are
orthogonal to z. -/
lemma finrank_commonLink (γ γ' : S.G E) :
    finrank E (commonLink γ γ') =
      finrank E ↥(link γ ⊓ link γ' ⊓ (zRowBlockDiagonal (S.ratMiddle E)).mulVecLin.ker) := by
  rw [commonLink, ← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj]
  refine (injective_iff_map_eq_zero _).2 fun ⟨p, ⟨hp, _⟩, hp_ker⟩ h_zero ↦ Subtype.ext ?_
  refine eq_zero_of_linkSource_or_linkTarget_eq_zero hp (.inl <| funext ?_)
  rintro (i | -)
  exacts [congrFun h_zero i, (mem_ker_zRowBlockDiagonal.1 hp_ker).2]

/-- The space `link γ` consists of the pairs of classes of `y` and `γ⁻¹ y` in `A^⊥ / A = X₀ ⊥ E z_N`
for `y` orthogonal to `A = ⟨e_1, …, e_ϱ⟩` and `γ A`. The space `X₀^γ = linkedX₀ γ` consists of the
vectors of `X₀` that `Υ_γ` maps into `X₀`, and `commonLink γ γ'` of the vectors of `X₀^γ` on which
`Υ_γ` and `Υ_γ'` coincide. Then `rk X₀^γ + rk (link γ ∩ link γ') ≤ rk (commonLink γ γ') + (k + 1)`:
the corank of `commonLink γ γ'` in `X₀^γ` is at most the corank of `link γ ∩ link γ'` in
`link γ`. -/
lemma finrank_linkedX₀_add_finrank_inf_le (γ γ' : S.G E) :
    finrank E (linkedX₀ γ) + finrank E ↥(link γ ⊓ link γ') ≤
      finrank E (commonLink γ γ') + (𝔰.k + 1) := by
  rw [← commonLink_self, finrank_commonLink, finrank_commonLink, inf_idem]
  set K : Submodule E (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E) :=
    (zRowBlockDiagonal (S.ratMiddle E)).mulVecLin.ker
  have h_sup : finrank E ↥(link γ ⊓ K ⊔ link γ ⊓ link γ') ≤ 𝔰.k + 1 :=
    (Submodule.finrank_mono (sup_le inf_le_left inf_le_left)).trans (finrank_link γ).le
  rw [← Submodule.finrank_sup_add_finrank_inf_eq,
    show link γ ⊓ K ⊓ (link γ ⊓ link γ') = link γ ⊓ link γ' ⊓ K by order]
  omega

/-- Let the pair `(ζ, 1)` occur at the last index `𝔰.top`: a combination of the frame
`e_1, …, e_ϱ, z_N` with coefficient `ζ` at `z_N` equals a combination of its image under `γ` with
coefficient `1` at `γ z_N`. Then `λ = ζ̄ λ'` for every `y` orthogonal to `A = ⟨e_1, …, e_ϱ⟩` and to
`γ A`. -/
lemma inv_mulVec_z_eq_of_pairOccursAt {ζ : E} (h_pair : PairOccursAt γ ζ 1 𝔰.top)
    (hy : y ∈ isotropicPerp γ) : (γ⁻¹.val.val *ᵥ y) 𝔰.z = star ζ * y 𝔰.z := by
  obtain ⟨x, x', hxx', hx, hx', -⟩ := h_pair
  obtain ⟨h_dual, hγ_dual⟩ := mem_isotropicPerp.1 hy
  -- Pair `y` with the common vector, written in the two frames: this gives `-N ζ̄ λ' = -N λ`.
  have h_form : star (frameImage 1 *ᵥ x) ⬝ᵥ S.ratGram *ᵥ y =
      star (frameImage 1 *ᵥ x') ⬝ᵥ S.ratGram *ᵥ γ⁻¹.val.val *ᵥ y := by
    rw [hxx', form_frameImage_coe]
  simp only [form_frameImage_one, h_dual, hγ_dual, hx, hx'] at h_form
  simpa [S.N_prime.ne_zero] using h_form.symm

/-- If `γ` has cell rank `j` (`S.HasCellRank j γ`), which includes that `j = ϱ + 1` exactly when
`gr(γ) = S.termDisc γ ≠ 0`, and `S.termDisc γ = 0`, then `j ≤ ϱ`. -/
lemma HasCellRank.le_of_termDisc_eq_zero {j : Fin (𝔰.ϱ + 2)} (h_rank : S.HasCellRank j γ)
    (h_disc : S.termDisc γ = 0) : j.val ≤ 𝔰.ϱ :=
  not_lt.1 fun h_lt ↦ h_rank.lt_iff_termDisc_ne_zero.1 h_lt h_disc

/-- If `γ` has cell rank `j` and `S.termDisc γ = 0`, then the link isometry `Υ_γ` maps `X₀` into
itself: `linkedX₀ γ` is all of `X₀`. -/
lemma HasCellRank.linkedX₀_eq_top {j : Fin (𝔰.ϱ + 2)} (h_rank : S.HasCellRank j γ)
    (h_disc : S.termDisc γ = 0) : linkedX₀ γ = ⊤ := by
  have hj_le : j.val ≤ 𝔰.ϱ := h_rank.le_of_termDisc_eq_zero h_disc
  obtain ⟨⟨ζ, hζ, h_pairs⟩, -, -⟩ := h_rank
  refine Submodule.eq_top_iff'.2 fun v ↦ ?_
  obtain ⟨y, hy, -, hγy_z, h_link⟩ := exists_mem_isotropicPerp_comp_eq γ v
  -- Here `0 = λ = ζ̄ λ'` with `ζ̄ ≠ 0`, so `λ' = 0`.
  rw [inv_mulVec_z_eq_of_pairOccursAt (h_pairs 𝔰.top hj_le) hy] at hγy_z
  rw [mem_linkedX₀, h_link]
  exact (mul_eq_zero_iff_left (right_ne_zero_of_mul_eq_one hζ)).1 hγy_z

/-- Let `E` contain a primitive root of unity of order `5040`. If `γ` agrees and
`gr(γ) = S.termDisc γ` vanishes, then the link of `γ` maps all of `X₀` into `X₀`, that is,
`X₀^γ = X₀`. -/
theorem CharsAgree.linkedX₀_eq_top [HasPrimitiveRoot5040 E] (h_agree : S.CharsAgree γ)
    (h_disc : S.termDisc γ = 0) : linkedX₀ γ = ⊤ :=
  h_agree.exists_hasCellRank h_disc |>.elim fun _ h_rank ↦ h_rank.linkedX₀_eq_top h_disc

/-- If `gr(γ) = S.termDisc γ` is not zero, then the span `A⁺` of the frame `e_1, …, e_ϱ, z_N` and
the span `γ A⁺` of its image have the intersection `0`. -/
theorem disjoint_colSpan_frameImage (h_disc : S.termDisc γ ≠ 0) :
    Disjoint (colSpan (frameImage 1))
      (colSpan (frameImage (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E))) :=
  disjoint_iff.2 <| by_contra fun h_ne ↦ h_disc (termDisc_eq_zero_iff.2 h_ne)

/-- If `gr(γ) = S.termDisc γ` is not zero, then `I_γ = A ∩ γ A` is zero, where
`A = ⟨e_1, …, e_ϱ⟩`. -/
lemma commonIsotropic_eq_bot (h_disc : S.termDisc γ ≠ 0) : commonIsotropic γ = ⊥ :=
  disjoint_self.1 ((disjoint_colSpan_frameImage h_disc).mono
    (commonIsotropic_le_colSpan_frameImage_one γ) (commonIsotropic_le_colSpan_frameImage_coe γ))

/-- The span `γ A⁺` of the image under `γ` of the frame `e_1, …, e_ϱ, z_N` has the rank
`n = ϱ + 1`. -/
lemma finrank_colSpan_frameImage (γ : S.G E) :
    finrank E (colSpan (frameImage (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E))) = 𝔰.n := by
  rw [LinearMap.finrank_range_of_inj ((injective_iff_map_eq_zero _).2 fun _ ↦
    frameImage_mulVec_eq_zero_iff.1), finrank_fin_fun]

/-- The ranks of `frameSum γ` = `A⁺_γ = A⁺ + γ A⁺` (the span of the frame and of its image under
`γ`) and of its orthogonal complement `framePerp γ` add up to `𝔰.r`, the rank of the whole space. -/
lemma finrank_frameSum_add_finrank_framePerp (γ : S.G E) :
    finrank E (frameSum γ) + finrank E (framePerp γ) = 𝔰.r := by
  have h_unit : IsUnit S.ratGram.det := (isUnit_iff_isUnit_det _).1 Floors.IsHermitianUnit.isUnit
  have h_rank : ((framePair γ)ᴴ * S.ratGram).rank = finrank E (frameSum γ) := by
    rw [rank_mul_eq_left_of_isUnit_det _ _ h_unit, rank_conjTranspose_eq, ← colSpan_framePair]
    rfl
  rw [← h_rank, Shape.r, ← finrank_fintype_fun_eq_card E, framePerp]
  exact ((framePair γ)ᴴ * S.ratGram).mulVecLin.finrank_range_add_finrank_ker

/-- The space `X₀^γ` of the vectors of `X₀` that the link of `γ` maps into `X₀` has the rank of
`(A⁺_γ)^⊥ / I_γ`, where `A⁺_γ = A⁺ + γ A⁺` and `I_γ = A ∩ γ A`. -/
lemma finrank_linkedX₀_add_finrank_commonIsotropic (γ : S.G E) :
    finrank E (linkedX₀ γ) + finrank E (commonIsotropic γ) = finrank E (framePerp γ) := by
  rw [← (framePerpToX₀ γ).finrank_range_add_finrank_ker, range_framePerpToX₀, ker_framePerpToX₀,
    (Submodule.submoduleOfEquivOfLe (commonIsotropic_le_framePerp γ)).finrank_eq]

/-- If `gr(γ) = S.termDisc γ` is not zero, then `A⁺_γ = A⁺ + γ A⁺`, the span of the frame and of its
image under `γ`, has the rank `𝔰.n + 𝔰.n`. -/
lemma finrank_frameSum_of_termDisc_ne_zero (h_disc : S.termDisc γ ≠ 0) :
    finrank E (frameSum γ) = 𝔰.n + 𝔰.n := by
  have h_one : finrank E (colSpan (frameImage (𝔰 := 𝔰) (R := E) 1)) = 𝔰.n :=
    finrank_colSpan_frameImage (1 : S.G E)
  rw [frameSum, ← add_zero (finrank E _), ← finrank_bot E (𝔰.BesselIndex → E),
    ← (disjoint_colSpan_frameImage h_disc).eq_bot, Submodule.finrank_sup_add_finrank_inf_eq, h_one,
    finrank_colSpan_frameImage]

/-- If `gr(γ) = S.termDisc γ` is not zero, then the space `X₀^γ` of the vectors of
`X₀ = 𝔰.κ → E` that the link `linkIsometry γ` (an isometry of `X₀ ⊥ E z⁺`) maps into `X₀` is a
hyperplane of `X₀`: its rank is `r - 2 n = k - 1`. -/
theorem finrank_linkedX₀_add_one (h_disc : S.termDisc γ ≠ 0) :
    finrank E (linkedX₀ γ) + 1 = 𝔰.k := by
  have h_quot : finrank E (linkedX₀ γ) = finrank E (framePerp γ) := by
    rw [← finrank_linkedX₀_add_finrank_commonIsotropic, commonIsotropic_eq_bot h_disc, finrank_bot,
      add_zero]
  have h_perp : 𝔰.n + 𝔰.n + finrank E (framePerp γ) = 𝔰.r := by
    rw [← finrank_frameSum_of_termDisc_ne_zero h_disc, finrank_frameSum_add_finrank_framePerp]
  have h_r : 𝔰.r = 𝔰.ϱ + (𝔰.k + 1 + 𝔰.ϱ) := by simp [Shape.r]
  have h_n : 𝔰.n = 𝔰.ϱ + 1 := rfl
  lia

/-- If `γ` has the cell rank `j`, then `finrank E (linkedX₀ γ) + (j - ϱ) = 𝔰.k`, the dimension of
`X₀`. So `X₀^γ` has corank `1` in `X₀` for `j = ϱ + 1` and corank `0` otherwise. -/
lemma HasCellRank.finrank_linkedX₀_add_sub {j : Fin (𝔰.ϱ + 2)} (h_rank : S.HasCellRank j γ) :
    finrank E (linkedX₀ γ) + (j.val - 𝔰.ϱ) = 𝔰.k := by
  by_cases h_disc : S.termDisc γ = 0
  · rw [h_rank.linkedX₀_eq_top h_disc, Nat.sub_eq_zero_of_le
      (h_rank.le_of_termDisc_eq_zero h_disc), finrank_top, finrank_fintype_fun_eq_card, add_zero]
  · have h_top : 𝔰.ϱ < j.val := h_rank.lt_iff_termDisc_ne_zero.2 h_disc
    have h_one : j.val - 𝔰.ϱ = 1 := by omega
    rw [h_one, finrank_linkedX₀_add_one h_disc]

/-! ### The flags of the two frames and the cell rank -/

/-- The space `M A_{≤j}` spanned by the images under `M` of the first `j` vectors of the frame
`e_1, …, e_ϱ, z_N`. -/
def flagSpan (M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) (j : Fin (𝔰.ϱ + 2)) :
    Submodule E (𝔰.BesselIndex → E) :=
  colSpan ((frameImage M).submatrix id (castLE j.is_le))

omit [CMType E] in
/-- The vectors of `M A_{≤j}`, the span of the first `j` vectors of the frame `M e_•`, are the
combinations of that frame whose coefficients vanish from the index `j` on. -/
lemma mem_flagSpan {M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E} {j : Fin (𝔰.ϱ + 2)} :
    y ∈ flagSpan M j ↔ ∃ x : Fin (𝔰.ϱ + 1) → E,
      (∀ a : Fin (𝔰.ϱ + 1), j.val ≤ a.val → x a = 0) ∧ frameImage M *ᵥ x = y := by
  simp only [flagSpan, mem_colSpan_submatrix (castLE_injective j.is_le), range_castLE,
    Set.mem_ofPred_eq, not_lt]

omit [CMType E] in
/-- The vectors of `M A = ⟨M e_1, …, M e_ϱ⟩` are the combinations of the frame
`M e_1, …, M e_ϱ, M z_N` whose last coefficient vanishes. -/
lemma mem_isotropicSpan {M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E} :
    y ∈ isotropicSpan M ↔ ∃ x : Fin (𝔰.ϱ + 1) → E, x 𝔰.top = 0 ∧ frameImage M *ᵥ x = y := by
  have h_range (a : Fin (𝔰.ϱ + 1)) : a ∉ Set.range castSucc ↔ a = 𝔰.top := by
    rw [Set.mem_range, exists_castSucc_eq, not_ne_iff]
  simp only [isotropicSpan, mem_colSpan_submatrix (castSucc_injective 𝔰.ϱ), h_range, forall_eq]

/-- The span `flagSpan γ j` of the images under `γ` of the first `j` vectors of the frame
`e_1, …, e_ϱ, z_N` has rank `j`. -/
lemma finrank_flagSpan_coe (γ : S.G E) (j : Fin (𝔰.ϱ + 2)) :
    finrank E (flagSpan (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) j) = j := by
  let g : GL 𝔰.BesselIndex E := γ
  let e : Fin j → 𝔰.BesselIndex := 𝔰.besselFrame ∘ castLE j.is_le
  have he : Injective e := besselFrame_injective.comp (castLE_injective j.is_le)
  -- The rows of `γ⁻¹` at the indices `e` form a left inverse of the columns of `γ` at `e`.
  have h_left : g⁻¹.val.submatrix e id * g.val.submatrix id e = 1 := by
    rw [← submatrix_mul _ _ e id e bijective_id, g.inv_mul, submatrix_one e he]
  rw [flagSpan, submatrix_submatrix, id_comp,
    LinearMap.finrank_range_of_inj (HasLeftInv.injective_mulVec ⟨g⁻¹.val.submatrix e id, h_left⟩),
    finrank_fin_fun]

/-- A vector with the coefficients `x` in the frame `e_1, …, e_ϱ, z_N` and `x'` in its image under
`γ` lies in `I_γ = A ∩ γ A` if one of its coefficients at `z_N` and `γ z_N` vanishes, because the
two coefficients have the same norm. -/
lemma frameImage_mulVec_mem_commonIsotropic {x x' : Fin (𝔰.ϱ + 1) → E}
    (hxx' : frameImage 1 *ᵥ x = frameImage γ *ᵥ x') (h_top : x 𝔰.top = 0 ∨ x' 𝔰.top = 0) :
    frameImage 1 *ᵥ x ∈ commonIsotropic γ := by
  have h_norm : star (x 𝔰.top) * x 𝔰.top = star (x' 𝔰.top) * x' 𝔰.top :=
    star_mul_last_eq_of_frameImage_eq hxx'
  obtain ⟨hx, hx'⟩ : x 𝔰.top = 0 ∧ x' 𝔰.top = 0 := by
    obtain h | h := h_top <;> simp_all
  exact mem_commonIsotropic_iff.2
    ⟨mem_isotropicSpan.2 ⟨x, hx, rfl⟩, mem_isotropicSpan.2 ⟨x', hx', hxx'.symm⟩⟩

omit [CMType E] in
/-- Let `I` be a subspace of `M A = ⟨M e_1, …, M e_ϱ⟩` and let `j ≤ ϱ`. Suppose that `I` contains
vectors with any given coefficients in the frame `M e_1, …, M e_ϱ, M z_N` at the indices from `j`
on, the last coefficient being `0`. Then `M A = M A_{≤j} + I`, where `M A_{≤j}` is spanned by the
first `j` vectors of that frame. -/
lemma flagSpan_sup_eq_isotropicSpan {M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E}
    {j : Fin (𝔰.ϱ + 2)} {I : Submodule E (𝔰.BesselIndex → E)} (hj : j.val ≤ 𝔰.ϱ)
    (hI : I ≤ isotropicSpan M)
    (h_coeff : ∀ x : Fin (𝔰.ϱ + 1) → E, x 𝔰.top = 0 → ∃ x' : Fin (𝔰.ϱ + 1) → E,
      (∀ a : Fin (𝔰.ϱ + 1), j.val ≤ a.val → x' a = x a) ∧ frameImage M *ᵥ x' ∈ I) :
    flagSpan M j ⊔ I = isotropicSpan M := by
  refine le_antisymm (sup_le (fun w hw ↦ ?_) hI) fun w hw ↦ ?_
  · obtain ⟨x, hx, rfl⟩ := mem_flagSpan.1 hw
    exact mem_isotropicSpan.2 ⟨x, hx 𝔰.top hj, rfl⟩
  · obtain ⟨x, hx, rfl⟩ := mem_isotropicSpan.1 hw
    obtain ⟨x', hx', h_mem⟩ := h_coeff x hx
    rw [← sub_add_cancel x x', mulVec_add]
    exact Submodule.add_mem_sup
      (mem_flagSpan.2 ⟨x - x', fun a ha ↦ sub_eq_zero.2 (hx' a ha).symm, rfl⟩) h_mem

/-- Let a norm-one pair occur for `γ` from the index `j ≤ ϱ`: for one `ζ` with `ζ ζ̄ = 1`, the frame
`e_1, …, e_ϱ, z_N` and its image under `γ` share a vector with the leading coefficients `ζ` and `1`
at each index from `j` on. Then `γ A = γ A_{≤j} + I_γ`, where `A = ⟨e_1, …, e_ϱ⟩`,
`A_{≤j} = ⟨e_1, …, e_j⟩` and `I_γ = A ∩ γ A`. -/
lemma _root_.New.NormOnePairOccursFrom.flagSpan_coe_sup_commonIsotropic {j : Fin (𝔰.ϱ + 2)}
    (h_occurs : NormOnePairOccursFrom j.val γ) (hj : j.val ≤ 𝔰.ϱ) :
    flagSpan γ j ⊔ commonIsotropic γ = isotropicSpan γ := by
  refine flagSpan_sup_eq_isotropicSpan hj (commonIsotropic_le_isotropicSpan_coe γ) fun x hx ↦ ?_
  obtain ⟨w, x', hx', h_shared : frameImage 1 *ᵥ w = frameImage γ *ᵥ x'⟩ :=
    exists_frameImage_eq_of_normOnePairOccursFrom h_occurs x
  refine ⟨x', hx', ?_⟩
  rw [← h_shared]
  exact frameImage_mulVec_mem_commonIsotropic h_shared (.inr ((hx' 𝔰.top hj).trans hx))

/-- Let a norm-one pair occur for `γ` from the index `j ≤ ϱ`: for one `ζ` with `ζ ζ̄ = 1`, the frame
`e_1, …, e_ϱ, z_N` and its image under `γ` share a vector with the leading coefficients `ζ` and `1`
at each index from `j` on. Then `A = A_{≤j} + I_γ`, where `A = ⟨e_1, …, e_ϱ⟩`,
`A_{≤j} = ⟨e_1, …, e_j⟩` and `I_γ = A ∩ γ A`. -/
lemma _root_.New.NormOnePairOccursFrom.flagSpan_one_sup_commonIsotropic {j : Fin (𝔰.ϱ + 2)}
    (h_occurs : NormOnePairOccursFrom j.val γ) (hj : j.val ≤ 𝔰.ϱ) :
    flagSpan 1 j ⊔ commonIsotropic γ = isotropicSpan 1 := by
  refine flagSpan_sup_eq_isotropicSpan hj (commonIsotropic_le_isotropicSpan_one γ) fun x hx ↦ ?_
  -- Apply the norm-one pair that occurs for `γ⁻¹`, then move the shared vector by `γ`.
  obtain ⟨w, x', hx', h_inv : frameImage 1 *ᵥ w = frameImage (γ⁻¹ : S.G E) *ᵥ x'⟩ :=
    exists_frameImage_eq_of_normOnePairOccursFrom h_occurs.inv x
  have h_shared : frameImage 1 *ᵥ x' = frameImage γ *ᵥ w := by
    rw [frameImage_mulVec _ w, h_inv, frameImage_mulVec (γ⁻¹ : S.G E) x']
    simp [mulVec_mulVec]
  exact ⟨x', hx', frameImage_mulVec_mem_commonIsotropic h_shared (.inl ((hx' 𝔰.top hj).trans hx))⟩

omit [CMType E] in
/-- If a square matrix `Z` kills a nonzero vector `x` whose coefficients vanish from the index `j`
on, then the leading minor of order `j` of `Z` vanishes. -/
lemma leadingMinor_eq_zero_of_mulVec_eq_zero {j : Fin (𝔰.ϱ + 2)}
    {Z : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) E} {x : Fin (𝔰.ϱ + 1) → E} (hx_ne : x ≠ 0)
    (hZx : Z *ᵥ x = 0) (h_above : ∀ b : Fin (𝔰.ϱ + 1), j.val ≤ b.val → x b = 0) :
    leadingMinor Z j = 0 := by
  have h_padded : paddedLeading j Z *ᵥ x = 0 := by
    funext b
    have hb_row : (Z *ᵥ x) b = 0 := congrFun hZx b
    by_cases hb : b.val < j.val <;> simp_all [paddedLeading, mulVec, dotProduct]
  rw [← det_paddedLeading]
  exact exists_mulVec_eq_zero_iff.1 ⟨x, hx_ne, h_padded⟩

/-- Let `δ_i` be the leading minor of order `i` of the matrix `S.frameProducts γ` of the hermitian
products of the frame `e_1, …, e_ϱ, z_N` with its image under `γ`, and let
`gr(γ) = S.termDisc γ = |δ_n|² - N² |δ_{n-1}|²` vanish. Let `γ` have the cell rank `j`: a norm-one
pair occurs from the index `j` on, `δ_j ≠ 0`, and `j = n` exactly when `gr(γ) ≠ 0`. Then `j` is the
least index from which a norm-one pair occurs for `γ`, since a smaller index would give
`δ_j = 0`. -/
lemma HasCellRank.isLeast_normOnePairOccursFrom {j : Fin (𝔰.ϱ + 2)} (h_rank : S.HasCellRank j γ)
    (h_disc : S.termDisc γ = 0) : IsLeast {i : ℕ | NormOnePairOccursFrom i γ} j.val := by
  have hj_le : j.val ≤ 𝔰.ϱ := h_rank.le_of_termDisc_eq_zero h_disc
  obtain ⟨h_occurs, h_minor, -⟩ := h_rank
  refine ⟨h_occurs, ?_⟩
  rintro i ⟨ζ, -, h_pairs⟩
  by_contra! hij : i < j.val
  -- The vector shared at the index `i < j` gives a nonzero `x'` in the kernel of the products.
  let a : Fin (𝔰.ϱ + 1) := ⟨i, by lia⟩
  obtain ⟨x, x', hxx', -, hx', h_above⟩ : ∃ x x' : Fin (𝔰.ϱ + 1) → E,
      frameImage 1 *ᵥ x = frameImage γ *ᵥ x' ∧ x a = ζ ∧ x' a = 1 ∧
        ∀ b > a, x b = 0 ∧ x' b = 0 :=
      h_pairs a le_rfl
  have hx_top : x 𝔰.top = 0 := (h_above 𝔰.top (Fin.lt_def.2 (hij.trans_le hj_le))).1
  have h_products : S.frameProducts γ *ᵥ x' = 0 := by
    rw [frameProducts_mulVec_of_frameImage_eq hxx', hx_top, mul_zero, Pi.single_zero]
  have hx'_ne : x' ≠ 0 := fun h ↦ by simp [h] at hx'
  have hx'_above (b : Fin (𝔰.ϱ + 1)) (hb : j.val ≤ b.val) : x' b = 0 :=
    (h_above b (Fin.lt_def.2 (hij.trans_le hb))).right
  exact h_minor (leadingMinor_eq_zero_of_mulVec_eq_zero hx'_ne h_products hx'_above)

/-- Let `E` contain a primitive root of unity of order `5040`. Let `S.CharsAgree γ` hold: the
character `unipotentChar` takes the same value at `u` and at `γ⁻¹ u γ` for every rational `u` in
`U₀ ∩ γ U₀ γ⁻¹`. Let `j` be least with `NormOnePairOccursFrom j γ`: for one `ζ` with `ζ ζ̄ = 1`, at
every index from `j` on, the flags of the frame `e_1, …, e_ϱ, z_N` and of its image under `γ` share
a vector with leading coefficients `ζ` and `1`. Then `flagSpan 1 j`, the span of the first `j` frame
vectors, meets `colSpan (frameImage γ)`, the span of the image of the frame under `γ`, only in
`0`. -/
lemma CharsAgree.disjoint_flagSpan_one {j : Fin (𝔰.ϱ + 2)} [HasPrimitiveRoot5040 E]
    (h_agree : S.CharsAgree γ) (h_least : IsLeast {i : ℕ | NormOnePairOccursFrom i γ} j.val) :
    Disjoint (flagSpan 1 j)
      (colSpan (frameImage (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E))) := by
  refine Submodule.disjoint_def.2 fun w hw hw' ↦ ?_
  obtain ⟨x, hx, rfl⟩ := mem_flagSpan.1 hw
  obtain ⟨x', hx' : frameImage γ *ᵥ x' = frameImage 1 *ᵥ x⟩ := hw'
  by_contra h_ne
  have hx_ne : x ≠ 0 := fun h ↦ h_ne (by rw [h, mulVec_zero])
  obtain ⟨l, hl, hxl : x l ≠ 0, -⟩ := h_agree.exists_coords_ne_zero_of_common_vector h_least
    hx'.symm hx_ne
  exact hxl (hx l hl)

/-- Let `E` contain a primitive root of unity of order `5040`. Let `γ` satisfy `S.CharsAgree γ`: the
character `unipotentChar` takes the same value at `u` and at `γ⁻¹uγ` for every rational `u` in
`U₀ ∩ γU₀γ⁻¹`. Let `j` be least with `NormOnePairOccursFrom j γ`: for one `ζ` with `ζ ζ̄ = 1`, at
every index from `j` on, the flags of the frame `e_1, …, e_ϱ, z_N` and of its image under `γ` share
a vector with leading coefficients `ζ` and `1`. Then `flagSpan γ j`, the span of the images under
`γ` of the first `j` frame vectors, meets the span `colSpan (frameImage 1)` of the frame only in
`0`. -/
lemma CharsAgree.disjoint_flagSpan_coe {j : Fin (𝔰.ϱ + 2)} [HasPrimitiveRoot5040 E]
    (h_agree : S.CharsAgree γ) (h_least : IsLeast {i : ℕ | NormOnePairOccursFrom i γ} j.val) :
    Disjoint (flagSpan (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) j) (colSpan (frameImage 1)) := by
  refine Submodule.disjoint_def.2 fun w hw hw' ↦ ?_
  obtain ⟨x', hx', rfl⟩ := mem_flagSpan.1 hw
  obtain ⟨x, hx : frameImage 1 *ᵥ x = frameImage γ *ᵥ x'⟩ := hw'
  by_contra h_ne
  have hx_ne : x ≠ 0 := fun h ↦ h_ne (by rw [← hx, h, mulVec_zero])
  obtain ⟨l, hl, -, hx'l : x' l ≠ 0⟩ := h_agree.exists_coords_ne_zero_of_common_vector h_least hx
    hx_ne
  exact hx'l (hx' l hl)

/-- Let `gr(γ) = S.termDisc γ` vanish and let `γ` have the cell rank `j`. Then `A = A_{≤j} + I_γ`,
where `A = ⟨e_1, …, e_ϱ⟩`, `A_{≤j} = ⟨e_1, …, e_j⟩` and `I_γ = A ∩ γ A`. -/
theorem HasCellRank.flagSpan_one_sup_commonIsotropic {j : Fin (𝔰.ϱ + 2)}
    (h_rank : S.HasCellRank j γ) (h_disc : S.termDisc γ = 0) :
    flagSpan 1 j ⊔ commonIsotropic γ = isotropicSpan 1 :=
  h_rank.normOnePairOccursFrom.flagSpan_one_sup_commonIsotropic
    (h_rank.le_of_termDisc_eq_zero h_disc)

/-- Let `gr(γ) = S.termDisc γ` vanish and let `γ` have the cell rank `j`. Then
`γ A = γ A_{≤j} + I_γ`, where `A = ⟨e_1, …, e_ϱ⟩`, `A_{≤j} = ⟨e_1, …, e_j⟩` and `I_γ = A ∩ γ A`. -/
theorem HasCellRank.flagSpan_coe_sup_commonIsotropic {j : Fin (𝔰.ϱ + 2)}
    (h_rank : S.HasCellRank j γ) (h_disc : S.termDisc γ = 0) :
    flagSpan γ j ⊔ commonIsotropic γ = isotropicSpan γ :=
  h_rank.normOnePairOccursFrom.flagSpan_coe_sup_commonIsotropic
    (h_rank.le_of_termDisc_eq_zero h_disc)

/-- Let `E` contain a primitive root of unity of order `5040`, let `γ` agree, let
`gr(γ) = S.termDisc γ` vanish and let `γ` have the cell rank `j`. Then `A_{≤j} = ⟨e_1, …, e_j⟩`
meets `I_γ = A ∩ γ A` only in `0`. -/
theorem CharsAgree.disjoint_flagSpan_one_commonIsotropic {j : Fin (𝔰.ϱ + 2)}
    [HasPrimitiveRoot5040 E] (h_agree : S.CharsAgree γ) (h_disc : S.termDisc γ = 0)
    (h_rank : S.HasCellRank j γ) : Disjoint (flagSpan 1 j) (commonIsotropic γ) :=
  (h_agree.disjoint_flagSpan_one (h_rank.isLeast_normOnePairOccursFrom h_disc)).mono_right
    (commonIsotropic_le_colSpan_frameImage_coe γ)

/-- Let `E` contain a primitive root of unity of order `5040`, let `γ` agree, let
`gr(γ) = S.termDisc γ` vanish and let `γ` have the cell rank `j`. Then
`γ A_{≤j} = ⟨γ e_1, …, γ e_j⟩` meets `I_γ = A ∩ γ A` only in `0`. -/
theorem CharsAgree.disjoint_flagSpan_coe_commonIsotropic {j : Fin (𝔰.ϱ + 2)}
    [HasPrimitiveRoot5040 E] (h_agree : S.CharsAgree γ) (h_disc : S.termDisc γ = 0)
    (h_rank : S.HasCellRank j γ) : Disjoint (flagSpan γ j) (commonIsotropic γ) :=
  (h_agree.disjoint_flagSpan_coe (h_rank.isLeast_normOnePairOccursFrom h_disc)).mono_right
    (commonIsotropic_le_colSpan_frameImage_one γ)

/-- Let `E` contain a primitive root of unity of order `5040`. Let `S.CharsAgree γ` hold:
`unipotentChar` takes the same value at `u` and at `γ⁻¹uγ` for every rational `u` in `U₀ ∩ γU₀γ⁻¹`.
Let `S.termDisc γ = |δ_{ϱ+1}|² - N² |δ_ϱ|²` vanish. Let `γ` have the cell rank `j`:
`NormOnePairOccursFrom j γ` holds, `δ_j ≠ 0`, and `j = ϱ + 1` exactly when `S.termDisc γ ≠ 0`. Then
`j + finrank E (commonIsotropic γ) = ϱ`. -/
theorem CharsAgree.add_finrank_commonIsotropic_eq {j : Fin (𝔰.ϱ + 2)} [HasPrimitiveRoot5040 E]
    (h_agree : S.CharsAgree γ) (h_disc : S.termDisc γ = 0) (h_rank : S.HasCellRank j γ) :
    j.val + finrank E (commonIsotropic γ) = 𝔰.ϱ := by
  have h_sup : flagSpan γ j ⊔ commonIsotropic γ = isotropicSpan γ :=
    h_rank.flagSpan_coe_sup_commonIsotropic h_disc
  have h_inf : flagSpan γ j ⊓ commonIsotropic γ = ⊥ :=
    (h_agree.disjoint_flagSpan_coe_commonIsotropic h_disc h_rank).eq_bot
  rw [← finrank_flagSpan_coe γ j, ← Submodule.finrank_sup_add_finrank_inf_eq, h_sup, h_inf,
    finrank_bot, add_zero, finrank_isotropicSpan_coe]

/-- Let `E` contain a primitive root of unity of order `5040`, let `γ` agree, let
`gr(γ) = S.termDisc γ` vanish, and let `j + rk I_γ = ϱ` for `I_γ = A ∩ γ A` and `A = ⟨e_1, …, e_ϱ⟩`.
Then `γ` has the cell rank `j`: a norm-one pair occurs for it from the index `j` on, and the leading
minor `δ_j` of the products of the frame with its image is not zero. -/
theorem CharsAgree.hasCellRank_of_add_finrank_eq {j : Fin (𝔰.ϱ + 2)} [HasPrimitiveRoot5040 E]
    (h_agree : S.CharsAgree γ) (h_disc : S.termDisc γ = 0)
    (hj : j.val + finrank E (commonIsotropic γ) = 𝔰.ϱ) : S.HasCellRank j γ := by
  obtain ⟨i, h_rank⟩ := h_agree.exists_hasCellRank h_disc
  have hi : i.val + finrank E (commonIsotropic γ) = 𝔰.ϱ :=
    h_agree.add_finrank_commonIsotropic_eq h_disc h_rank
  rwa [show j = i by omega]

/-! ### The action of the unipotent group -/

/-- An element `u` of the unipotent group `U₀` maps `A = ⟨e_1, …, e_ϱ⟩` into itself. -/
lemma mulVec_mem_isotropicSpan_one {u : S.G E} (hu : u ∈ besselU) (hy : y ∈ isotropicSpan 1) :
    (u : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) *ᵥ y ∈ isotropicSpan 1 := by
  rw [mem_isotropicSpan_one] at hy ⊢
  refine fun i ↦ Finset.sum_eq_zero ?_
  rintro (a | b) - <;> simp [apply_inr_of_mem_besselU hu, hy]

/-- An element `u` of the unipotent group `U₀` preserves `A = ⟨e_1, …, e_ϱ⟩`: the vector `u y` lies
in `A` if and only if `y` does. -/
lemma mulVec_mem_isotropicSpan_one_iff {u : S.G E} (hu : u ∈ besselU) :
    (u : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) *ᵥ y ∈ isotropicSpan 1 ↔ y ∈ isotropicSpan 1 :=
  ⟨fun h ↦ by simpa using mulVec_mem_isotropicSpan_one (inv_mem hu) h,
    mulVec_mem_isotropicSpan_one hu⟩

/-- For `u`, `u'` in the Bessel unipotent group `besselU` we have `I_{u γ u'} = u I_γ`, where
`I_γ = commonIsotropic γ = A ∩ γ A` and `A = ⟨e_1, …, e_ϱ⟩`. -/
theorem commonIsotropic_besselU_mul {u u' : S.G E} (hu : u ∈ besselU) (hu' : u' ∈ besselU) :
    commonIsotropic (u * γ * u') =
      (commonIsotropic γ).map (u : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E).mulVecLin := by
  let mat (g : S.G E) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E := g
  ext y
  have h_inv : mat (u * γ * u')⁻¹ *ᵥ y = mat u'⁻¹ *ᵥ mat γ⁻¹ *ᵥ mat u⁻¹ *ᵥ y := by
    simp [mat]
  have h_mem : y ∈ commonIsotropic (u * γ * u') ↔ mat u⁻¹ *ᵥ y ∈ commonIsotropic γ := by
    rw [mem_commonIsotropic_iff, mem_commonIsotropic_iff, mem_isotropicSpan_coe,
      mem_isotropicSpan_coe, h_inv, mulVec_mem_isotropicSpan_one_iff (inv_mem hu),
      mulVec_mem_isotropicSpan_one_iff (inv_mem hu')]
  refine h_mem.trans ⟨fun h ↦ ⟨_, h, by simp [mat]⟩, ?_⟩
  rintro ⟨t, ht, rfl⟩
  simpa [mat] using ht

/-- The rank of `I_γ = A ∩ γ A`, where `A = ⟨e_1, …, e_ϱ⟩`, does not change when `γ` is multiplied
on either side by elements of the unipotent group `U₀`. -/
theorem finrank_commonIsotropic_besselU_mul {u u' : S.G E} (hu : u ∈ besselU) (hu' : u' ∈ besselU) :
    finrank E (commonIsotropic (u * γ * u')) = finrank E (commonIsotropic γ) := by
  rw [commonIsotropic_besselU_mul hu hu']
  exact (Submodule.equivMapOfInjective _
    (mulVec_injective_of_isUnit (u : GL 𝔰.BesselIndex E).isUnit) _).finrank_eq.symm

/-- The function `ψ_U = S.unipotentChar` on the finite adelic group is multiplicative on the images
under `S.ratToFin` of the rational points of the unipotent group `U₀ = besselU`. -/
lemma unipotentChar_ratToFin_mul {u u' : S.G E} (hu : u ∈ besselU) (hu' : u' ∈ besselU) :
    S.unipotentChar (S.ratToFin (u * u')) =
      S.unipotentChar (S.ratToFin u) * S.unipotentChar (S.ratToFin u') := by
  have h_sum : simpleRootSum (S.ratToFin u * S.ratToFin u') =
      simpleRootSum (S.ratToFin u) + simpleRootSum (S.ratToFin u') :=
    simpleRootSum_mul (mem_partialUnitriangularGroup_of_mem_besselU (ratToFin_mem_besselU_iff.2 hu))
      (mem_partialUnitriangularGroup_of_mem_besselU (ratToFin_mem_besselU_iff.2 hu'))
  rw [map_mul, unipotentChar, h_sum, mul_add, AddChar.map_add_eq_mul, unipotentChar,
    unipotentChar]

/-- The function `ψ_U = S.unipotentChar` is invariant under conjugation in the rational points of
the unipotent group `U₀`. -/
lemma unipotentChar_ratToFin_conj {u u' : S.G E} (hu : u ∈ besselU) (hu' : u' ∈ besselU) :
    S.unipotentChar (S.ratToFin (u⁻¹ * u' * u)) = S.unipotentChar (S.ratToFin u') := by
  have h_ne : S.unipotentChar (S.ratToFin u) ≠ 0 := (S.selfDualChar.val_isUnit _).ne_zero
  apply mul_left_cancel₀ h_ne
  rw [← unipotentChar_ratToFin_mul hu (mul_mem (mul_mem (inv_mem hu) hu') hu), mul_assoc,
    mul_inv_cancel_left, unipotentChar_ratToFin_mul hu' hu, mul_comm]

/-- For `u`, `u'` in `besselU`, the element `u γ u'` agrees if and only if `γ` does. -/
theorem charsAgree_mul_mul_iff_of_mem_besselU {u u' : S.G E} (hu : u ∈ besselU)
    (hu' : u' ∈ besselU) :
    S.CharsAgree (u * γ * u') ↔ S.CharsAgree γ := by
  have h_map {a a' δ : S.G E} (ha : a ∈ besselU) (ha' : a' ∈ besselU) (hδ : S.CharsAgree δ) :
      S.CharsAgree (a * δ * a'⁻¹) := by
    intro w hw w' hw' h_comm
    have h_conj : a⁻¹ * w * a * δ = δ * (a'⁻¹ * w' * a') :=
      calc a⁻¹ * w * a * δ = a⁻¹ * (w * (a * δ * a'⁻¹)) * a' := by group
        _ = a⁻¹ * (a * δ * a'⁻¹ * w') * a' := by rw [h_comm]
        _ = δ * (a'⁻¹ * w' * a') := by group
    rw [← unipotentChar_ratToFin_conj ha hw, ← unipotentChar_ratToFin_conj ha' hw']
    exact hδ _ (mul_mem (mul_mem (inv_mem ha) hw) ha) _ (mul_mem (mul_mem (inv_mem ha') hw') ha')
      h_conj
  exact ⟨fun h ↦ by simpa [mul_assoc] using h_map (inv_mem hu) hu' h,
    fun h ↦ by simpa using h_map hu (inv_mem hu') h⟩

/-! ### The terms that remain -/

/-- For `A = ⟨e_1, …, e_ϱ⟩` we have `A = γ A` if and only if `I_γ = A ∩ γ A` has the rank `ϱ`. -/
lemma isotropicSpan_eq_iff_finrank :
    isotropicSpan 1 = isotropicSpan (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) ↔
      finrank E (commonIsotropic γ) = 𝔰.ϱ := by
  have h_one : finrank E (isotropicSpan (𝔰 := 𝔰) (E := E) 1) = 𝔰.ϱ :=
    finrank_isotropicSpan_coe (1 : S.G E)
  refine ⟨fun h ↦ by rw [commonIsotropic, ← h, inf_idem, h_one], fun h ↦ ?_⟩
  have h_eq_one : commonIsotropic γ = isotropicSpan 1 :=
    Submodule.eq_of_le_of_finrank_eq (commonIsotropic_le_isotropicSpan_one γ) (h.trans h_one.symm)
  have h_eq_coe : commonIsotropic γ = isotropicSpan γ :=
    Submodule.eq_of_le_of_finrank_eq (commonIsotropic_le_isotropicSpan_coe γ)
      (h.trans (finrank_isotropicSpan_coe γ).symm)
  exact h_eq_one.symm.trans h_eq_coe

variable (S) in
/-- The set `Γ*` of the rational elements `γ` that have `gr(γ) = S.termDisc γ ≠ 0`, or agree and
have `gr(γ) = 0` and `A ≠ γ A`, where `A = ⟨e_1, …, e_ϱ⟩`. -/
def remainingTerms : Set (S.G E) :=
  {γ : S.G E | S.termDisc γ ≠ 0 ∨
    S.CharsAgree γ ∧ S.termDisc γ = 0 ∧ isotropicSpan 1 ≠ isotropicSpan γ.val.val}

/-- `γ` lies in `Γ*` (`S.remainingTerms`) exactly when `S.termDisc γ ≠ 0`, or `S.CharsAgree γ`,
`S.termDisc γ = 0` and `isotropicSpan 1 ≠ isotropicSpan γ`. -/
lemma mem_remainingTerms_iff :
    γ ∈ S.remainingTerms ↔ S.termDisc γ ≠ 0 ∨ S.CharsAgree γ ∧ S.termDisc γ = 0 ∧
      isotropicSpan 1 ≠ isotropicSpan (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) :=
  Iff.rfl

/-- The set `Γ*` of the remaining terms is stable under the unipotent group on both sides: for `u`,
`u'` in `U₀`, the element `u⁻¹ γ u'` lies in `Γ*` if and only if `γ` does. -/
lemma isStable_remainingTerms : S.IsStable S.remainingTerms := by
  intro u hu u' hu' γ
  simp only [mem_remainingTerms_iff, Ne, isotropicSpan_eq_iff_finrank,
    frameDisc_frameGram_inv_mul_mul_of_mem_besselU hu hu',
      charsAgree_mul_mul_iff_of_mem_besselU (inv_mem hu) hu',
    finrank_commonIsotropic_besselU_mul (inv_mem hu) hu']

omit [CMType E] in
lemma flagSpan_zero (M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) : flagSpan M 0 = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun y hy ↦ ?_
  obtain ⟨x, hx, rfl⟩ := mem_flagSpan.1 hy
  rw [show x = 0 from funext fun a ↦ hx a (Nat.zero_le a), mulVec_zero]

/-- Let `Γ*` = `S.remainingTerms` be the set of rational `γ` with `S.termDisc γ ≠ 0`, or with
`S.CharsAgree γ`, `S.termDisc γ = 0` and `A ≠ γ A`, where `A = ⟨e_1, …, e_ϱ⟩`. Here
`S.termDisc γ = |δ_{ϱ+1}|² - N²|δ_ϱ|²`, where the `δ_i` are the leading minors of the matrix of
hermitian products of the vectors `e_1, …, e_ϱ, z_N` with their images under `γ`; `z_N` is a vector
of norm `-N`. Suppose `NormOnePairOccursFrom 0 γ` holds: for one `ζ` with `ζ ζ̄ = 1`, the flags
spanned by these vectors and by their images share, at every index, a vector with leading
coefficients `ζ` and `1`. Then `γ ∉ Γ*`. A shared vector gives `S.termDisc γ = 0`, and `A = γ A`,
since both equal `I_γ = A ∩ γ A`. -/
lemma _root_.New.NormOnePairOccursFrom.notMem_remainingTerms
    (h_occurs : NormOnePairOccursFrom 0 γ) :
    γ ∉ S.remainingTerms := by
  rw [mem_remainingTerms_iff]
  rintro (h_disc | ⟨-, -, h_ne⟩)
  · obtain ⟨ζ, -, h_pairs⟩ := h_occurs
    obtain ⟨x, x', hxx' : frameImage 1 *ᵥ x = frameImage γ *ᵥ x', -, hx' : x' 0 = 1, -⟩ :=
      h_pairs 0 le_rfl
    have hx'_ne : x' ≠ 0 := fun h ↦ by simp [h] at hx'
    exact h_disc (termDisc_eq_zero_iff_exists.2 ⟨x, x', hx'_ne, hxx'⟩)
  · have h_one : flagSpan 1 0 ⊔ commonIsotropic γ = isotropicSpan 1 :=
      NormOnePairOccursFrom.flagSpan_one_sup_commonIsotropic (j := 0) h_occurs 𝔰.ϱ.zero_le
    have h_coe : flagSpan γ 0 ⊔ commonIsotropic γ = isotropicSpan γ :=
      NormOnePairOccursFrom.flagSpan_coe_sup_commonIsotropic (j := 0) h_occurs 𝔰.ϱ.zero_le
    rw [flagSpan_zero, bot_sup_eq] at h_one h_coe
    exact h_ne (h_one.symm.trans h_coe)

/-- Let `E` contain a primitive root of unity of order `5040`. If `γ` agrees and is not in the set
`Γ*` of the remaining terms, then a norm-one pair occurs for `γ` from the index `0` on: for one `ζ`
with `ζ ζ̄ = 1`, the frame and its image under `γ` share a vector with the leading coefficients `ζ`
and `1` at every index. -/
lemma CharsAgree.normOnePairOccursFrom_zero [HasPrimitiveRoot5040 E] (h_agree : S.CharsAgree γ)
    (hγ : γ ∉ S.remainingTerms) : NormOnePairOccursFrom 0 γ := by
  have h_disc : S.termDisc γ = 0 := by_contra fun h ↦ hγ (.inl h)
  have h_span : isotropicSpan 1 = isotropicSpan (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) :=
    by_contra fun h ↦ hγ (.inr ⟨h_agree, h_disc, h⟩)
  exact (h_agree.hasCellRank_of_add_finrank_eq (j := 0) h_disc
    (by simpa using isotropicSpan_eq_iff_finrank.1 h_span)).normOnePairOccursFrom

end Filling

end New

end
