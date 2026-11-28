import New.Spanning.Unfolding.TermStructure

/-!
# Denominators: bases of `A⁺ / I_γ` and `γ A⁺ / I_γ`

Let `γ` be a rational point of the unitary group that has the cell rank `j`. This file gives bases
of `A⁺ / I_γ` and `γ A⁺ / I_γ`: the first `j` vectors of the frame with `z_N`, and their images
under `γ`. The basis of `γ A⁺ / I_γ` is proved from the cell rank alone; the basis of `A⁺ / I_γ` is
proved when `E` contains a primitive `5040`-th root of unity (`HasPrimitiveRoot5040 E`). Under the
same hypothesis the determinant `New.Filling.subframeMinor` of the products of the two lists is not
zero (`New.Filling.HasCellRank.subframeMinor_ne_zero`); so the two quotients pair perfectly.

Here `n = ϱ + 1` and `N = S.N` is the prime of the data `S`. The basis vectors `e_1, …, e_{n-1}`
span the isotropic space `A`, the basis vector `z_N` has the product `-N` with itself, and
`A⁺ = A + E z_N` is the span of the frame `e_• = (e_1, …, e_{n-1}, z_N)`, which the code indexes
from `0`. The rank of `A / I_γ` is `min j (n - 1)`.

* `New.Filling.HasCellRank.linearIndependent_mkQ_frameImage_one_and_sup_eq`,
  `New.Filling.HasCellRank.linearIndependent_mkQ_frameImage_coe_and_sup_eq`: the two bases modulo
  `I_γ`; `New.Filling.HasCellRank.linearIndependent_mkQ_frameImage_and_sup_eq` states both.

Notions from other files:
* `frameImage M` is the matrix whose columns are the frame `M e_•`, and `colSpan` is the span of the
  columns, so `A⁺ = colSpan (frameImage 1)`.
* `commonIsotropic γ` is the space `I_γ = A ∩ γ A`.
* `subframeIndices j` is the set of indices of the first `j` vectors of `e_•` and of `z_N`.
* `S.frameProducts γ` is the matrix of the hermitian products (Gram matrix `S.ratGram`) of `e_•`
  with `γ e_•`, and `δ_j` is its leading minor of order `j`.
* `S.HasCellRank j γ` says: for one `ζ` with `ζ ζ̄ = 1` and every index `l ≥ j`, the flags of `e_•`
  and `γ e_•` share a vector with leading coefficients `ζ` and `1` at `l`; `δ_j ≠ 0`; and `j = n`
  exactly when `𝗀 = S.termDisc γ = |δ_n|² - N² |δ_{n-1}|²` is nonzero.
-/

noncomputable section

open Matrix Fin Function

namespace New

/-- A combination of the columns of `F` whose coefficients vanish outside `s` is a combination of
the columns with indices in `s`. -/
lemma mulVec_eq_submatrix_mulVec_of_eq_zero_off {K m n : Type*} [Semiring K] [Fintype n]
    (F : Matrix m n K) {s : Finset n} {y : n → K} (hy : ∀ a : n, a ∉ s → y a = 0) :
    F *ᵥ y = F.submatrix id ((↑) : s → n) *ᵥ fun a : s ↦ y a := by
  funext i
  change ∑ a : n, F i a * y a = ∑ a : s, F i a * y a
  rw [s.sum_coe_sort fun a ↦ F i a * y a]
  exact (Finset.sum_subset s.subset_univ fun a _ ha ↦ by rw [hy a ha, mul_zero]).symm

/-- Let `I` lie in the column space of `F`. Suppose that no nonzero combination of the columns with
indices in `s` lies in `I`, and that any coefficients outside `s` occur in a combination of all
columns that lies in `I`. Then the columns with indices in `s` are a basis of the column space
modulo `I`. -/
lemma linearIndependent_mkQ_col_and_colSpan_sup_eq {K m n : Type*} [Field K] [Fintype n]
    [DecidableEq n] {F : Matrix m n K} {I : Submodule K (m → K)} {s : Finset n}
    (h_le : I ≤ colSpan F) (h_zero : ∀ y : n → K, (∀ a : n, a ∉ s → y a = 0) → F *ᵥ y ∈ I → y = 0)
    (h_free : ∀ y : n → K, ∃ y' : n → K, (∀ a : n, a ∉ s → y' a = y a) ∧ F *ᵥ y' ∈ I) :
    LinearIndependent K (fun a : s ↦ I.mkQ (F.col a)) ∧
    colSpan (F.submatrix id ((↑) : s → n)) ⊔ I = colSpan F := by
  refine ⟨Fintype.linearIndependent_iff.2 fun c hc a ↦ ?_, le_antisymm (sup_le ?_ h_le) ?_⟩
  · let y : n → K := fun a ↦ if ha : a ∈ s then c ⟨a, ha⟩ else 0
    have hy (a : n) (ha : a ∉ s) : y a = 0 := dite_eq_right ha
    have h_sum : F *ᵥ y = ∑ a : s, c a • F.col a := by
      rw [mulVec_eq_submatrix_mulVec_of_eq_zero_off F hy]
      funext i
      simp [mulVec, dotProduct, mul_comm, y]
    have h_mem : F *ᵥ y ∈ I := by
      rw [h_sum, ← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sum]
      simpa only [map_smul] using hc
    simpa [y] using congrFun (h_zero y hy h_mem) a
  · rw [colSpan, colSpan, range_mulVecLin, range_mulVecLin]
    exact Submodule.span_mono (Set.range_subset_iff.2 fun a ↦ ⟨a, rfl⟩)
  · rintro _ ⟨y, rfl⟩
    obtain ⟨y', hy', h_mem⟩ := h_free y
    have h_split : F *ᵥ y = F.submatrix id (↑) *ᵥ (fun a : s ↦ (y - y') a) + F *ᵥ y' := by
      rw [← mulVec_eq_submatrix_mulVec_of_eq_zero_off F fun a ha ↦ by simp [hy' a ha], mulVec_sub,
        sub_add_cancel]
    rw [mulVecLin_apply, h_split]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) h_mem

namespace Filling

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰} {j : Fin (𝔰.ϱ + 2)}
  {γ : S.G E}

/-- Let `γ` have the cell rank `j`: at every index `l ≥ j` (counted from `0`) the flags of the frame
`e_• = (e_1, …, e_ϱ, z_N)` and of `γ e_•` share a vector with leading coefficients `ζ` and `1` (one
`ζ` with `ζ ζ̄ = 1`), the leading minor of order `j` of the matrix `S.frameProducts γ` of their
products is nonzero, and `j = ϱ + 1` exactly when `S.termDisc γ ≠ 0`. Then a vector with
coefficients `x` in `e_•` (the columns of `frameImage 1`) and `y` in `γ e_•` is orthogonal to the
first `j` vectors of `e_•`; its products with `e_•` are the entries of `S.frameProducts γ *ᵥ y`. -/
lemma HasCellRank.frameProducts_mulVec_eq_zero_of_shared (hγ : S.HasCellRank j γ)
    {x y : Fin (𝔰.ϱ + 1) → E} (hxy : frameImage 1 *ᵥ x = frameImage γ *ᵥ y)
    (a : Fin (𝔰.ϱ + 1)) (ha : a.val < j.val) : (S.frameProducts γ *ᵥ y) a = 0 := by
  by_cases hj : 𝔰.ϱ < j.val
  · obtain rfl : y = 0 := frameImage_mulVec_eq_zero_iff.1 <| Submodule.disjoint_def.1
      (disjoint_colSpan_frameImage (hγ.lt_iff_termDisc_ne_zero.1 hj)) _ ⟨x, hxy⟩ ⟨y, rfl⟩
    simp
  · rw [frameProducts_mulVec_of_frameImage_eq hxy,
      Pi.single_eq_of_ne (Fin.ne_of_val_ne (show a.val ≠ 𝔰.ϱ by lia))]

/-- Let `γ` have the cell rank `j`: at every index `l ≥ j` (counted from `0`) the flags of the frame
`e_• = (e_1, …, e_ϱ, z_N)` and of `γ e_•` share a vector with leading coefficients `ζ` and `1` (one
`ζ` with `ζ ζ̄ = 1`), the leading minor of order `j` of the matrix `S.frameProducts γ` is nonzero,
and `j = ϱ + 1` exactly when `S.termDisc γ ≠ 0`. The entries of `S.frameProducts γ` are the products
of `e_•` (rows) with `γ e_•` (columns) in the hermitian form with Gram matrix `S.ratGram`. Let `y`
vanish at every index `≥ j`, and let the combination of `γ e_•` with coefficients `y` be orthogonal
to the first `j` vectors of `e_•`. Then `y = 0`. -/
lemma HasCellRank.eq_zero_of_frameProducts_mulVec_eq_zero (hγ : S.HasCellRank j γ)
    {y : Fin (𝔰.ϱ + 1) → E} (h_above : ∀ a : Fin (𝔰.ϱ + 1), j.val ≤ a.val → y a = 0)
    (h_below : ∀ a : Fin (𝔰.ϱ + 1), a.val < j.val → (S.frameProducts γ *ᵥ y) a = 0) : y = 0 := by
  refine eq_zero_of_mulVec_eq_zero (M := paddedLeading j (S.frameProducts γ))
    (by simpa only [det_paddedLeading] using hγ.leadingMinor_ne_zero) (funext fun a ↦ ?_)
  by_cases ha : a.val < j.val
  · simpa [paddedLeading, mulVec, dotProduct, ha] using h_below a ha
  · simpa [paddedLeading, mulVec, dotProduct, ha] using h_above a (not_lt.1 ha)

/-! ### The subframe of the first `j` vectors and `z_N` -/

/-- Let `γ` have the cell rank `j`: at every index `l ≥ j` (counted from `0`) the flags of the frame
`e_• = (e_1, …, e_ϱ, z_N)` and of `γ e_•` share a vector with leading coefficients `ζ` and `1` (one
`ζ` with `ζ ζ̄ = 1`), the leading minor of order `j` of the matrix `S.frameProducts γ` of their
products is nonzero, and `j = ϱ + 1` exactly when `S.termDisc γ ≠ 0`. Then no nonzero combination of
the first `j` vectors of `γ e_•` (the columns of `frameImage γ`) and its last vector `γ z_N`, whose
indices form `subframeIndices j`, lies in `commonIsotropic γ = A ∩ γ A`, where
`A = ⟨e_1, …, e_ϱ⟩`. -/
lemma HasCellRank.eq_zero_of_mem_commonIsotropic (hγ : S.HasCellRank j γ)
    {x' : Fin (𝔰.ϱ + 1) → E} (h_off : ∀ a : Fin (𝔰.ϱ + 1), a ∉ subframeIndices j → x' a = 0)
    (h_mem : frameImage γ *ᵥ x' ∈ commonIsotropic γ) : x' = 0 := by
  obtain ⟨x, hxx'⟩ : ∃ x : Fin (𝔰.ϱ + 1) → E, frameImage 1 *ᵥ x = frameImage γ *ᵥ x' :=
    commonIsotropic_le_colSpan_frameImage_one γ h_mem
  obtain ⟨t, ht_top, ht⟩ : ∃ t : Fin (𝔰.ϱ + 1) → E,
      t 𝔰.top = 0 ∧ frameImage γ *ᵥ t = frameImage γ *ᵥ x' :=
    mem_isotropicSpan.1 (commonIsotropic_le_isotropicSpan_coe γ h_mem)
  obtain rfl : t = x' := by
    rwa [← sub_eq_zero, ← mulVec_sub, frameImage_mulVec_eq_zero_iff, sub_eq_zero] at ht
  refine hγ.eq_zero_of_frameProducts_mulVec_eq_zero (fun a ha ↦ ?_)
    (hγ.frameProducts_mulVec_eq_zero_of_shared hxx')
  obtain rfl | h_ne := eq_or_ne a 𝔰.top
  exacts [ht_top, h_off a (by simp [ha, h_ne])]

/-- Let `γ` have the cell rank `j`: at every index `l ≥ j` (counted from `0`) the flags of the frame
`e_• = (e_1, …, e_ϱ, z_N)` and of `γ e_•` share a vector with leading coefficients `ζ` and `1` (one
`ζ` with `ζ ζ̄ = 1`), the leading minor of order `j` of the matrix `S.frameProducts γ` of their
products is nonzero, and `j = ϱ + 1` exactly when `S.termDisc γ ≠ 0`. Here `S.termDisc γ` is
`|δ_{ϱ+1}|² - N² |δ_ϱ|²`, where `δ_i` is the leading minor of order `i` of `S.frameProducts γ` and
`N = S.N`. Put `A = ⟨e_1, …, e_ϱ⟩`, `A_{≤j} = ⟨e_1, …, e_j⟩` and
`I_γ = commonIsotropic γ = A ∩ γ A`. Let `M` be a square matrix of the size of `γ` such that, if
`S.termDisc γ` vanishes, `M A = M A_{≤j} + I_γ`; both `1` and `γ` are such. Then any coefficients
`x a` at the indices `j ≤ a < ϱ` (those outside `subframeIndices j`) occur in a combination of the
frame `M e_•` (the columns of `frameImage M`) that lies in `I_γ`. -/
lemma HasCellRank.exists_mem_commonIsotropic (hγ : S.HasCellRank j γ)
    {M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E}
    (h_sum : S.termDisc γ = 0 → flagSpan M j ⊔ commonIsotropic γ = isotropicSpan M)
    (x : Fin (𝔰.ϱ + 1) → E) :
    ∃ t : Fin (𝔰.ϱ + 1) → E,
      (∀ a : Fin (𝔰.ϱ + 1), a ∉ subframeIndices j → t a = x a) ∧
      frameImage M *ᵥ t ∈ commonIsotropic γ := by
  by_cases hj : 𝔰.ϱ < j.val
  · exact ⟨0, fun a ha ↦ absurd (by simp [a.is_le.trans_lt hj]) ha, by simp⟩
  -- Split the part of `x` in `M A` along `M A = M A_{≤j} + I_γ`.
  have h_disc : S.termDisc γ = 0 := by simpa [hγ.lt_iff_termDisc_ne_zero] using hj
  obtain ⟨w, hw, y, hy, h_split⟩ : ∃ w ∈ flagSpan M j, ∃ y ∈ commonIsotropic γ,
      w + y = frameImage M *ᵥ update x 𝔰.top 0 :=
    Submodule.mem_sup.1 ((h_sum h_disc).ge (mem_isotropicSpan.2 ⟨_, update_self .., rfl⟩))
  obtain ⟨x', h_above, rfl⟩ := mem_flagSpan.1 hw
  refine ⟨update x 𝔰.top 0 - x', fun a ha ↦ ?_, ?_⟩
  · obtain ⟨h_le, h_ne⟩ : j.val ≤ a.val ∧ a ≠ 𝔰.top := by simpa using ha
    simp [h_above a h_le, h_ne]
  · rwa [mulVec_sub, ← h_split, add_sub_cancel_left]

/-- Let `e_• = (e_1, …, e_ϱ, z_N)` be the frame, let `A = ⟨e_1, …, e_ϱ⟩`, write
`I_γ = commonIsotropic γ = A ∩ γ A`, and recall that `frameImage M` is the matrix with columns
`M e_•`. The combination of `e_•` with coefficients `x` lies in `I_γ` exactly when the combination
of `γ⁻¹ e_•` with the same coefficients lies in `I_{γ⁻¹}`, as `γ⁻¹` carries the one to the
other. -/
lemma frameImage_one_mulVec_mem_commonIsotropic_iff (x : Fin (𝔰.ϱ + 1) → E) :
    frameImage 1 *ᵥ x ∈ commonIsotropic γ ↔
      frameImage (γ⁻¹ : S.G E) *ᵥ x ∈ commonIsotropic γ⁻¹ := by
  have h_cancel : γ.val *ᵥ frameImage (γ⁻¹ : S.G E) *ᵥ x = frameImage 1 *ᵥ x := by
    rw [frameImage_mulVec, mulVec_mulVec]
    simp
  rw [mem_commonIsotropic_iff, mem_commonIsotropic_iff, mem_isotropicSpan_coe,
    mem_isotropicSpan_coe, inv_inv, h_cancel, ← frameImage_mulVec, and_comm]

/-- Let `γ` have the cell rank `j`: at every index `l ≥ j` (counted from `0`) the flags of the frame
`e_• = (e_1, …, e_ϱ, z_N)` and of `γ e_•` share a vector with leading coefficients `ζ` and `1` (one
`ζ` with `ζ ζ̄ = 1`), the leading minor of order `j` of the matrix `S.frameProducts γ` of their
products is nonzero, and `j = ϱ + 1` exactly when `S.termDisc γ ≠ 0`. Then the first `j` vectors of
`γ e_•` (the columns of `frameImage γ`) and its last vector `γ z_N`, whose indices form
`subframeIndices j`, are a basis of `γ A⁺ / I_γ`. Here `γ A⁺` is the span of `γ e_•` and
`I_γ = commonIsotropic γ = A ∩ γ A`, where `A = ⟨e_1, …, e_ϱ⟩`. -/
theorem HasCellRank.linearIndependent_mkQ_frameImage_coe_and_sup_eq (hγ : S.HasCellRank j γ) :
    LinearIndependent E
      (fun a : subframeIndices j ↦ (commonIsotropic γ).mkQ ((frameImage γ).col a)) ∧
    colSpan ((frameImage γ).submatrix id ((↑) : subframeIndices j → Fin (𝔰.ϱ + 1))) ⊔
      commonIsotropic γ = colSpan (frameImage γ) :=
  linearIndependent_mkQ_col_and_colSpan_sup_eq (commonIsotropic_le_colSpan_frameImage_coe γ)
    (fun _ ↦ hγ.eq_zero_of_mem_commonIsotropic)
    (hγ.exists_mem_commonIsotropic hγ.flagSpan_coe_sup_commonIsotropic)

/-- Let `γ` have the cell rank `j`: at every index `l ≥ j` (counted from `0`) the flags of the frame
`e_• = (e_1, …, e_ϱ, z_N)` and of `γ e_•` share a vector with leading coefficients `ζ` and `1` (one
`ζ` with `ζ ζ̄ = 1`), the leading minor of order `j` of the matrix `S.frameProducts γ` of their
products is nonzero, and `j = ϱ + 1` exactly when `S.termDisc γ ≠ 0`. If `E` contains a primitive
`5040`-th root of unity, the first `j` vectors of `e_•` (the columns of `frameImage 1`) and its last
vector `z_N`, whose indices form `subframeIndices j`, are a basis of `A⁺ / I_γ`. Here `A⁺` is the
span of `e_•`, `A = ⟨e_1, …, e_ϱ⟩` and `I_γ = commonIsotropic γ = A ∩ γ A`. -/
theorem HasCellRank.linearIndependent_mkQ_frameImage_one_and_sup_eq [HasPrimitiveRoot5040 E]
    (hγ : S.HasCellRank j γ) :
    LinearIndependent E
      (fun a : subframeIndices j ↦ (commonIsotropic γ).mkQ ((frameImage 1).col a)) ∧
    colSpan ((frameImage 1).submatrix id ((↑) : subframeIndices j → Fin (𝔰.ϱ + 1))) ⊔
      commonIsotropic γ = colSpan (frameImage 1) := by
  -- Independence is the case of `γ⁻¹` and its frame `γ⁻¹ e_•`, moved by `γ`.
  have h_zero (x : Fin (𝔰.ϱ + 1) → E) (h_off : ∀ a : Fin (𝔰.ϱ + 1), a ∉ subframeIndices j → x a = 0)
      (h_mem : frameImage 1 *ᵥ x ∈ commonIsotropic γ) : x = 0 :=
    hγ.inv.eq_zero_of_mem_commonIsotropic h_off
      ((frameImage_one_mulVec_mem_commonIsotropic_iff x).1 h_mem)
  exact linearIndependent_mkQ_col_and_colSpan_sup_eq (commonIsotropic_le_colSpan_frameImage_one γ)
    h_zero (hγ.exists_mem_commonIsotropic hγ.flagSpan_one_sup_commonIsotropic)

/-- Let `γ` have the cell rank `j`: at every index `l ≥ j` (counted from `0`) the flags of the frame
`e_• = (e_1, …, e_ϱ, z_N)` and of `γ e_•` share a vector with leading coefficients `ζ` and `1` (one
`ζ` with `ζ ζ̄ = 1`), the leading minor of order `j` of the matrix `S.frameProducts γ` of their
products is nonzero, and `j = ϱ + 1` exactly when `S.termDisc γ ≠ 0`. Let `E` contain a primitive
`5040`-th root of unity, let `A⁺` be the span of `e_•` (the columns of `frameImage 1`) and
`I_γ = commonIsotropic γ = A ∩ γ A`, where `A = ⟨e_1, …, e_ϱ⟩`. Then the subframe of the first `j`
vectors of `e_•` and `z_N` (indices `subframeIndices j`) is a basis of `A⁺ / I_γ`, and its image
under `γ` (columns of `frameImage γ`) is a basis of `γ A⁺ / I_γ`. -/
theorem HasCellRank.linearIndependent_mkQ_frameImage_and_sup_eq [HasPrimitiveRoot5040 E]
    (hγ : S.HasCellRank j γ) :
    (LinearIndependent E
        (fun a : subframeIndices j ↦ (commonIsotropic γ).mkQ ((frameImage 1).col a)) ∧
      colSpan ((frameImage 1).submatrix id ((↑) : subframeIndices j → Fin (𝔰.ϱ + 1))) ⊔
        commonIsotropic γ = colSpan (frameImage 1)) ∧
    (LinearIndependent E
        (fun a : subframeIndices j ↦ (commonIsotropic γ).mkQ ((frameImage γ).col a)) ∧
      colSpan ((frameImage γ).submatrix id ((↑) : subframeIndices j → Fin (𝔰.ϱ + 1))) ⊔
        commonIsotropic γ = colSpan (frameImage γ)) :=
  ⟨hγ.linearIndependent_mkQ_frameImage_one_and_sup_eq,
    hγ.linearIndependent_mkQ_frameImage_coe_and_sup_eq⟩

end Filling

end New
