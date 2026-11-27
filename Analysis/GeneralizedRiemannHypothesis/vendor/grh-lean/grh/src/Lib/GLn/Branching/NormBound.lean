import Lib.GLn.SchurModule.LeadingRows

/-!
# Branching from GL(n+1) to GL(n) × GL(1): the branching vector and the norm bound

This file treats the branching from `GL(n + 1)` to `GL(n) × GL(1)` for the representations of
`∏ τ, GL (N τ)`. The rows `N τ` are the rows `n τ` together with one new row, given by `ι τ`. A
weight `κ` is given by the numbers `κ τ h` of columns of height `h` at the place `τ`. This file
defines the branching vector and writes products of kernels as the minors of one filling. It
proves the norm bound for an equivariant matrix through the transposed contraction
`New.GL.extendedTensor`.

## Main definitions and results

* `New.GL.branchVector`: the product of the leading minors to the powers `γ`, with the new row
  first, so that every column of positive height contains it, and to the powers `κ`, with the new
  row last, so that no column contains it.
* `New.GL.weylNormSq_mulVec_le_of_equivariant`: the norm bound for an equivariant matrix whose
  transpose sends the extremal vector to a multiple of the branching vector.

Notions from other files:
* `New.MatrixPoly`: Polynomials over `R` in an array of variables `X (a, i)`, with rows `a : m` and
  columns `i : ℕ`.
* `New.rankAt`: The number of elements of the finite row type n_τ at the place τ;
  `New.GL.rowEquivFin n τ : n τ ≃ Fin (rankAt n τ)` is the fixed numbering of these rows, and a
  row's position is its number.
* `New.permArray`: For maps e_τ from rows to natural numbers, the array over R whose entry at row
  (τ,a), column i is 1 if e_τ(a)=i and 0 otherwise.
* `New.toPoly`: The linear map from coordinate vectors ξ to polynomials, ξ ↦ Σ_i (Gξ)_i b_i, with G
  the Gram matrix `New.weylGram` (`New.weylGramOver` is its image over another ring) and b_i the
  basis `New.nablaBasis` of products of minors; `New.GL.nablaCombination` is ξ ↦ Σ_i ξ_i b_i.
* `New.weylEval`: For an array y, the evaluation vector `ev_y` with entries b_i(y); its polynomial
  under `New.toPoly` is `New.weylKernel n κ y`.

## Relation to the literature

Known; see `Lib.GLn.Branching.IntegralMap` for sources.
-/

noncomputable section

/-!
## The branching vector and integrality of products of minors

A weight `κ` is given by the numbers `κ τ h` of columns of height `h` at the place `τ`.
`New.weylKernel n κ (permArray e)` is the product over `h < rankAt n τ` of the minors on the first
`h` rows in the order `e` and the first `h` columns, to the powers `κ τ h`; `New.rowSubst z f` is
`y ↦ f (z y)`; `New.toPoly n κ` sends a coordinate vector `ξ` to `∑ i, (G ξ) i • b i`, with `G` the
Gram matrix and `b` the basis of minor products.
-/

section BranchingVector

open Finset Matrix

namespace New.GL

variable {Φ : Type} (R : Type) [CommRing R] [Fintype Φ] {n N : Φ → Type}
  [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)] [∀ τ : Φ, Fintype (N τ)]
  (ι : ∀ τ : Φ, n τ ⊕ Unit ≃ N τ) {κ₀ γ κ' : Φ → ℕ → ℕ}

open scoped Classical in
/-- The numbering of the rows `N τ` by `0, …, rankAt N τ - 1` that gives the added row the number
`i τ` and keeps the rows of `n τ` in their fixed order. -/
def newRowOrder (i : ∀ τ : Φ, Fin (rankAt n τ + 1)) (τ : Φ) : N τ ≃ Fin (rankAt N τ) :=
  -- Insert the new row at position `i τ` into the fixed numbering `rowEquivFin n τ`, then invert.
  finCongr (rankAt_eq_succ ι τ)
    |>.trans (finSuccEquiv' (i τ))
    |>.trans (rowEquivFin n τ).symm.optionCongr
    |>.trans (Equiv.optionEquivSumPUnit (n τ))
    |>.trans (ι τ)
    |>.symm

/-- The product over `τ` and `h < rankAt N τ` of the leading `h × h` minors to the power `γ τ h`
with the added row first, and to the power `κ τ h` with it last. -/
def branchVector (γ κ : Φ → ℕ → ℕ) : MatrixPoly ((τ : Φ) × N τ) R :=
  weylKernel N γ (permArray fun (τ : Φ) (i : N τ) ↦ (newRowOrder ι 0 τ i : ℕ)) *
    weylKernel (R := R) N κ (permArray fun (τ : Φ) (i : N τ) ↦ (newRowOrder ι ⊤ τ i : ℕ))

/-- Multiplying the new row by `s τ` (substituting the matrix `blockScalar ι 1 s`, that is
`diag(1, s τ)` at each `τ`) multiplies `branchVector R ι γ κ'` by the product over `τ` of `s τ` to
the power `diagramWeight (rankAt N) γ (τ, 0)`, the number of columns of `γ` of height
`1, …, rankAt n τ`. -/
lemma rowSubst_branchVector (s : Φ → R) :
    rowSubst (blockScalar ι 1 s) (branchVector R ι γ κ') =
      (∏ τ : Φ, s τ ^ diagramWeight (rankAt N) γ (τ, 0)) • branchVector R ι γ κ' := by
  classical
  -- `blockScalar ι 1 s` is diagonal, so it multiplies each kernel by a power of `s`. The new row is
  -- first in the order for `γ`, so it lies in all columns of positive height; it is last in the
  -- order for `κ'`, so it lies in none.
  have h_triangular (e : ∀ τ : Φ, N τ ≃ Fin (rankAt N τ)) (τ : Φ) :
      (blockScalar (R := R) ι 1 s τ)ᵀ.BlockTriangular (e τ) := by
    have h_diagonal : blockScalar (R := R) ι 1 s τ =
        diagonal (Sum.elim (fun _ : n τ ↦ (1 : R)) (fun _ : Unit ↦ s τ) ∘ (ι τ).symm) := by
      rw [blockScalar, Pi.one_apply, ← diagonal_one, fromBlocks_diagonal, reindex_apply,
        submatrix_diagonal_equiv]
    rw [h_diagonal, diagonal_transpose]
    exact blockTriangular_diagonal _
  rw [branchVector, map_mul, rowSubst_weylKernel_permArray _ _ (h_triangular _),
    rowSubst_weylKernel_permArray _ _ (h_triangular _)]
  simp [newRowOrder, blockScalar, rankAt_eq_succ ι, reindex_equiv (ι _), diagramWeight_apply,
    Nat.Ioo_eq_range']

/-! ### The product of the two kernels as the minors of one filling -/

variable {R} {κ : Φ → ℕ → ℕ}

/-- For numberings `e τ` of the rows, the kernel at the array `permArray e` is the product over `τ`
and `h` of the minor on the first `h` rows in the order `e τ`, to the power `κ τ h`. -/
lemma weylKernel_permArray_eq_prod_minor (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ)) :
    weylKernel n κ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)) =
      ∏ τ : Φ, ∏ h : Fin (rankAt n τ),
        minor R (Sigma.mk τ ∘ (e τ).symm ∘ Fin.castLE h.is_le') ^ κ τ h := by
  classical
  have h_entry (τ : Φ) (h : Fin (rankAt n τ)) (s t : Fin h) :
      ∑ a : n τ, permArray (R := R) (fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)) (⟨τ, a⟩, s) •
          MvPolynomial.X (R := R) ((⟨τ, a⟩ : Σ τ : Φ, n τ), (t : ℕ)) =
        MvPolynomial.X (⟨τ, (e τ).symm (Fin.castLE h.is_le' s)⟩, (t : ℕ)) := by
    have h_iff (a : n τ) : (e τ a : ℕ) = s ↔ a = (e τ).symm (Fin.castLE h.is_le' s) := by
      simp [Equiv.eq_symm_apply, Fin.ext_iff]
    simp [permArray, h_iff, ite_smul]
  simp only [weylKernel, rowSubst_highestPoly, prod_range, h_entry, minor, Function.comp_apply]

omit [Fintype Φ] in
/-- Substituting the permutation matrices of `σ` carries the minor on given rows to the minor on
their images under `σ τ`. -/
lemma rowSubst_permMatrix_minor (σ : ∀ τ : Φ, Equiv.Perm (n τ)) {τ : Φ} {h : ℕ}
    (rows : Fin h → n τ) :
    rowSubst (fun τ : Φ ↦ (σ τ).permMatrix R) (minor R (Sigma.mk τ ∘ rows)) =
      minor R (Sigma.mk τ ∘ σ τ ∘ rows) := by
  rw [minor, minor, AlgHom.map_det]
  refine congrArg det (Matrix.ext fun s t ↦ ?_)
  simp [rowSubst, PEquiv.toMatrix_apply, ite_smul]

/-- The cyclic permutation of `Fin N` that moves `p` to the front and each position below `p` to the
next one; it is the identity if `N ≤ p`. -/
def frontPermutation (N p : ℕ) : Equiv.Perm (Fin N) :=
  if hp : p < N then Fin.cycleRange ⟨p, hp⟩ else 1

/-- For `p < N` the permutation sends a position below `p` to the next one and `p` to `0`, and it
fixes the later positions. -/
lemma frontPermutation_val {N p : ℕ} (hp : p < N) (i : Fin N) :
    (frontPermutation N p i : ℕ) =
      if (i : ℕ) < p then (i : ℕ) + 1 else if (i : ℕ) = p then 0 else (i : ℕ) := by
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, N = M + 1 := ⟨N - 1, by omega⟩
  rw [frontPermutation, dite_eq_left hp]
  split_ifs with h_lt h_eq
  · exact Fin.coe_cycleRange_of_lt h_lt
  · rw [Fin.cycleRange_of_eq (show i = ⟨p, hp⟩ from Fin.ext h_eq), Fin.val_zero]
  · rw [Fin.cycleRange_of_gt (show ⟨p, hp⟩ < i by grind)]

/-- The rotation of `Fin N` sends each position other than the last to the next one. -/
lemma finRotate_val {N : ℕ} (i : Fin N) (hi : (i : ℕ) + 1 < N) :
    (finRotate N i : ℕ) = i + 1 := by
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, N = M + 1 := ⟨N - 1, by omega⟩
  exact coe_finRotate_of_ne_last fun h_last ↦ by simp [h_last] at hi

variable (n) in
/-- The renaming of the rows `n τ` that moves the row at position `p τ` to the front and each
earlier row to the next position. -/
def frontRenaming (p : Φ → ℕ) (τ : Φ) : Equiv.Perm (n τ) :=
  (rowEquivFin n τ).symm.permCongr (frontPermutation (rankAt n τ) (p τ))

/-- The rows of column `j` among the columns of height `h`, when the first `k` of these columns hold
the rows at the positions `0, …, h - 1` and the others those at the positions `1, …, h`. -/
def extremalRows {τ : Φ} (k : ℕ) (h : Fin (rankAt n τ)) (j : ℕ) : Fin h → n τ :=
  if j < k then (rowEquivFin n τ).symm ∘ Fin.castLE h.is_le'
  else (rowEquivFin n τ).symm ∘ finRotate (rankAt n τ) ∘ Fin.castLE h.is_le'

/-- Let `κ₀ τ h = κ' τ h + γ τ h` for `0 < h < rankAt n τ`. The product of the kernel of `γ` at the
row order shifted by one and the kernel of `κ'` at the row order `rowEquivFin` is the product, over
the columns of `κ₀`, of the minors on the rows `extremalRows (κ' τ h) h j`. -/
lemma weylKernel_mul_weylKernel_eq_prod_minor
    (hκ₀ : ∀ τ : Φ, ∀ h ∈ Ioo 0 (rankAt n τ), κ₀ τ h = (κ' + γ) τ h) :
    weylKernel n γ (permArray fun (τ : Φ) (a : n τ) ↦
          ((finRotate (rankAt n τ)).symm (rowEquivFin n τ a) : ℕ)) *
        weylKernel n κ' (permArray fun (τ : Φ) (a : n τ) ↦ (rowEquivFin n τ a : ℕ)) =
      ∏ τ : Φ, ∏ h : Fin (rankAt n τ), ∏ j : Fin (κ₀ τ h),
        minor R (Sigma.mk τ ∘ extremalRows (κ' τ h) h j) := by
  -- Both sides are products over `τ` and `h`. For a height `h > 0` the first `κ' τ h` columns
  -- give the minor in the order `rowEquivFin`, and the other `γ τ h` the minor in the shifted
  -- order.
  have h_shift : weylKernel n γ (permArray fun (τ : Φ) (a : n τ) ↦
        ((finRotate (rankAt n τ)).symm (rowEquivFin n τ a) : ℕ)) =
      ∏ τ : Φ, ∏ h : Fin (rankAt n τ), minor R (Sigma.mk τ ∘ (rowEquivFin n τ).symm ∘
        finRotate (rankAt n τ) ∘ Fin.castLE h.is_le') ^ γ τ h :=
    weylKernel_permArray_eq_prod_minor fun τ ↦ (rowEquivFin n τ).trans (finRotate _).symm
  simp only [weylKernel_permArray_eq_prod_minor (rowEquivFin n), h_shift, ← prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ ↦ Finset.prod_congr rfl fun h _ ↦ ?_
  obtain h_zero | h_pos : (h : ℕ) = 0 ∨ 0 < (h : ℕ) := Nat.eq_zero_or_pos h
  · have h_empty : IsEmpty (Fin h) := ⟨fun s ↦ s.pos.ne' h_zero⟩
    simp [minor]
  have h_split : κ₀ τ h = κ' τ h + γ τ h := hκ₀ τ h (mem_Ioo.mpr ⟨h_pos, h.isLt⟩)
  rw [h_split, Fin.prod_univ_add, mul_comm]
  simp [extremalRows]

/-- A filling of the diagram of `κ₀` without its first `p τ` rows, with entries in the last
`rankAt n τ - p τ` rows, numbered from `0`. Among the columns of height `k`, the first
`κ' τ (p τ + k)` hold the rows `0, …, k - 1` and the others the rows `1, …, k`. -/
def extremalFilling (p : Φ → ℕ) (κ₀ κ' : Φ → ℕ → ℕ) :
    ColumnFilling (fun τ : Φ ↦ Fin (rankAt n τ - p τ)) (flatColumns p κ₀) :=
  fun (τ : Φ) (k : Fin (rankAt (fun σ : Φ ↦ Fin (rankAt n σ - p σ)) τ)) (j : Fin (κ₀ τ (p τ + k))) ↦
    if (j : ℕ) < κ' τ (p τ + k) then ⟨Fin.castLE k.is_le', Fin.strictMono_castLE _⟩
    else ⟨fun s : Fin k ↦ ⟨s + 1, by omega⟩, fun _ _ hst ↦ Nat.add_lt_add_right hst 1⟩

omit [Fintype Φ] [∀ τ, DecidableEq (n τ)] in
/-- Put the first `p τ` rows on top of `extremalFilling p κ₀ κ'`. In column `j` of height `h` the
entry of index `s` is then the position `s` if `s < p τ` or `j < κ' τ h`, and `s + 1` otherwise. -/
lemma leadingWedge_extremalFilling {p : Φ → ℕ}
    (h_rank : ∀ τ : Φ, p τ + rankAt (fun σ : Φ ↦ Fin (rankAt n σ - p σ)) τ = rankAt n τ) (τ : Φ)
    (h : Fin (rankAt n τ)) (j : Fin (κ₀ τ h)) (s : Fin h) :
    ((leadingWedge h_rank (extremalFilling p κ₀ κ') τ h j).val s : ℕ) =
      if (s : ℕ) < p τ ∨ (j : ℕ) < κ' τ h then (s : ℕ) else (s : ℕ) + 1 := by
  obtain ⟨h, rfl⟩ : ∃ i : Fin (p τ + rankAt (fun σ : Φ ↦ Fin (rankAt n σ - p σ)) τ),
      Fin.cast (h_rank τ) i = h := ⟨Fin.cast (h_rank τ).symm h, rfl⟩
  induction h using Fin.addCases with
  | left h =>
    rw [ite_eq_left (Or.inl (s.isLt.trans h.isLt))]
    exact leadingWedge_castAdd h_rank _ τ h j s
  | right k =>
    rw [leadingWedge_natAdd h_rank (extremalFilling p κ₀ κ') τ k j]
    induction s using Fin.addCases with
    | left a => simp [Fin.append_left]
    | right a =>
      by_cases hj : (j : ℕ) < κ' τ (p τ + k) <;>
        simp [Fin.append_right, extremalFilling, hj, add_assoc]

omit [Fintype Φ] [∀ τ, DecidableEq (n τ)] in
/-- Let a column of height `h` hold the positions `f s = s` if `s < p τ` or `j < k`, and
`f s = s + 1` otherwise, where `j < k` does not occur for `0 < h ≤ p τ`. After the row at position
`p τ` is moved to the front, its minor is that on `extremalRows k h j` up to sign. -/
lemma exists_minor_extremalRows_eq_smul {τ : Φ} {p : Φ → ℕ} {h : Fin (rankAt n τ)}
    (hp : p τ < rankAt n τ) {j k : ℕ} {f : Fin h → Fin (rankAt n τ)}
    (hf : ∀ s : Fin h, (f s : ℕ) = if (s : ℕ) < p τ ∨ j < k then (s : ℕ) else (s : ℕ) + 1)
    (h_low : 0 < (h : ℕ) → (h : ℕ) ≤ p τ → k ≤ j) :
    ∃ ε : ℤˣ, minor ℤ (Sigma.mk τ ∘ extremalRows k h j) =
      (ε : ℤ) • minor ℤ (Sigma.mk τ ∘ frontRenaming n p τ ∘ (rowEquivFin n τ).symm ∘ f) := by
  obtain h_zero | h_pos : (h : ℕ) = 0 ∨ 0 < (h : ℕ) := Nat.eq_zero_or_pos h
  · have h_empty : IsEmpty (Fin h) := ⟨fun s ↦ s.pos.ne' h_zero⟩
    exact ⟨1, by simp [minor]⟩
  by_cases hj : j < k
  · -- As `p τ < h`, the renaming permutes the first `h` rows among themselves.
    have hp_lt : p τ < h := lt_of_not_ge fun h_le ↦ (h_low h_pos h_le).not_gt hj
    let ρ : Equiv.Perm (Fin h) := (frontPermutation h (p τ)).symm
    have h_rows : extremalRows k h j = (frontRenaming n p τ ∘ (rowEquivFin n τ).symm ∘ f) ∘ ρ := by
      funext s
      obtain ⟨t, rfl⟩ := (frontPermutation h (p τ)).surjective s
      simp [extremalRows, frontRenaming, ρ, Fin.ext_iff, hj, hf, frontPermutation_val hp_lt,
        frontPermutation_val hp]
    refine ⟨Equiv.Perm.sign ρ, ?_⟩
    rw [h_rows, minor, minor, zsmul_eq_mul]
    exact det_permute ρ (of fun s t : Fin h ↦ MvPolynomial.X (R := ℤ)
      ((⟨τ, frontRenaming n p τ ((rowEquivFin n τ).symm (f s))⟩ : Σ σ : Φ, n σ), (t : ℕ)))
  · -- The renaming sends the positions of the column, which omit `p τ`, to `1, …, h` in this order.
    have h_rows : extremalRows k h j = frontRenaming n p τ ∘ (rowEquivFin n τ).symm ∘ f := by
      funext s
      have h_rotate : (finRotate (rankAt n τ) (Fin.castLE h.is_le' s) : ℕ) = s + 1 :=
        finRotate_val _ (show (s : ℕ) + 1 < rankAt n τ by omega)
      have h_front : (frontPermutation (rankAt n τ) (p τ) (f s) : ℕ) = s + 1 := by
        grind [frontPermutation_val]
      simpa [extremalRows, frontRenaming, Fin.ext_iff, hj] using h_rotate.trans h_front.symm
    exact ⟨1, by simp [h_rows]⟩

/-- Let `p τ` be below the number of rows `rankAt n τ` whenever there are rows, and let `h_rank`
say that the first `p τ` rows and the remaining `rankAt n τ - p τ` make up all the rows. Let `κ'`
have no column of height `h` with `0 < h ≤ p τ`, and let `κ₀ τ h = κ' τ h + γ τ h` for
`0 < h < rankAt n τ`. Put the first `p τ` rows on top of `extremalFilling p κ₀ κ'` and move the row
at position `p τ` to the front. Up to sign, the product of minors becomes the product of the kernel
of `γ` at the row order shifted by one and the kernel of `κ'` at the row order `rowEquivFin`. -/
lemma exists_smul_rowSubst_extremalFilling {p : Φ → ℕ}
    (h_rank : ∀ τ : Φ, p τ + rankAt (fun σ : Φ ↦ Fin (rankAt n σ - p σ)) τ = rankAt n τ)
    (hp : ∀ τ : Φ, 0 < rankAt n τ → p τ < rankAt n τ)
    (h_low : ∀ (τ : Φ) (h : ℕ), 0 < h → h ≤ p τ → κ' τ h = 0)
    (hκ₀ : ∀ τ : Φ, ∀ h ∈ Ioo 0 (rankAt n τ), κ₀ τ h = (κ' + γ) τ h) :
    ∃ ε : ℤˣ, (ε : ℤ) • rowSubst (fun τ : Φ ↦ (frontRenaming n p τ).permMatrix ℤ)
        (fillingPoly ℤ (leadingWedge h_rank (extremalFilling p κ₀ κ'))) =
      weylKernel n γ (permArray fun (τ : Φ) (a : n τ) ↦
          ((finRotate (rankAt n τ)).symm (rowEquivFin n τ a) : ℕ)) *
        weylKernel n κ' (permArray fun (τ : Φ) (a : n τ) ↦ (rowEquivFin n τ a : ℕ)) := by
  set T : ColumnFilling n κ₀ := leadingWedge h_rank (extremalFilling p κ₀ κ')
  have h_column : ∀ (τ : Φ) (h : Fin (rankAt n τ)) (j : Fin (κ₀ τ h)), ∃ ε : ℤˣ,
      minor ℤ (Sigma.mk τ ∘ extremalRows (κ' τ h) h j) =
        (ε : ℤ) • minor ℤ (Sigma.mk τ ∘ frontRenaming n p τ ∘ fillingRows T τ h j) :=
    fun τ h j ↦ exists_minor_extremalRows_eq_smul (hp τ h.pos)
      (leadingWedge_extremalFilling h_rank τ h j) fun h_pos h_le ↦ by simp [h_low τ h h_pos h_le]
  choose ε hε using h_column
  have h_subst : rowSubst (fun τ : Φ ↦ (frontRenaming n p τ).permMatrix ℤ) (fillingPoly ℤ T) =
      ∏ τ : Φ, ∏ h : Fin (rankAt n τ), ∏ j : Fin (κ₀ τ h),
        minor ℤ (Sigma.mk τ ∘ frontRenaming n p τ ∘ fillingRows T τ h j) := by
    simp only [fillingPoly, tableauPoly, map_prod, rowSubst_permMatrix_minor]
  refine ⟨∏ τ : Φ, ∏ h : Fin (rankAt n τ), ∏ j : Fin (κ₀ τ h), ε τ h j, ?_⟩
  rw [weylKernel_mul_weylKernel_eq_prod_minor hκ₀, h_subst]
  simp only [hε, zsmul_eq_mul, Units.coe_prod, Int.cast_prod, Finset.prod_mul_distrib]

/-- Let `κ'` have no column of height below `q`, and let `κ₀ τ h = κ' τ h + γ τ h` for
`0 < h < rankAt n τ`. Here `weylKernel n κ y` is the polynomial `f(yᵀx)` in `x`, with `f` the
product of leading minors for `κ`, and `toPoly n κ₀ η` is `Σ_i (Gη)_i b_i` for a Weyl vector `η`
(Gram matrix `G`, basis minor products `b_i`). Then some integer `c` with `0 < c` (a hook number)
satisfies two claims. (a) `c ≤ (L ^ L) ^ 3` for every bound `L` of the number of boxes of `κ₀` in
the columns of height `h` with `q ≤ h < rankAt n τ`. (b) `c` times `weylKernel n γ` at the
permutation array of `rowEquivFin` shifted cyclically by one, times `weylKernel n κ'` at that of
`rowEquivFin`, equals `toPoly n κ₀ η` for some `η : WeylIndexFamily n κ₀ → ℤ`. -/
lemma exists_smul_weylKernel_mul_eq_toPoly [DecidableEq Φ] {q : ℕ}
    (hq : ∀ τ : Φ, ∀ i < q, κ' τ i = 0)
    (hκ₀ : ∀ τ : Φ, ∀ h ∈ Ioo 0 (rankAt n τ), κ₀ τ h = (κ' + γ) τ h) :
    ∃ c : ℤ, 0 < c ∧
      (∀ L : ℕ, ∑ τ : Φ, ∑ h ∈ Ico q (rankAt n τ), h * κ₀ τ h ≤ L → c ≤ (L ^ L) ^ 3) ∧
      ∃ η : WeylIndexFamily n κ₀ → ℤ,
        c • (weylKernel n γ (permArray fun (τ : Φ) (a : n τ) ↦
              ((finRotate (rankAt n τ)).symm (rowEquivFin n τ a) : ℕ)) *
            weylKernel n κ' (permArray fun (τ : Φ) (a : n τ) ↦ (rowEquivFin n τ a : ℕ)) :
              MatrixPoly (Σ τ : Φ, n τ) ℤ) =
          toPoly n κ₀ η := by
  -- Let `p` be `q - 1`, capped at the last position. Every column of height above `p` contains the
  -- rows at the positions `1, …, p`, and a column of height `h ≤ p` holds those at `1, …, h`. Up to
  -- a renaming of the rows and a sign, the product is thus that of a filling with `p` leading rows,
  -- and the hook number `c` of the diagram without its first `p` rows makes `c` times that product
  -- the image of an integral vector.
  let p : Φ → ℕ := fun τ ↦ min (q - 1) (rankAt n τ - 1)
  have h_rank (τ : Φ) : p τ + rankAt (fun σ : Φ ↦ Fin (rankAt n σ - p σ)) τ = rankAt n τ := by
    simp [rankAt, p]
  have hp (τ : Φ) (h_pos : 0 < rankAt n τ) : p τ < rankAt n τ := by grind
  have h_low (τ : Φ) (h : ℕ) (h_pos : 0 < h) (h_le : h ≤ p τ) : κ' τ h = 0 := hq τ h (by grind)
  let c : ℤ := hookNumber (flatColumns p κ₀) (rankAt fun τ : Φ ↦ Fin (rankAt n τ - p τ))
  obtain ⟨η, hη⟩ : ∃ η : WeylIndexFamily n κ₀ → ℤ,
      toPoly n κ₀ η = c • fillingPoly ℤ (leadingWedge h_rank (extremalFilling p κ₀ κ')) :=
    exists_toPoly_eq_hookNumber_smul_leadingWedge h_rank _
  obtain ⟨ε, hε⟩ := exists_smul_rowSubst_extremalFilling h_rank hp h_low hκ₀
  -- The Schur matrix of the transposed permutation matrices acts as the renaming of the rows.
  let P (τ : Φ) : Matrix (n τ) (n τ) ℤ := (frontRenaming n p τ).permMatrix ℤ
  have h_rename :
      toPoly n κ₀ (schur κ₀ (fun τ : Φ ↦ (P τ)ᵀ) *ᵥ η) = rowSubst P (toPoly n κ₀ η) := by
    simp [toPoly_schur FitsRanks.refl, detPow]
  refine ⟨c, hookNumber_pos, fun L hL ↦ ?_, (ε : ℤ) • schur κ₀ (fun τ : Φ ↦ (P τ)ᵀ) *ᵥ η, ?_⟩
  · -- A column of height `h ≥ p τ` leaves `h - p τ` boxes below the first `p τ` rows, which is
    -- `0` if `h < q`.
    have h_boxes (τ : Φ) :
        ∑ h ∈ range (rankAt (fun σ : Φ ↦ Fin (rankAt n σ - p σ)) τ), h * flatColumns p κ₀ τ h ≤
          ∑ h ∈ Ico q (rankAt n τ), h * κ₀ τ h :=
      calc
        _ = ∑ h ∈ Ico (p τ) (rankAt n τ), (h - p τ) * κ₀ τ h := by
          simp [sum_Ico_eq_sum_range, flatColumns, rankAt]
        _ ≤ ∑ h ∈ Ico q (rankAt n τ), (h - p τ) * κ₀ τ h := by
          refine sum_le_sum_of_ne_zero fun h h_mem h_ne ↦ ?_
          have h_above : h - p τ ≠ 0 := left_ne_zero_of_mul h_ne
          grind
        _ ≤ ∑ h ∈ Ico q (rankAt n τ), h * κ₀ τ h := by
          gcongr
          exact Nat.sub_le _ _
    exact hookNumber_le ((sum_le_sum fun τ _ ↦ h_boxes τ).trans hL)
  · rw [map_smul, h_rename, hη, map_smul, smul_comm (ε : ℤ) c, hε]

end New.GL

end BranchingVector

/-!
## The norm of a branching map

The matrix of a branching map is a multiple of the contraction of tensors followed by the orthogonal
projection to the Weyl module. The contraction takes the coefficient of the new basis vector in the
shortened columns and deletes the terms that contain it in the others. It is used here through its
transpose `New.GL.extendedTensor`, which is isometric on the evaluation vectors after division by
a power of the determinant. The norm bound follows because an orthogonal projection does not
increase norms.
-/

section Contraction

open MvPolynomial Finset Matrix ComplexOrder

namespace New.GL

variable {Φ : Type} [Fintype Φ] {n N : Φ → Type} [∀ τ : Φ, Fintype (n τ)]
  [∀ τ : Φ, DecidableEq (n τ)] [∀ τ : Φ, Fintype (N τ)] [∀ τ : Φ, DecidableEq (N τ)]
  (ι : ∀ τ : Φ, n τ ⊕ Unit ≃ N τ) {κ₀ γ κ' : Φ → ℕ → ℕ} {R : Type} [CommRing R]

/-- The minor of `z` on the first `h` rows and the first `h` columns in the numbering `e`. -/
def leadingMinorAlong {m : Type} {k : ℕ} (e : m ≃ Fin k) (z : Matrix m m R) {h : ℕ}
    (h_le : h ≤ k) : R :=
  (z.submatrix (e.symm ∘ Fin.castLE h_le) (e.symm ∘ Fin.castLE h_le)).det

/-- The tableau of `branchVector` at `τ`. Of the columns of height `h`, the first `γ τ h` hold the
first `h` rows in the numbering with the new row first, and the other `κ' τ h` hold the first `h`
rows in the numbering with the new row last. -/
def branchRows (γ κ' : Φ → ℕ → ℕ) (τ : Φ) : Tableau (N τ) (rankAt N τ) ((γ + κ') τ) :=
  fun h : Fin (rankAt N τ) ↦ Fin.addCases
    (fun _ : Fin (γ τ h) ↦ (newRowOrder ι 0 τ).symm ∘ Fin.castLE h.is_le')
    (fun _ : Fin (κ' τ h) ↦ (newRowOrder ι ⊤ τ).symm ∘ Fin.castLE h.is_le')

omit [∀ τ : Φ, DecidableEq (n τ)] in
/-- The branching vector is the product of the minors on the columns of `branchRows`. -/
lemma branchVector_eq_prod_tableauPoly :
    branchVector R ι γ κ' = ∏ τ : Φ, tableauPoly R (Sigma.mk τ) (branchRows ι γ κ' τ) := by
  simp [branchVector, weylKernel_permArray_eq_prod_minor, branchRows, tableauPoly,
    Fin.prod_univ_add, Finset.prod_mul_distrib]

/-- The transpose of the contraction, applied to the tensor whose factor in a column of height `h`
is the exterior product of the first `h` rows of `a`. The transpose puts the new basis vector in
front of the shortened columns and leaves the others unchanged, so the coordinate at a filling `T`
is the product over the columns of the minor of `diag(a, 1)` with rows from `branchRows` and
columns from `T`. -/
def extendedTensor (γ κ' : Φ → ℕ → ℕ) (a : ∀ τ : Φ, Matrix (n τ) (n τ) R)
    (T : ColumnFilling N (γ + κ')) : R :=
  ∏ τ : Φ, ∏ h : Fin (rankAt N τ), ∏ j : Fin ((γ + κ') τ h),
    ((blockScalar ι a 1 τ).submatrix (branchRows ι γ κ' τ h j) (fillingRows T τ h j)).det

section

omit [Fintype Φ]

omit [∀ τ : Φ, DecidableEq (n τ)] [∀ τ : Φ, DecidableEq (N τ)] in
/-- In the numbering `newRowOrder ι i τ` that gives the new row the number `i τ`, the old row with
number `s` has the number `s` if `s < i τ` and `s + 1` otherwise. -/
lemma newRowOrder_symm_of_val_eq_succAbove {i : ∀ τ : Φ, Fin (rankAt n τ + 1)} {τ : Φ}
    (s : Fin (rankAt n τ)) {t : Fin (rankAt N τ)} (h_val : (t : ℕ) = (i τ).succAbove s) :
    (newRowOrder ι i τ).symm t = ι τ (.inl ((rowEquivFin n τ).symm s)) := by
  obtain rfl : t = Fin.cast (rankAt_eq_succ ι τ).symm ((i τ).succAbove s) := Fin.ext h_val
  simp [newRowOrder, ← Equiv.optionCongr_symm]

omit [∀ τ : Φ, DecidableEq (n τ)] [∀ τ : Φ, DecidableEq (N τ)] in
/-- With the new row first, the leading minor of size `h + 1` of `diag(p, 1)` is the leading minor
of size `h` of `p`. -/
lemma leadingMinorAlong_newRowOrder_zero (p : ∀ τ : Φ, Matrix (n τ) (n τ) R) (τ : Φ) {h : ℕ}
    (h_old : h ≤ rankAt n τ) (h_new : h + 1 ≤ rankAt N τ) :
    leadingMinorAlong (newRowOrder ι 0 τ) (blockScalar ι p 1 τ) h_new =
      leadingMinorAlong (rowEquivFin n τ) (p τ) h_old := by
  have h_rows : (newRowOrder ι 0 τ).symm ∘ Fin.castLE h_new =
      ι τ ∘ Fin.cons (.inr ()) fun s : Fin h ↦ .inl ((rowEquivFin n τ).symm (s.castLE h_old)) := by
    funext s
    cases s using Fin.cases with
    | zero => rfl
    | succ s => exact newRowOrder_symm_of_val_eq_succAbove ι (Fin.castLE h_old s) rfl
  rw [leadingMinorAlong, h_rows, det_succ_row_zero]
  simp [Fin.sum_univ_succ, blockScalar, leadingMinorAlong, submatrix]

omit [∀ τ : Φ, DecidableEq (n τ)] [∀ τ : Φ, DecidableEq (N τ)] in
/-- With the new row last, the leading minors of `diag(p, 1)` of size at most `rankAt n τ` are
those of `p`. -/
lemma leadingMinorAlong_newRowOrder_top (p : ∀ τ : Φ, Matrix (n τ) (n τ) R) (τ : Φ) {h : ℕ}
    (h_old : h ≤ rankAt n τ) (h_new : h ≤ rankAt N τ) :
    leadingMinorAlong (newRowOrder ι ⊤ τ) (blockScalar ι p 1 τ) h_new =
      leadingMinorAlong (rowEquivFin n τ) (p τ) h_old := by
  have h_rows : (newRowOrder ι ⊤ τ).symm ∘ Fin.castLE h_new =
      fun s : Fin h ↦ ι τ (.inl ((rowEquivFin n τ).symm (Fin.castLE h_old s))) :=
    funext fun s ↦ newRowOrder_symm_of_val_eq_succAbove ι _ (by simp [Fin.top_eq_last])
  rw [leadingMinorAlong, h_rows]
  simp [blockScalar, leadingMinorAlong, submatrix]

omit [∀ τ : Φ, DecidableEq (N τ)] in
/-- Let `κ₀ τ h = κ' τ h + γ τ (h + 1)` for `0 < h < rankAt n τ`, and let `p τ` be square matrices
over a commutative ring `R`. In the tableau `branchRows ι γ κ' τ`, of the columns of height `h`, the
first `γ τ h` hold the first `h` rows with the new row first, and the other `κ' τ h` hold the first
`h` rows with the new row last. The product over all these columns of the principal minor of
`diag(p τ, 1)` (`blockScalar ι p 1 τ`) on the column's rows equals `det (p τ) ^ κ' τ (rankAt n τ)`
times the product over `h < rankAt n τ` of the `h`-th leading minor of `p τ` along `rowEquivFin`
raised to the power `κ₀ τ h`. -/
lemma prod_det_blockScalar_branchRows
    (hκ₀ : ∀ τ : Φ, ∀ h ∈ Ioo 0 (rankAt n τ), κ₀ τ h = κ' τ h + γ τ (h + 1))
    (p : ∀ τ : Φ, Matrix (n τ) (n τ) R) (τ : Φ) :
    ∏ h : Fin (rankAt N τ), ∏ j : Fin ((γ + κ') τ h),
        ((blockScalar ι p 1 τ).submatrix (branchRows ι γ κ' τ h j) (branchRows ι γ κ' τ h j)).det =
      (p τ).det ^ κ' τ (rankAt n τ) *
        ∏ h : Fin (rankAt n τ), leadingMinorAlong (rowEquivFin n τ) (p τ) h.is_le' ^ κ₀ τ h := by
  set k : ℕ := rankAt n τ
  let A (h : Fin (k + 1)) : R := leadingMinorAlong (rowEquivFin n τ) (p τ) h.is_le
  let e : Fin (k + 1) ≃ Fin (rankAt N τ) := finCongr (rankAt_eq_succ ι τ).symm
  set Z : Matrix (N τ) (N τ) R := blockScalar ι p 1 τ
  have h_columns (h : Fin (rankAt N τ)) :
      ∏ j : Fin ((γ + κ') τ h),
          (Z.submatrix (branchRows ι γ κ' τ h j) (branchRows ι γ κ' τ h j)).det =
        leadingMinorAlong (newRowOrder ι 0 τ) Z h.is_le' ^ γ τ h *
          leadingMinorAlong (newRowOrder ι ⊤ τ) Z h.is_le' ^ κ' τ h := by
    refine (Fin.prod_univ_add _).trans ?_
    simp [branchRows, leadingMinorAlong]
  have h_first (h : Fin k) :
      leadingMinorAlong (newRowOrder ι 0 τ) Z (e h.succ).is_le' = A h.castSucc :=
    leadingMinorAlong_newRowOrder_zero ι p τ _ _
  have h_last (h : Fin (k + 1)) : leadingMinorAlong (newRowOrder ι ⊤ τ) Z (e h).is_le' = A h :=
    leadingMinorAlong_newRowOrder_top ι p τ _ _
  have h_empty : A 0 = 1 := det_fin_zero
  have h_full : A (Fin.last k) = (p τ).det := det_submatrix_equiv_self (rowEquivFin n τ).symm (p τ)
  calc
    _ = (∏ h : Fin (k + 1), leadingMinorAlong (newRowOrder ι 0 τ) Z (e h).is_le' ^ γ τ h) *
          ∏ h : Fin (k + 1), A h ^ κ' τ h := by
      rw [← e.prod_comp, ← Finset.prod_mul_distrib]
      simp only [h_columns, h_last]
      simp [e]
    _ = (∏ h : Fin k, A h.castSucc ^ γ τ (h + 1)) *
          ((∏ h : Fin k, A h.castSucc ^ κ' τ h) * (p τ).det ^ κ' τ k) := by
      rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc (fun h : Fin (k + 1) ↦ A h ^ κ' τ h), h_full]
      simp only [h_first]
      simp [e, leadingMinorAlong]
    _ = (p τ).det ^ κ' τ k * ∏ h : Fin k, A h.castSucc ^ κ₀ τ h := by
      rw [← mul_assoc, mul_comm, ← Finset.prod_mul_distrib]
      refine congrArg _ (Finset.prod_congr rfl fun h _ ↦ ?_)
      obtain h_zero | h_pos := Nat.eq_zero_or_pos (h : ℕ)
      · simp [show h.castSucc = 0 from Fin.ext h_zero, h_empty]
      · rw [hκ₀ τ h (mem_Ioo.2 ⟨h_pos, h.isLt⟩), pow_add, mul_comm]

end

variable [DecidableEq Φ]

omit [∀ τ : Φ, DecidableEq (N τ)] in
/-- The extended tensors of `a` and `b` pair to the product of the leading minors of `a bᵀ` for
`κ₀`, times a power of the determinant. This is the Cauchy–Binet formula in each column. -/
lemma extendedTensor_dotProduct
    (hκ₀ : ∀ τ : Φ, ∀ h ∈ Ioo 0 (rankAt n τ), κ₀ τ h = κ' τ h + γ τ (h + 1))
    (a b : ∀ τ : Φ, Matrix (n τ) (n τ) R) :
    extendedTensor ι γ κ' a ⬝ᵥ extendedTensor ι γ κ' b =
      ∏ τ : Φ, (a τ * (b τ)ᵀ).det ^ κ' τ (rankAt n τ) * ∏ h : Fin (rankAt n τ),
        leadingMinorAlong (rowEquivFin n τ) (a τ * (b τ)ᵀ) h.is_le' ^ κ₀ τ h := by
  have h_binet (τ : Φ) {h : ℕ} (U : Fin h → N τ) :
      ∑ I : IncreasingMap (rankAt N τ) h,
          ((blockScalar ι a 1 τ).submatrix U ((rowEquivFin N τ).symm ∘ I.1)).det *
            ((blockScalar ι b 1 τ).submatrix U ((rowEquivFin N τ).symm ∘ I.1)).det =
        ((blockScalar ι (fun σ : Φ ↦ a σ * (b σ)ᵀ) 1 τ).submatrix U U).det := by
    have h_prod : blockScalar ι (fun σ : Φ ↦ a σ * (b σ)ᵀ) 1 τ =
        blockScalar ι a 1 τ * (blockScalar ι b 1 τ)ᵀ := by
      simp [blockScalar, fromBlocks_transpose, fromBlocks_multiply]
    rw [h_prod, submatrix_mul _ _ U (rowEquivFin N τ).symm U (rowEquivFin N τ).symm.bijective,
      det_mul_eq_sum_increasing]
    refine Finset.sum_congr rfl fun I _ ↦ congrArg _ ?_
    rw [← det_transpose]
    rfl
  simp only [← prod_det_blockScalar_branchRows ι hκ₀ (fun σ : Φ ↦ a σ * (b σ)ᵀ), ← h_binet,
    Fintype.prod_sum, dotProduct, extendedTensor, ← Finset.prod_mul_distrib]
  -- The rows of a column filling are `fillingRows` by definition.
  rfl

/-- The Gram pairing of the evaluation vectors at `y` and `z` is the product of the leading minors
of `yᵀ z` for `κ₀`, where `y` and `z` are cut down to their square parts. -/
lemma weylEval_dotProduct_weylGram_mulVec_weylEval (y z : (Σ τ : Φ, n τ) × ℕ → R) :
    weylEval n κ₀ y ⬝ᵥ weylGramOver *ᵥ weylEval n κ₀ z =
      ∏ τ : Φ, ∏ h : Fin (rankAt n τ), leadingMinorAlong (rowEquivFin n τ)
        ((squarePart (rowEquivFin n) y τ)ᵀ * squarePart (rowEquivFin n) z τ) h.is_le' ^ κ₀ τ h := by
  rw [← eval_toPoly, toPoly_weylEval, weylKernel, rowSubst_highestPoly]
  simp only [map_prod, map_pow, RingHom.map_det, prod_range]
  refine Finset.prod_congr rfl fun τ _ ↦ Finset.prod_congr rfl fun h _ ↦ ?_
  rw [← det_transpose]
  refine congrArg (· ^ _) (congrArg det (Matrix.ext fun s t ↦ ?_))
  simp [squarePart, mul_apply, mul_comm]

/-- Let `v` be the Gram matrix `weylGramOver` times the evaluation vector at the permutation array
of `rowEquivFin`. Let the integral matrix `B` be equivariant for the block group, and let the row
vector `v ᵥ* B` be the coordinates of `c • branchVector ℂ ι γ κ'` in the basis of products of
minors. Then `B` is `c` times the contraction followed by the projection to the Weyl module, in the
following sense. Up to a power of the determinant, the Gram pairing of the evaluation vector at `y`
with `B ξ` is `c` times the pairing of the extended tensor of `y` with the tensor
`fillingMatrixOver ℂ N (γ + κ') *ᵥ ξ` of `ξ`, a vector indexed by column fillings. -/
lemma det_mul_dotProduct_mulVec_eq_extendedTensor {c : ℤ}
    {B : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily N (γ + κ')) ℤ}
    (B_top : nablaCombination (γ + κ') ((weylGramOver *ᵥ weylEval n κ₀
        (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) ᵥ*
          B.map (Int.cast : ℤ → ℂ)) =
      (c : ℂ) • branchVector ℂ ι γ κ')
    (B_block : ∀ g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ,
      B.map (Int.cast : ℤ → ℂ) * schur (γ + κ') (blockScalar ι g 1) =
        (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (schur κ₀ g * B.map (Int.cast : ℤ → ℂ)))
    (ξ : WeylIndexFamily N (γ + κ') → ℂ) (y : (Σ τ : Φ, n τ) × ℕ → ℂ) :
    (∏ τ : Φ, (squarePart (rowEquivFin n) y τ).det ^ κ' τ (rankAt n τ)) *
        (weylEval n κ₀ y ⬝ᵥ weylGramOver *ᵥ B.map (Int.cast : ℤ → ℂ) *ᵥ ξ) =
      c * (extendedTensor ι γ κ' (fun τ : Φ ↦ (squarePart (rowEquivFin n) y τ)ᵀ) ⬝ᵥ
        fillingMatrixOver ℂ N (γ + κ') *ᵥ ξ) := by
  -- Move the value on the extremal vector to the array `y` by the action of `diag(yᵀ, 1)`.
  let rows (τ : Φ) : Matrix (n τ) (n τ) ℂ := (squarePart (rowEquivFin n) y τ)ᵀ
  let G₀ : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily n κ₀) ℂ := weylGramOver
  let T : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily N (γ + κ')) ℂ := B.map (↑)
  let E : Matrix (ColumnFilling N (γ + κ')) (WeylIndexFamily N (γ + κ')) ℂ :=
    fillingMatrixOver ℂ N (γ + κ')
  let top : WeylIndexFamily n κ₀ → ℂ := weylEval n κ₀ (permArray fun τ i ↦ rowEquivFin n τ i)
  have h_subst : (G₀ *ᵥ top) ᵥ* T ᵥ* schur (γ + κ') (blockScalar ι rows 1) =
      (c : ℂ) • Eᵀ *ᵥ extendedTensor ι γ κ' rows := by
    refine (vecMul_schur_eq_iff FitsRanks.refl _).2 ?_
    rw [B_top, map_smul, map_smul, branchVector_eq_prod_tableauPoly, rowSubst_prod_tableauPoly,
      nablaCombination_transpose_mulVec]
    simp [extendedTensor]
  have h_adjoint : (G₀ *ᵥ top) ᵥ* schur κ₀ rows = weylEval n κ₀ y ᵥ* G₀ := by
    have h_symm : G₀ᵀ = G₀ := by rw [← transpose_map, weylGram_isSymm.eq]
    rw [← mulVec_transpose, mulVec_mulVec,
      ← weylGramOver_mul_schur (g := squarePart (rowEquivFin n) y),
      ← mulVec_mulVec, schur_squarePart_mulVec, ← mulVec_transpose, h_symm]
  calc
    _ = ((∏ τ : Φ, (rows τ).det ^ κ' τ (rankAt n τ)) • (G₀ *ᵥ top) ᵥ* schur κ₀ rows ᵥ* T) ⬝ᵥ ξ := by
      simp only [rows, det_transpose, h_adjoint, smul_dotProduct, dotProduct_mulVec, smul_eq_mul,
        G₀, T]
    _ = ((G₀ *ᵥ top) ᵥ* T ᵥ* schur (γ + κ') (blockScalar ι rows 1)) ⬝ᵥ ξ := by
      rw [vecMul_vecMul, vecMul_vecMul, B_block, vecMul_smul]
    _ = c * (extendedTensor ι γ κ' rows ⬝ᵥ E *ᵥ ξ) := by
      rw [h_subst, smul_dotProduct, mulVec_transpose, dotProduct_mulVec, smul_eq_mul]

/-- The evaluation vectors at the arrays whose square parts have `∏ τ, det ^ d τ ≠ 0` span the
Weyl module. -/
lemma span_weylEval_eq_top (d : Φ → ℕ) :
    Submodule.span ℂ (Set.range fun y : {y : (Σ τ : Φ, n τ) × ℕ → ℂ //
      ∏ τ : Φ, (squarePart (rowEquivFin n) y τ).det ^ d τ ≠ 0} ↦ weylEval n κ₀ y.val) = ⊤ := by
  -- A linear form that kills these vectors vanishes.
  rw [← Submodule.dualAnnihilator_eq_bot_iff, Submodule.eq_bot_iff]
  intro F hF
  refine ext_weylEval (L' := 0) (s := Set.univ) d (fun y _ h_det ↦ ?_) Set.infinite_univ
  have h_eval : eval y (detPow ℂ n d) = ∏ τ : Φ, (squarePart (rowEquivFin n) y τ).det ^ d τ := by
    simp only [← det_submatrix_equiv_self (rowEquivFin n _).symm (squarePart (rowEquivFin n) y _)]
    simp [detPow, minor, squarePart, RingHom.map_det, Matrix.map, submatrix]
  exact (Submodule.mem_dualAnnihilator F).1 hF _
    (Submodule.subset_span ⟨⟨y, by rwa [← h_eval]⟩, rfl⟩)

omit [DecidableEq Φ] [∀ τ : Φ, DecidableEq (N τ)] [∀ τ : Φ, DecidableEq (n τ)] in
/-- Complex conjugation commutes with passing to the extended tensor. -/
lemma star_extendedTensor (a : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ) :
    star (extendedTensor ι γ κ' a) =
      extendedTensor ι γ κ' fun τ : Φ ↦ (a τ).map (starRingEnd ℂ) := by
  have h_block (τ : Φ) : (blockScalar ι a 1 τ).map (starRingEnd ℂ) =
      blockScalar ι (fun σ : Φ ↦ (a σ).map (starRingEnd ℂ)) 1 τ := by
    simp [blockScalar, ← submatrix_map, fromBlocks_map]
  ext T
  simp only [Pi.star_apply, ← starRingEnd_apply, extendedTensor, map_prod, RingHom.map_det,
    RingHom.mapMatrix_apply, ← submatrix_map, h_block]

/-- Let the vectors `m y` have the same Hermitian pairings for the standard form as the vectors
`v y` have for the form `G`, and let `η` lie in the span of the `v y`. If `η` pairs with each `v y`
as `u` pairs with `m y`, so that `η` corresponds to the orthogonal projection of `u` to the span of
the `m y`, then the squared norm of `η` is at most that of `u`. -/
lemma re_dotProduct_mulVec_le_of_forall_dotProduct_eq {I J Y : Type} [Fintype I] [Fintype J]
    {G : Matrix I I ℂ} {v : Y → I → ℂ} {m : Y → J → ℂ} {η : I → ℂ} {u : J → ℂ}
    (h_isometry : ∀ y z : Y, star (v y) ⬝ᵥ G *ᵥ v z = star (m y) ⬝ᵥ m z)
    (h_span : η ∈ Submodule.span ℂ (Set.range v))
    (h_pairing : ∀ y : Y, star (v y) ⬝ᵥ G *ᵥ η = star (m y) ⬝ᵥ u) :
    (star η ⬝ᵥ G *ᵥ η).re ≤ (star u ⬝ᵥ u).re := by
  classical
  -- Write `η = ∑ a y • v y` and put `M = ∑ a y • m y`. Then `‖η‖² = ‖M‖² = ⟪M, u⟫`.
  obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h_span
  let M : J → ℂ := a.sum fun (y : Y) (t : ℂ) ↦ t • m y
  have h_left {ζ : I → ℂ} {w : J → ℂ} (h : ∀ y : Y, star (v y) ⬝ᵥ G *ᵥ ζ = star (m y) ⬝ᵥ w) :
      star η ⬝ᵥ G *ᵥ ζ = star M ⬝ᵥ w := by
    simp only [← ha, M, Finsupp.sum, star_sum, star_smul, sum_dotProduct, smul_dotProduct, h]
  have h_norm : star η ⬝ᵥ G *ᵥ η = star M ⬝ᵥ M := h_left fun y : Y ↦ by
    simp only [← ha, M, Finsupp.sum, mulVec_sum, mulVec_smul, dotProduct_sum, dotProduct_smul,
      h_isometry]
  have h_cauchy : ‖star M ⬝ᵥ u‖ ^ 2 ≤ (star u ⬝ᵥ u).re * (star M ⬝ᵥ M).re := by
    simpa using posDef_cauchy_schwarz PosDef.one M u
  have h_re : (star M ⬝ᵥ M).re ≤ ‖star M ⬝ᵥ u‖ := by
    rw [← h_left h_pairing, h_norm]
    exact Complex.re_le_norm _
  have hu_nonneg : 0 ≤ (star u ⬝ᵥ u).re := (dotProduct_star_self_nonneg u).1
  rw [h_norm]
  nlinarith

/-- Let `κ₀ τ h = κ' τ h + γ τ (h + 1)` for `0 < h < rankAt n τ`, and let `B` be an integral matrix.
Assume `B * schur (γ + κ') (diag(g, 1)) = (∏ τ, det (g τ) ^ κ' τ (rankAt n τ)) • (schur κ₀ g * B)`
for all complex `g`, with `diag(g, 1)` built by `blockScalar ι`. Let `v` be the Gram matrix
`weylGramOver` times `weylEval` at the permutation array of `rowEquivFin`, and assume also that the
row vector `v ᵥ* B` has the polynomial `c • branchVector ℂ ι γ κ'` under `nablaCombination`
(ξ ↦ Σ ξ_i b_i over the basis products of minors). Then
`weylNormSq (B *ᵥ ξ) ≤ c ^ 2 * weylNormSq ξ` for every complex vector `ξ`. -/
lemma weylNormSq_mulVec_le_of_equivariant {c : ℤ}
    (hκ₀ : ∀ τ : Φ, ∀ h ∈ Ioo 0 (rankAt n τ), κ₀ τ h = κ' τ h + γ τ (h + 1))
    {B : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily N (γ + κ')) ℤ}
    (B_top : nablaCombination (γ + κ') ((weylGramOver *ᵥ weylEval n κ₀
        (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) ᵥ*
          B.map (Int.cast : ℤ → ℂ)) =
      (c : ℂ) • branchVector ℂ ι γ κ')
    (B_block : ∀ g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ,
      B.map (Int.cast : ℤ → ℂ) * schur (γ + κ') (blockScalar ι g 1) =
        (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (schur κ₀ g * B.map (Int.cast : ℤ → ℂ)))
    (ξ : WeylIndexFamily N (γ + κ') → ℂ) :
    weylNormSq (B.map (Int.cast : ℤ → ℂ) *ᵥ ξ) ≤ (c : ℝ) ^ 2 * weylNormSq ξ := by
  -- On the evaluation vectors `weylEval n κ₀ y` with `d y ≠ 0`, which span, the transposed
  -- contraction `weylEval n κ₀ y ↦ m y` is an isometry, and `B ξ` pairs with `weylEval n κ₀ y` as
  -- `c` times the tensor `E ξ` pairs with `m y`.
  let E : Matrix (ColumnFilling N (γ + κ')) (WeylIndexFamily N (γ + κ')) ℂ :=
    fillingMatrixOver ℂ N (γ + κ')
  let d (y : Sigma n × ℕ → ℂ) : ℂ := ∏ τ, (squarePart (rowEquivFin n) y τ).det ^ κ' τ (rankAt n τ)
  let m (y : Sigma n × ℕ → ℂ) : ColumnFilling N (γ + κ') → ℂ :=
    (d y)⁻¹ • extendedTensor ι γ κ' fun τ : Φ ↦ (squarePart (rowEquivFin n) y τ)ᵀ
  have star_d (y : Sigma n × ℕ → ℂ) : star (d y) = d (star y) := by
    simp only [d, ← starRingEnd_apply, map_prod, map_pow, RingHom.map_det]
    rfl
  have star_m (y : Sigma n × ℕ → ℂ) : star (m y) = m (star y) := by
    simp only [m, star_smul, star_inv₀, star_d, star_extendedTensor]
    rfl
  have h_isometry (y z : Sigma n × ℕ → ℂ) (hy : d y ≠ 0) (hz : d z ≠ 0) :
      weylEval n κ₀ y ⬝ᵥ weylGramOver *ᵥ weylEval n κ₀ z = m y ⬝ᵥ m z := by
    have h_det : ∏ τ : Φ, ((squarePart (rowEquivFin n) y τ)ᵀ * squarePart (rowEquivFin n) z τ).det ^
        κ' τ (rankAt n τ) = d y * d z := by
      simp only [d, det_mul, det_transpose, mul_pow, Finset.prod_mul_distrib]
    simp only [m, smul_dotProduct, dotProduct_smul, smul_eq_mul, extendedTensor_dotProduct ι hκ₀,
      transpose_transpose, Finset.prod_mul_distrib, h_det,
      weylEval_dotProduct_weylGram_mulVec_weylEval]
    field_simp
  have h_pairing (y : Sigma n × ℕ → ℂ) (hy : d y ≠ 0) :
      weylEval n κ₀ y ⬝ᵥ weylGramOver *ᵥ B.map (↑) *ᵥ ξ = m y ⬝ᵥ (c : ℂ) • E *ᵥ ξ := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← det_mul_dotProduct_mulVec_eq_extendedTensor ι B_top B_block ξ y, inv_mul_cancel_left₀ hy]
  have h_star_ne {y : Sigma n × ℕ → ℂ} (hy : d y ≠ 0) : d (star y) ≠ 0 := by simpa [← star_d]
  have h_tensor : star (E *ᵥ ξ) ⬝ᵥ E *ᵥ ξ = weylNormSq ξ := by
    have h_real : Eᴴ = Eᵀ := Matrix.ext fun i T ↦ by simp [E]
    rw [coe_weylNormSq, weylGramOver_eq_transpose_mul, star_mulVec, ← dotProduct_mulVec, h_real,
      mulVec_mulVec]
  calc weylNormSq (B.map (↑) *ᵥ ξ)
    _ ≤ (star ((c : ℂ) • E *ᵥ ξ) ⬝ᵥ (c : ℂ) • E *ᵥ ξ).re := by
      refine re_dotProduct_mulVec_le_of_forall_dotProduct_eq (m := fun y : {y // d y ≠ 0} ↦ m y)
        (fun y z ↦ ?_) ((span_weylEval_eq_top _).ge Submodule.mem_top) fun y ↦ ?_
      · rw [star_weylEval, star_m, h_isometry _ _ (h_star_ne y.property) z.property]
      · rw [star_weylEval, star_m, h_pairing _ (h_star_ne y.property)]
    _ = (c : ℝ) ^ 2 * weylNormSq ξ := by
      simp [h_tensor, ← mul_assoc, sq]

end New.GL

end Contraction

end
