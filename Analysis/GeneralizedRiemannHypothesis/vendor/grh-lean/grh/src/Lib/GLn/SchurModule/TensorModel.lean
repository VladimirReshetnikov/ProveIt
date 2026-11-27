import Lib.GLn.SchurModule.SchurMatrix
import Lib.General.LinearAlgebra.MinorProducts

/-!
# The Weyl module inside the tensors of its diagram

A tensor in the product of exterior powers, one factor for each column of the diagram, is written as
a function on the column fillings `New.ColumnFilling`, which index the basis tensors.

* `New.fillingMatrix`: the integral matrix that embeds the Weyl module into tensors. Its row at a
  column filling holds the coordinates, in the standard basis, of the product of minors
  `New.fillingPoly` of that filling.
* `New.fillingMatrixOver_mul_schur`: the Schur matrix of a family of square matrices, one for each
  place `τ`, is the restriction of their action `New.minorsMatrix` on tensors.
* `New.span_fillingPoly`: the products of minors span the module of Borel semi-invariants, whose
  dual is the Weyl module.
* `New.exists_fillingMatrix_leftInverse`: the Weyl module is a direct summand of the integral
  tensors.
* `New.exists_fillingMatrix_mulVec_eq_iff_mem_span`: the Weyl module over `ℤ` consists of the
  integral tensors in the span over `ℚ` of the tensors of rational matrices.

Notions from other files:
* A `Tableau` lists the entries of each column; `tableauPoly R e T` is the product, over the columns
  of the tableau `T`, of the `minor` whose rows are the images under `e` of the entries. Here
  `minor R I` is the determinant of the variables `y` in the rows `I` and the first columns;
  `MatrixPoly ι R` is the ring of polynomials in these variables `y`, indexed by `ι × ℕ` (a row and
  a column number).
* `nablaBasis R n κ`, the standard basis, is a chosen basis of products of minors of the module
  `nablaFamily R n κ`, indexed by `WeylIndexFamily n κ`; `nablaCombination κ` takes a coordinate
  vector to its combination of this basis. A vector of the Weyl module is given by its coordinates
  `WeylIndexFamily n κ → R` in the dual basis.
* `rowSubst z` substitutes `z y` for `y`, and row `i` of `schur κ z` holds the coordinates of
  `rowSubst z` of the basis element `i`; so `schur κ z` acts on the Weyl module.

## Relation to the literature

Known result: the Weyl module over `ℤ` as a direct summand as a ℤ-module of a tensor product of
exterior powers. Source: Akin, Buchsbaum and Weyman, Schur functors and Schur complexes.
-/

noncomputable section

open MvPolynomial Finset Matrix Fintype Function New «GL»

namespace New

section Tensors

variable {Φ R : Type} [CommRing R] {n : Φ → Type} [∀ τ : Φ, Fintype (n τ)] {κ : Φ → ℕ → ℕ}

/-- The strictly increasing sequences of length `h` in `Fin N`. -/
abbrev IncreasingMap (N h : ℕ) : Type := {f : Fin h → Fin N // StrictMono f}

/-- The Cauchy–Binet formula as a sum over increasing sequences: the determinant of the product of
an `h × N` and an `N × h` matrix is the sum, over the increasing sequences `I` of length `h`, of
the products of the two minors at `I`. -/
lemma det_mul_eq_sum_increasing {N h : ℕ}
    (A : Matrix (Fin h) (Fin N) R) (B : Matrix (Fin N) (Fin h) R) :
    (A * B).det =
      ∑ I : IncreasingMap N h, (A.submatrix id I.val).det * (B.submatrix I.val id).det := by
  -- A set `S` of `h` indices is the same as its increasing enumeration `enumSubset S`.
  let enum (S : Set.powersetCard (Fin N) h) : IncreasingMap N h :=
    ⟨enumSubset S, (Set.powersetCard.ofFinEmbEquiv.symm S).strictMono⟩
  have h_bij : Function.Bijective enum :=
    ⟨fun S S' h_eq ↦ Set.powersetCard.ofFinEmbEquiv.symm.injective
        (DFunLike.coe_injective (congrArg Subtype.val h_eq)),
      fun ⟨f, hf⟩ ↦ ⟨Set.powersetCard.ofFinEmbEquiv (.ofStrictMono f hf),
        by simp [enum, enumSubset]⟩⟩
  rw [det_mul_eq_sum_minors]
  exact Fintype.sum_bijective enum h_bij _ _ fun _ ↦ mul_comm _ _

/-- For an `h` by `n τ` matrix `c`, the determinant of `c y`, where `y` consists of the first `h`
columns of the variables at the place `τ`, is the sum over increasing row numbers `I` of the minor
of `c` with columns `I` times the minor of `y` with rows `I`. Here `rankAt n τ` is the number of
elements of `n τ`, and the row numbers are read as elements of `n τ` through their numbering
`rowEquivFin n τ`. -/
lemma det_sum_smul_X (τ : Φ) {h : ℕ} (c : Matrix (Fin h) (n τ) R) :
    (of fun s t : Fin h ↦ ∑ a : n τ, c s a • X (R := R) ((⟨τ, a⟩ : Σ τ : Φ, n τ), (t : ℕ))).det =
      ∑ I : IncreasingMap (rankAt n τ) h, (c.submatrix id ((rowEquivFin n τ).symm ∘ I.val)).det •
        minor R (Sigma.mk τ ∘ (rowEquivFin n τ).symm ∘ I.val) := by
  have hproduct : (of fun s t : Fin h ↦
      ∑ a : n τ, c s a • X (R := R) ((⟨τ, a⟩ : Σ τ, n τ), (t : ℕ))) =
        ((c.submatrix id (rowEquivFin n τ).symm).map C :
            Matrix (Fin h) (Fin (rankAt n τ)) (MatrixPoly (Σ τ : Φ, n τ) R)) *
          of fun (a : Fin (rankAt n τ)) (t : Fin h) ↦
            X (R := R) ((⟨τ, (rowEquivFin n τ).symm a⟩ : Σ τ, n τ), (t : ℕ)) := by
    ext s t : 1
    simp only [mul_apply, map_apply, submatrix_apply, of_apply, id_eq, smul_eq_C_mul]
    exact (Equiv.sum_comp (rowEquivFin n τ).symm _).symm
  rw [hproduct, det_mul_eq_sum_increasing]
  -- Both sides are products of the same minors, by the definition of the matrix of variables.
  exact Finset.sum_congr rfl fun I _ ↦ by
    simp [smul_eq_C_mul, RingHom.map_det, minor, Matrix.submatrix, Matrix.map,
      Function.comp_def]

variable (n κ) in
/-- The index set of the basis tensors for the diagram with `κ τ h` columns of height `h` at `τ`,
for the heights below the rank `rankAt n τ`, the number of elements of `n τ`: an increasing sequence
of `h` row numbers for each column. -/
abbrev ColumnFilling : Type :=
  ∀ (τ : Φ) (h : Fin (rankAt n τ)), Fin (κ τ h) → IncreasingMap (rankAt n τ) h

/-- The tableau of a column filling at `τ`, with row numbers read as rows through `rowEquivFin n τ`,
the numbering of `n τ` by `Fin (rankAt n τ)`. -/
def fillingRows (T : ColumnFilling n κ) (τ : Φ) : Tableau (n τ) (rankAt n τ) (κ τ) :=
  fun (h : Fin (rankAt n τ)) (j : Fin (κ τ h)) (s : Fin h) ↦ (rowEquivFin n τ).symm ((T τ h j).1 s)

variable [Fintype Φ]

variable (R) in
/-- The product of the minors of the variables on the columns of a filling: a column of height `h`
gives the minor with the rows of its entries and the first `h` columns of variables. -/
def fillingPoly (T : ColumnFilling n κ) : MatrixPoly (Σ τ : Φ, n τ) R :=
  ∏ τ : Φ, tableauPoly R (Sigma.mk τ) (fillingRows T τ)

variable (κ) in
/-- The matrix by which `z` acts on tensors: the entry at `(T, T')` is the product, over the
columns of the diagram, of the minor of `z τ` with rows from `T` and columns from `T'`, where `τ`
is the place of the column. -/
def minorsMatrix (z : ∀ τ : Φ, Matrix (n τ) (n τ) R) :
    Matrix (ColumnFilling n κ) (ColumnFilling n κ) R :=
  of fun T T' : ColumnFilling n κ ↦ ∏ τ : Φ, ∏ h : Fin (rankAt n τ), ∏ j : Fin (κ τ h),
    ((z τ).submatrix (fillingRows T τ h j) (fillingRows T' τ h j)).det

end Tensors

section Action

variable {Φ R : Type} [CommRing R] {n : Φ → Type} [∀ τ : Φ, Fintype (n τ)] {κ : Φ → ℕ → ℕ}
  [Fintype Φ]

/-- The action `minorsMatrix` of transposed matrices on tensors is the transpose of the action. -/
lemma minorsMatrix_transpose (z : ∀ τ : Φ, Matrix (n τ) (n τ) R) :
    minorsMatrix κ (fun τ : Φ ↦ (z τ)ᵀ) = (minorsMatrix κ z)ᵀ := by
  ext T T'
  simp only [minorsMatrix, of_apply, transpose_apply, ← transpose_submatrix, det_transpose]

variable [DecidableEq Φ]

omit [DecidableEq Φ] [Fintype Φ] in
/-- Substituting `z y` for the variables `y` in the minor with rows `J` at the place `τ` gives the
sum, over increasing row numbers `I`, of the minor of `z τ` with rows `J` and columns `I` times the
minor of `y` with rows `I`. -/
lemma rowSubst_minor_comp_sigmaMk (z : ∀ τ : Φ, Matrix (n τ) (n τ) R) (τ : Φ) {h : ℕ}
    (J : Fin h → n τ) :
    rowSubst z (minor R (Sigma.mk τ ∘ J)) = ∑ I : IncreasingMap (rankAt n τ) h,
      ((z τ).submatrix J ((rowEquivFin n τ).symm ∘ I.val)).det •
        minor R (Sigma.mk τ ∘ (rowEquivFin n τ).symm ∘ I.val) := by
  refine Eq.trans ?_ (det_sum_smul_X τ ((z τ).submatrix J id))
  simp [minor, AlgHom.map_det, rowSubst, Matrix.map]

/-- For a family of tableaux `U`, substituting `z y` for the variables `y` in the product of the
minors on the columns of `U` gives the sum over column fillings `T` of the product of minors
`fillingPoly` of `T`, times the product over the columns of the minor of `z τ` with rows from `U`
and columns from `T`, where `τ` is the place of the column. -/
lemma rowSubst_prod_tableauPoly (z : ∀ τ : Φ, Matrix (n τ) (n τ) R)
    (U : ∀ τ : Φ, Tableau (n τ) (rankAt n τ) (κ τ)) :
    rowSubst z (∏ τ : Φ, tableauPoly R (Sigma.mk τ) (U τ)) =
      ∑ T : ColumnFilling n κ, (∏ τ : Φ, ∏ h : Fin (rankAt n τ), ∏ j : Fin (κ τ h),
        ((z τ).submatrix (U τ h j) (fillingRows T τ h j)).det) • fillingPoly R T := by
  simp only [fillingPoly, tableauPoly, map_prod, rowSubst_minor_comp_sigmaMk, Fintype.prod_sum,
    Finset.prod_smul]
  -- The rows of the column filling are `fillingRows T` by definition.
  rfl

/-- Substituting `z y` for `y` in the product of minors `fillingPoly` of a column filling `T` gives
the combination of these products with row `T` of the matrix `minorsMatrix` as coefficients. -/
lemma rowSubst_fillingPoly (z : ∀ τ : Φ, Matrix (n τ) (n τ) R) (T : ColumnFilling n κ) :
    rowSubst z (fillingPoly R T) =
      ∑ T' : ColumnFilling n κ, minorsMatrix κ z T T' • fillingPoly R T' :=
  rowSubst_prod_tableauPoly z (fillingRows T)

end Action

section Embedding

variable {Φ R : Type} [CommRing R] {n : Φ → Type} [∀ τ : Φ, Fintype (n τ)] {κ : Φ → ℕ → ℕ}
  [Fintype Φ] [DecidableEq Φ] [∀ τ : Φ, DecidableEq (n τ)]

variable (n κ) in
/-- The integral matrix of the embedding of the Weyl module into tensors: row `T` holds the
coordinates, in the standard basis, of the product of minors of `T`. -/
def fillingMatrix : Matrix (ColumnFilling n κ) (WeylIndexFamily n κ) ℤ :=
  of fun T : ColumnFilling n κ ↦ invFun (nablaCombination (R := ℤ) κ) (fillingPoly ℤ T)

variable (R n κ) in
/-- The matrix `fillingMatrix` with its entries mapped into `R`. -/
abbrev fillingMatrixOver : Matrix (ColumnFilling n κ) (WeylIndexFamily n κ) R :=
  (fillingMatrix n κ).map (Int.cast : ℤ → R)

lemma fillingMatrixOver_int : fillingMatrixOver ℤ n κ = fillingMatrix n κ := by
  ext T i
  simp

/-- For a column filling `T` (an increasing sequence of rows in each column of the diagram `κ`), the
row `T` of the embedding `fillingMatrixOver` of the Weyl module into tensors is the coordinate
vector of the product of minors `fillingPoly R T`: the map `nablaCombination`, which takes
coordinates to the combination of the standard basis of products of minors, sends it to that
product. -/
lemma nablaCombination_fillingMatrixOver (T : ColumnFilling n κ) :
    nablaCombination κ (fillingMatrixOver R n κ T : WeylIndexFamily n κ → R) = fillingPoly R T := by
  -- By definition, row `T` of `fillingMatrix` holds coordinates of `fillingPoly ℤ T`.
  have hZ : ∑ i : WeylIndexFamily n κ, fillingMatrix n κ T i • nablaBasis ℤ n κ i =
      fillingPoly ℤ T :=
    sum_coords_nablaBasis (prod_tableauPoly_mem_nabla (T := fillingRows T))
  have hmap : MvPolynomial.map (Int.castRingHom R) (fillingPoly ℤ T) = fillingPoly R T := by
    simp [fillingPoly, tableauPoly, minor, RingHom.map_det, Matrix.map]
  -- Apply the change of rings from `ℤ` to `R` to the expansion over `ℤ`.
  simp [← hmap, ← hZ, Fintype.linearCombination_apply, smul_eq_C_mul]

/-- The embedding `fillingMatrixOver` of the Weyl module into tensors sends the vector `weylEval`,
of the values at `y` of the standard basis of products of minors, to the vector whose coordinate at
a column filling `T` is the value at `y` of the product of minors `fillingPoly R T`. -/
lemma fillingMatrixOver_mulVec_weylEval (y : (Σ τ : Φ, n τ) × ℕ → R) (T : ColumnFilling n κ) :
    (fillingMatrixOver R n κ *ᵥ weylEval n κ y) T = eval y (fillingPoly R T) := by
  simp [← nablaCombination_fillingMatrixOver T, Fintype.linearCombination_apply, mulVec, dotProduct,
    weylEval]

/-- For a tensor `v`, given by its values on column fillings, the transposed embedding
`(fillingMatrixOver R n κ)ᵀ` takes `v` to the coordinates of the combination with coefficients `v`
of the products of minors `fillingPoly`. Here `nablaCombination` takes coordinates to the
combination of the standard basis of products of minors. -/
lemma nablaCombination_transpose_mulVec (v : ColumnFilling n κ → R) :
    nablaCombination κ ((fillingMatrixOver R n κ)ᵀ *ᵥ v) =
      ∑ T : ColumnFilling n κ, v T • fillingPoly R T := by
  -- The transposed matrix sends `v` to the combination of the rows with coefficients `v`.
  simp only [mulVec_transpose, vecMul_eq_sum, map_sum, map_smul, nablaCombination_fillingMatrixOver]

/-- For a family `z` of square matrices, `nablaCombination`, which takes coordinates to the
combination of the standard basis, sends row `i` of the Schur matrix `schur κ z` to the basis
polynomial `nablaBasis R n κ i` with `z y` substituted for the variables `y`. -/
lemma nablaCombination_schur_row (z : ∀ τ : Φ, Matrix (n τ) (n τ) R) (i : WeylIndexFamily n κ) :
    nablaCombination κ (schur κ z i) = rowSubst z (nablaBasis R n κ i) := by
  -- For equal ranks no power of a determinant occurs in the expansion.
  simp [← sum_schur_smul_nablaBasis FitsRanks.refl z i, Fintype.linearCombination_apply, detPow]

/-- For a family `z` of square matrices, the embedding `fillingMatrixOver` of the Weyl module into
tensors intertwines the Schur matrix `schur κ z`, the action of `z` on the Weyl module, with
`minorsMatrix κ z`, the action of `z` on tensors by products of minors. -/
lemma fillingMatrixOver_mul_schur (z : ∀ τ : Φ, Matrix (n τ) (n τ) R) :
    fillingMatrixOver R n κ * schur κ z = minorsMatrix κ z * fillingMatrixOver R n κ := by
  refine funext fun T : ColumnFilling n κ ↦ ?_
  -- Both rows are compared as combinations of the standard basis, which is independent.
  apply nablaCombination_injective
  calc nablaCombination κ ((fillingMatrixOver R n κ * schur κ z) T)
      = rowSubst z (nablaCombination κ (fillingMatrixOver R n κ T)) := by
        simp [mul_apply_eq_vecMul, vecMul_eq_sum,
          Fintype.linearCombination_apply]
    _ = nablaCombination κ ((minorsMatrix κ z * fillingMatrixOver R n κ) T) := by
        simp [nablaCombination_fillingMatrixOver, rowSubst_fillingPoly, mul_apply_eq_vecMul,
          vecMul_eq_sum]

variable (R n κ) in
/-- The module `nablaFamily R n κ` of Borel semi-invariants is the span of the products of minors
`fillingPoly R T` over all column fillings `T`, the coordinates of the tensor of the variables. -/
lemma span_fillingPoly :
    Submodule.span R (Set.range fun T : ColumnFilling n κ ↦ fillingPoly R T) =
      nablaFamily R n κ := by
  apply le_antisymm
  · exact Submodule.span_le.2 <| Set.range_subset_iff.2 fun T ↦
      prod_tableauPoly_mem_nabla (T := fillingRows T)
  · rw [← range_nablaCombination, Fintype.range_linearCombination, Submodule.span_le,
      Set.range_subset_iff]
    intro i
    -- Substituting the identity matrices into a basis element, a product of minors with rows in
    -- any order, expands it in the products with increasing rows.
    have h_expand : nablaBasis R n κ i =
        ∑ T : ColumnFilling n κ, (∏ τ : Φ, ∏ h : Fin (rankAt n τ), ∏ j : Fin (κ τ h),
          ((1 : Matrix (n τ) (n τ) R).submatrix ((i τ).val h j) (fillingRows T τ h j)).det) •
            fillingPoly R T :=
      (rowSubst_one _).symm.trans (rowSubst_prod_tableauPoly (fun _ ↦ 1) fun τ : Φ ↦ (i τ).val)
    rw [h_expand]
    exact Submodule.sum_mem _ fun T _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨T, rfl⟩)

/-- The integral matrix `fillingMatrix`, which embeds the Weyl module of the diagram `κ` (with basis
indexed by `WeylIndexFamily n κ`) into tensors (with basis indexed by column fillings), has an
integral left inverse. So the Weyl module is a direct summand of the integral tensors. -/
lemma exists_fillingMatrix_leftInverse :
    ∃ Q : Matrix (WeylIndexFamily n κ) (ColumnFilling n κ) ℤ, Q * fillingMatrix n κ = 1 := by
  -- The map from tensors onto the span of the products of minors splits, as its target is free:
  -- choose a tensor `v i` over each basis element.
  have h_onto (i : WeylIndexFamily n κ) : ∃ v : ColumnFilling n κ → ℤ,
      ∑ T : ColumnFilling n κ, v T • fillingPoly ℤ T = nablaBasis ℤ n κ i := by
    rw [← Submodule.mem_span_range_iff_exists_fun, span_fillingPoly, nablaBasis]
    exact prod_tableauPoly_mem_nabla
  choose v hv using h_onto
  refine ⟨of v, funext fun i : WeylIndexFamily n κ ↦ ?_⟩
  apply nablaCombination_injective
  have h_row : (of v * fillingMatrix n κ) i = (fillingMatrixOver ℤ n κ)ᵀ *ᵥ v i := by
    rw [fillingMatrixOver_int, mulVec_transpose, mul_apply_eq_vecMul]
    rfl
  rw [h_row, nablaCombination_transpose_mulVec, hv]
  simp [one_apply, Fintype.linearCombination_apply]

variable (n κ) in
/-- Over an infinite field `K`, the image of the Weyl module in tensors under `fillingMatrixOver`
is the span of the tensors of the arrays `y` over `K`. The coordinate of the tensor of `y` at a
column filling `T` is the value at `y` of the product of minors `fillingPoly K T`. -/
lemma range_fillingMatrixOver_eq_span (K : Type) [Field K] [Infinite K] :
    LinearMap.range (fillingMatrixOver K n κ).mulVecLin =
      Submodule.span K (Set.range fun (y : (Σ τ : Φ, n τ) × ℕ → K) (T : ColumnFilling n κ) ↦
        eval y (fillingPoly K T)) := by
  apply le_antisymm
  · -- A tensor `c` orthogonal to the tensors of all arrays gives the zero combination of products
    -- of minors, so it is orthogonal to the image.
    rintro _ ⟨ξ, rfl⟩
    refine (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ _).mp fun φ hφ ↦ ?_
    obtain ⟨c, rfl⟩ := (dotProductEquiv K (ColumnFilling n κ)).surjective φ
    have h_poly : ∑ T : ColumnFilling n κ, c T • fillingPoly K T = 0 :=
      MvPolynomial.funext fun y ↦ by
        simpa [dotProduct, smul_eval] using
          (Submodule.mem_dualAnnihilator _).mp hφ _ (Submodule.subset_span ⟨y, rfl⟩)
    have h_ker : (fillingMatrixOver K n κ)ᵀ *ᵥ c = 0 :=
      nablaCombination_injective (by simp [nablaCombination_transpose_mulVec, h_poly])
    simp [dotProduct_mulVec, ← mulVec_transpose, h_ker]
  · rw [Submodule.span_le, Set.range_subset_iff]
    exact fun y ↦ ⟨weylEval n κ y, funext (fillingMatrixOver_mulVec_weylEval y)⟩

/-- The Weyl lattice inside the tensors. An integral tensor `v` is the image of an integral vector
of the Weyl module under the embedding `fillingMatrix` if and only if it lies in the span over `ℚ`
of the tensors of rational arrays `y`, whose coordinates are the values at `y` of the products of
minors `fillingPoly`. -/
lemma exists_fillingMatrix_mulVec_eq_iff_mem_span (v : ColumnFilling n κ → ℤ) :
    (∃ ξ : WeylIndexFamily n κ → ℤ, fillingMatrix n κ *ᵥ ξ = v) ↔
      (fun T : ColumnFilling n κ ↦ (v T : ℚ)) ∈
        Submodule.span ℚ (Set.range fun (y : (Σ τ : Φ, n τ) × ℕ → ℚ) (T : ColumnFilling n κ) ↦
          eval y (fillingPoly ℚ T)) := by
  rw [← range_fillingMatrixOver_eq_span]
  constructor
  · rintro ⟨ξ, rfl⟩
    exact ⟨fun i ↦ ξ i, funext fun T ↦ by simp [mulVec, dotProduct]⟩
  · -- A rational preimage `η` is `Q v` for an integral left inverse `Q`, hence integral.
    rintro ⟨η, hη : fillingMatrixOver ℚ n κ *ᵥ η = _⟩
    obtain ⟨Q, hQ⟩ := exists_fillingMatrix_leftInverse (n := n) (κ := κ)
    have hQ_rat : Q.map (Int.cast : ℤ → ℚ) * fillingMatrixOver ℚ n κ = 1 :=
      (Matrix.map_mul (f := Int.castRingHom ℚ)).symm.trans (by simp [hQ])
    have h_integral : η = fun i : WeylIndexFamily n κ ↦ ((Q *ᵥ v) i : ℚ) := by
      rw [← one_mulVec η, ← hQ_rat, ← mulVec_mulVec, hη]
      simp [funext_iff, mulVec, dotProduct]
    exact ⟨Q *ᵥ v, funext fun T ↦ Int.cast_injective (α := ℚ) <|
      by simp [← congrFun hη T, h_integral, mulVec, dotProduct]⟩

end Embedding

end New
