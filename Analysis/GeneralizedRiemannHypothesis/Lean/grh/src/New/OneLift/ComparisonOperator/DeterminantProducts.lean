import New.OneLift.ComparisonOperator.ExchangeData

/-!
# Products of determinants and first-column coordinates under substitution

This file studies polynomials in the entries of variable matrices `x_τ`, one for each `τ : Φ`, with
rows indexed by `N` and columns by `L`. It studies how these polynomials transform under the
two-sided linear substitutions `New.Rows.twoSidedSubst`, `x_τ ↦ c_τᵀ x_τ g_τᵀ`. It treats products
of determinants of constant matrices stacked over `x_τ`. It also treats the coordinates of a
polynomial in its first `p` columns, where `p` is a number of columns.

## Main definitions and results

* `New.Rows.stackedDetProd`, `New.Rows.twoSidedSubst_stackedDetProd`: a product of determinants of
  constant matrices stacked over `x_τ` (`New.Rows.stackedDet`). The substitution sends the product
  for the matrices `M τ k * (g τ)ᵀ` to a scalar multiple of the product for the matrices `M τ k`.
* `New.Rows.firstColsCoord`, `New.Rows.twoSidedSubst_firstColsCoord`: the coordinates of a
  polynomial in its first `p` columns; if the substitution with column matrices
  `fromBlocks 1 0 0 (g τ)` (fixing the first `p` columns) sends `F'` to a multiple of `F`, the
  coordinates of `F'` and `F` are related by the Schur matrix (`New.schur`).

Notions from other files:
* `New.nablaBasis`, `New.schur`: products of minors indexed by families of standard fillings
  (`New.WeylIndexFamily`), and the matrix of a substitution of rows in these polynomials.
-/

noncomputable section

section StackedDeterminants

open Matrix MvPolynomial Finset Fintype

variable {Φ a L N : Type} [Fintype a] [DecidableEq a] [Fintype N] [DecidableEq N] [Fintype L]
  [DecidableEq L]

/-- Let `Z` be a complex matrix with rows indexed by `L` and columns by `N`, and let `e` identify
`L` with `a ⊕ N`. There are a matrix `Y` and a constant `γ` such that for all `X` the determinant
of the square matrix `(X | Z)`, with columns ordered by `e`, is `γ * det (Y X)ᵀ`. -/
lemma New.exists_det_fromCols_eq_mul_det (e : L ≃ a ⊕ N) (Z : Matrix L N ℂ) :
    ∃ (Y : Matrix a L ℂ) (γ : ℂ), ∀ X : Matrix L a ℂ,
      ((fromCols X Z).submatrix id e).det = γ * (Y * X)ᵀ.det := by
  -- Choose an invertible `(U₁ | U₂)` with `U₁ᴴ Z = 0` and put `Y = U₁ᴴ`. Then `(U₁ | U₂)ᴴ (X | Z)`
  -- is block triangular; compare determinants.
  let colsZ : N ↪ L := Function.Embedding.inr.trans e.symm.toEmbedding
  obtain ⟨V, -, hV⟩ : ∃ V ∈ intGL L (⊤ : Subring ℂ),
      ∀ i : N, ∀ j ∉ Set.range colsZ, (Zᴴ * (V : Matrix L L ℂ)) i j = 0 :=
    isValuationPair_top.exists_mul_clear_cols Zᴴ colsZ
  let U₁ : Matrix L a ℂ := ((V : Matrix L L ℂ).submatrix id e.symm).toCols₁
  let U₂ : Matrix L N ℂ := ((V : Matrix L L ℂ).submatrix id e.symm).toCols₂
  have hV_eq : (fromCols U₁ U₂).submatrix id e = V := by simp [U₁, U₂]
  have hZU : Zᴴ * U₁ = 0 := Matrix.ext fun i j ↦ hV i (e.symm (.inl j)) (by simp [colsZ])
  have hUZ : U₁ᴴ * Z = 0 := conjTranspose_injective (by simpa using hZU)
  refine ⟨U₁ᴴ, (U₂ᴴ * Z).det / star (V : Matrix L L ℂ).det, fun X ↦ ?_⟩
  have h_block : (V : Matrix L L ℂ)ᴴ * (fromCols X Z).submatrix id e =
      (fromBlocks (U₁ᴴ * X) 0 (U₂ᴴ * X) (U₂ᴴ * Z)).submatrix e e := by
    rw [← hV_eq, ← hUZ, ← fromRows_mul_fromCols, ← conjTranspose_fromCols_eq_fromRows_conjTranspose]
    rfl
  have h_det : star (V : Matrix L L ℂ).det * ((fromCols X Z).submatrix id e).det =
      (U₁ᴴ * X).det * (U₂ᴴ * Z).det := by
    simp [← det_conjTranspose, ← det_mul, h_block]
  rw [det_transpose, div_mul_eq_mul_div, eq_div_iff (star_ne_zero.2 V.det_ne_zero)]
  linear_combination h_det

namespace New.Rows

/-- The substitution `x_τ ↦ c_τᵀ x_τ g_τᵀ` on complex polynomials in the entries of `N × L`
matrices `x_τ`. -/
abbrev twoSidedSubst (c : Φ → Matrix N N ℂ) (g : Φ → Matrix L L ℂ) :
    MvPolynomial (Φ × N × L) ℂ →ₐ[ℂ] MvPolynomial (Φ × N × L) ℂ :=
  aeval (R := ℂ) fun ((τ, a, b) : Φ × N × L) ↦
    ∑ i : N, ∑ j : L, (c τ i a * g τ b j) • X (R := ℂ) (τ, i, j)

/-- Rewrites a polynomial in matrix entries `x_{τ,i,j}` as a polynomial in the first `p` columns,
with coefficients polynomials in the entries of the columns indexed by `L`. -/
def inFirstCols {p : ℕ} :
    MvPolynomial (Φ × N × (Fin p ⊕ L)) ℂ →ₐ[ℂ]
      MatrixPoly ((_ : Φ) × N) (MvPolynomial (Φ × N × L) ℂ) :=
  aeval (R := ℂ) fun ((τ, a, b) : Φ × N × (Fin p ⊕ L)) ↦
    Sum.elim (fun i : Fin p ↦ X ⟨⟨τ, a⟩, i.val⟩) (fun l : L ↦ C (X (τ, a, l))) b

/-- The product over `τ` and `k` of the determinants of `M τ k` stacked over the variable matrix
`x_τ` (`New.Rows.stackedDet`), columns ordered by `e`. -/
def stackedDetProd (e : a ⊕ N ≃ L) [Fintype Φ] {ι : Φ → Type} [∀ τ : Φ, Fintype (ι τ)]
    (M : (τ : Φ) → ι τ → Matrix a L ℂ) : MvPolynomial (Φ × N × L) ℂ :=
  ∏ τ : Φ, ∏ k : ι τ, stackedDet τ (M τ k) e

/-- Write `det (A; x_τ)` for the determinant of a constant matrix `A` stacked over the variable
matrix `x_τ`; `stackedDetProd` is a product of these. Substituting `x_τ ↦ c_τᵀ x_τ g_τᵀ` in the
product of the `det (M τ k * g_τᵀ; x_τ)` gives the product of the `det (M τ k; x_τ)`, each factor
at `τ` multiplied by `det c_τ * det g_τ`. -/
lemma twoSidedSubst_stackedDetProd (e : a ⊕ N ≃ L) [Fintype Φ] {ι : Φ → Type}
    [∀ τ : Φ, Fintype (ι τ)] (M : (τ : Φ) → ι τ → Matrix a L ℂ) (c : Φ → Matrix N N ℂ)
    (g : Φ → Matrix L L ℂ) :
    twoSidedSubst c g (stackedDetProd e fun (τ : Φ) (k : ι τ) ↦ M τ k * (g τ)ᵀ) =
      (∏ τ : Φ, ((c τ).det * (g τ).det) ^ Fintype.card (ι τ)) • stackedDetProd e M := by
  -- It suffices to treat one factor. If `A` is its matrix on the right, the matrix on the left is
  -- `diag(1, c)ᵀ · A · gᵀ`.
  have h_factor (τ : Φ) (B : Matrix a L ℂ) :
      twoSidedSubst c g (stackedDet τ (B * (g τ)ᵀ) e) =
        ((c τ).det * (g τ).det) • stackedDet τ B e := by
    let A : Matrix (a ⊕ N) (a ⊕ N) (MvPolynomial (Φ × N × L) ℂ) :=
      ((B.map C).fromRows (of fun i j ↦ X (τ, i, j))).submatrix id e
    have h_left : twoSidedSubst c g (stackedDet τ (B * (g τ)ᵀ) e) =
        (C.mapMatrix (fromBlocks 1 0 0 (c τ))ᵀ * (A * C.mapMatrix ((g τ).submatrix e e)ᵀ)).det := by
      rw [stackedDet, AlgHom.map_det]
      congr 1
      ext (i | i) j : 2
      · simp [A, mul_apply, one_apply, ← e.sum_comp]
      · simp [A, mul_apply, mul_sum, mul_add, mul_assoc, mul_comm, ← e.sum_comp, ← C_mul']
    simp only [h_left, det_mul, ← RingHom.map_det]
    simp [stackedDet, A, ← C_mul', mul_comm, mul_left_comm, mul_assoc]
  simp only [stackedDetProd, map_prod, h_factor, prod_smul, prod_const, card_univ]

/-- The coordinate `l` of `F` in the first `p` columns: regard `F` as a polynomial in these
columns (`New.Rows.inFirstCols`), pair it with the basis polynomial `l` of weight `κ` (a product of
minors, `nablaBasis`) by the form `⟨P, Q⟩ = P(∂) Q (0)` (`fockPairing`) and divide by the hook
number. This is the integer `⟨f, f⟩` for the product `f` of the leading principal minors with
exponents `κ`, at the ranks `rankAt (fun _ ↦ N) τ = card N`. The result is a polynomial in the
entries of the columns `L`. If `F` is the polynomial (`toPoly`) of a vector `ζ (z)` of the Weyl
module of weight `κ`, with `z` the columns `L`, these are the coordinates of `ζ (z)`. -/
def firstColsCoord {p : ℕ} [Fintype Φ] (κ : Φ → ℕ → ℕ) (F : MvPolynomial (Φ × N × (Fin p ⊕ L)) ℂ)
    (l : WeylIndexFamily (fun _ : Φ ↦ N) κ) : MvPolynomial (Φ × N × L) ℂ :=
  (hookNumber κ (rankAt fun _ : Φ ↦ N) : ℂ)⁻¹ •
    fockPairing (MvPolynomial (Φ × N × L) ℂ) (inFirstCols F)
      (nablaBasis (MvPolynomial (Φ × N × L) ℂ) (fun _ : Φ ↦ N) κ l)

omit [DecidableEq L] in
/-- Let `F`, `F'` be polynomials in the entries of matrices `x_τ` with columns `Fin p ⊕ L`, and
suppose that the substitution `x_τ ↦ c_τᵀ x_τ diag(1, g_τ)ᵀ` (`twoSidedSubst`) sends `F'` to
`s • F`. Let `b_l` be the products of minors of weight `κ` in the first `p` columns (`nablaBasis`),
indexed by families `l` of standard fillings. The coordinate `firstColsCoord κ F l` is the Fock
pairing of `F` with `b_l` in these columns, divided by the hook number; it is a polynomial in the
entries `z_τ` of the columns `L`. The Schur matrix is given by
`b_l (c y) = ∑ l', schur κ c l l' * b_l' (y)`. Then the combination of the coordinates of `F'` by
its row `l` goes to `s` times the coordinate `l` of `F` under `z_τ ↦ c_τᵀ z_τ g_τᵀ`. -/
lemma twoSidedSubst_firstColsCoord {p : ℕ} [Fintype Φ] (c : Φ → Matrix N N ℂ)
    (g : Φ → Matrix L L ℂ) [DecidableEq Φ] {F F' : MvPolynomial (Φ × N × (Fin p ⊕ L)) ℂ}
    {s : ℂ} (h_subst : twoSidedSubst c (fun τ : Φ ↦ fromBlocks 1 0 0 (g τ)) F' = s • F)
    (κ : Φ → ℕ → ℕ) (l : WeylIndexFamily (fun _ : Φ ↦ N) κ) :
    twoSidedSubst c g
        (∑ l' : WeylIndexFamily (fun _ : Φ ↦ N) κ, schur κ c l l' • firstColsCoord κ F' l') =
      s • firstColsCoord κ F l := by
  -- Take coordinates in `h_subst`. Under `inFirstCols` the substitution by `(c, diag(1, g))` splits
  -- into `twoSidedSubst c g` on the coefficients and `rowSubst cᵀ` on the first columns; the
  -- adjoint of the latter is `rowSubst c` (`fockPairing_rowSubst`), which acts on the basis by the
  -- Schur matrix (`sum_schur_smul_nablaBasis`).
  let R : Type := MvPolynomial (Φ × N × L) ℂ
  let φ : R →+* R := twoSidedSubst c g
  have h_split : (inFirstCols (p := p)).comp (twoSidedSubst c fun τ ↦ fromBlocks 1 0 0 (g τ)) =
      ((rowSubst fun τ ↦ ((c τ).map C)ᵀ).restrictScalars ℂ).comp
        ((mapAlgHom (twoSidedSubst c g)).comp inFirstCols) :=
    algHom_ext <| by simp [inFirstCols, rowSubst, ← C_mul', one_apply]
  let v : WeylIndexFamily (fun _ : Φ ↦ N) κ → MatrixPoly ((_ : Φ) × N) R := nablaBasis R _ κ
  -- `φ` passes through the pairing with a basis vector, since it fixes that vector.
  have h_pass (l' : WeylIndexFamily (fun _ : Φ ↦ N) κ) (G : MatrixPoly ((_ : Φ) × N) R) :
      twoSidedSubst c g (fockPairing R G (v l')) = fockPairing R (map φ G) (v l') := by
    simpa [φ, v] using map_fockPairing φ G (v l')
  have h_schur : rowSubst (fun τ ↦ (c τ).map C) (v l) = ∑ l', (C (schur κ c l l') : R) • v l' := by
    simp [R, v, ← sum_schur_smul_nablaBasis, detPow, schur_map]
  have h_adjoint : fockPairing R (inFirstCols (s • F)) (v l) =
      ∑ l', schur κ c l l' • fockPairing R (map φ (inFirstCols F')) (v l') := by
    rw [← h_subst, ← inFirstCols.comp_apply, h_split]
    simp [φ, R, fockPairing_rowSubst, h_schur, C_mul']
  have h_smul : s • firstColsCoord κ F l = firstColsCoord κ (s • F) l := by
    simp [firstColsCoord, smul_comm s]
  rw [h_smul, firstColsCoord, h_adjoint]
  simp only [firstColsCoord, map_sum, map_smul, h_pass, smul_sum, smul_comm (schur ..), R, v]

end New.Rows

end StackedDeterminants

end
