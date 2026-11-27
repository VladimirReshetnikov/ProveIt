import Lib.GLn.SchurModule.SchurNorm
import Lib.General.LinearAlgebra.BlockEmbeddings
import Lib.General.LinearAlgebra.MatrixNormBounds

/-!
# Duality of integral GL(n) representations, mixed weights and the Cartan product

The integral representations of `∏_τ GL(n_τ)` act on lattices with bases of products of minors, and
a weight `κ` counts the columns of each height. For the reversed weight `κ'_τ(h) = κ_τ(|n_τ| - h)`,
the representation of weight `κ` composed with `g ↦ g⁻¹ᵀ` is that of weight `κ'` twisted by a power
of the determinant, through a unimodular, isometric, equivariant integer matrix. With this matrix,
the representation of mixed weight with positive part `kp` and negative part `km` embeds integrally
into the tensor product of the representation of weight `kp` with that of weight `km` composed with
`g ↦ g⁻¹ᵀ`. For a splitting `ε : N ⊕ m ≃ n` of the letters, this embedding sends the Cartan product
of vectors of weights `kp` and `km` to their tensor, and the squared norm of the product is
multiplicative. Finally, the representations of `GL n` with parameters `l` and `-l` are paired
invariantly by an integer matrix.

## Main definitions and results

* `New.GL.exists_star_matrix`: the product of the Hodge stars of the columns, a signed bijection
  between basis tensors that replaces each column by its complement.
* `New.GL.exists_int_duality_matrix`: the integer matrix by which the star maps one Weyl module to
  the other.
* `New.GL.IsDualIsometry`, `New.exists_isDualIsometry`: this matrix is unimodular, isometric and
  equivariant; `New.exists_dual_isometry` states these properties as one conjunction.
* `New.GL.MixedCartanEmbedding`: the integer matrix of the embedding and the four properties asked
  of it; `New.GL.weylEvalAt` is the evaluation vector at the array `New.permArray` of a map of rows.
* `New.mixedWeight`: the weight with `kp τ i + km τ (card n - i)` columns of height `i`.
* `New.nonempty_mixedCartanEmbedding`, `New.mixedCartan`: such an embedding exists for this weight,
  and a chosen one.
* `New.Rows.cartanProduct`: the product; `New.Rows.mixedCartan_mulVec_cartanProduct`: `mixedCartan`
  sends it to the tensor of the factors.
* `New.exists_isDualPairing_of_isHCParam`: the pairing is invariant and computes `New.ofAlgForm` at
  `-l`. It is invertible up to the hook number. It is isometric for the Gram norms `New.weylNormSq`.

Notions from other files:
* `New.permArray`: For maps e_τ from rows to natural numbers, the array over R whose entry at row
  (τ,a), column i is 1 if e_τ(a)=i and 0 otherwise.
* `New.nablaFamily`: The module of Borel semi-invariant polynomials of weight `New.diagramWeight`,
  in which `New.nablaBasis` gives coordinates (`New.sum_coords_nablaBasis`).
* `New.weylRep`: The monoid homomorphism from ∏_τ GL(n_τ,R) to square matrices sending g to ∏_τ
  det(g_τ)^{e_τ} times the Schur matrix of g, for integers e_τ.
* `New.schur`: The Schur matrix S_κ(z) of matrices z_τ of size n'_τ×n_τ. Row i holds chosen
  coordinates of b'_i(zy) in the family b_j(y)·∏_τ det(y_τ)^{d_τ}. Here b'_i and b_j are the
  standard basis polynomials in the rows n' and n, and d is given by `New.schurDetExp`.
* `New.weylEval`: The vector of values of the basis minor products at an array y.

## Relation to the literature

Known result: Dual of a Weyl module by Jacobi's complementary minors, and the Cartan component. Here
the results are stated for products of GL_n. The duality and the Cartan map are given by integer
matrices that are isometric and equivariant over fields of characteristic 0. The duality has an
integral inverse and the Cartan map has an integral left inverse. Source: Fulton, Harris,
Representation Theory, 1991, section 15.5; Jantzen 2003; for Jacobi's identity, Grinberg, An
Introduction to Algebraic Combinatorics, Thm 6.4.48.
-/

namespace New

/-!
## A unimodular isometry between the Weyl lattices of dual weights

Coordinates refer to the basis `New.nablaBasis` of products of minors, indexed by
`New.WeylIndexFamily`, and `New.weylGram` is the Gram matrix. Throughout, `rankAt n τ` is `|n_τ|`,
the number of rows at `τ`, and `e'` is the enumeration `e` reversed. The diagrams `κ` and `κ'` are
complementary if `κ'_τ(h) = κ_τ(|n_τ| - h)` for `1 ≤ h < |n_τ|`. Basis tensors are indexed by
`New.ColumnFilling`, and the Weyl modules lie in the tensors through `New.fillingMatrix`.
-/

section Duality

open ComplexOrder Finset Matrix MvPolynomial «GL» SetLike Equiv

variable {Φ : Type} {n : Φ → Type} [Fintype Φ] [∀ τ, Fintype (n τ)]
  [∀ τ, DecidableEq (n τ)] {κ κ' : Φ → ℕ → ℕ}

/-- Jacobi's formula for complementary minors: split the indices by `ρ` and permute the rows by
`π`; for invertible `A`, the minor of `A` on the second part is, up to the sign of `π`,
`det A` times the minor of `A⁻¹ᵀ` on the first part. -/
lemma GL.sign_mul_det_complementary_minor {R m a b : Type*} [CommRing R] [Fintype m] [DecidableEq m]
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {A : Matrix m m R} (hA : IsUnit A.det)
    (ρ : a ⊕ b ≃ m) (π : Equiv.Perm m) :
    π.sign * (A.submatrix (π ∘ ρ ∘ Sum.inr) (ρ ∘ Sum.inr)).det =
      A.det * (A⁻¹ᵀ.submatrix (π ∘ ρ ∘ Sum.inl) (ρ ∘ Sum.inl)).det := by
  -- Multiply `B`, the rearranged `A`, by `M`, whose columns are columns of `B⁻¹` on the first part
  -- and unit vectors on the second; `M` and `B * M` are block triangular.
  let B : Matrix (a ⊕ b) (a ⊕ b) R := (A.submatrix π id).submatrix ρ ρ
  let M : Matrix (a ⊕ b) (a ⊕ b) R := ((A⁻¹ᵀ.submatrix (π ∘ ρ ∘ .inl) ρ).fromRows (fromCols 0 1))ᵀ
  have hB : B.det = π.sign * A.det := by rw [det_submatrix_equiv_self, det_permute]
  have hM : M.det = (A⁻¹ᵀ.submatrix (π ∘ ρ ∘ Sum.inl) (ρ ∘ Sum.inl)).det := by
    rw [det_transpose, ← (submatrix _ _ ρ).fromCols_toCols, fromRows_fromCols_eq_fromBlocks,
      det_fromBlocks_zero₂₁, det_one, mul_one]
    rfl
  have hBM : B * M = fromBlocks 1 B.toBlocks₁₂ 0 (A.submatrix (π ∘ ρ ∘ Sum.inr) (ρ ∘ Sum.inr)) := by
    ext (s | s) (t | t)
    · simp [B, M, transpose_fromRows, hA, Matrix.one_apply]
    · simp [B, M, mul_apply, toBlocks₁₂, Matrix.one_apply]
    · simp [B, M, transpose_fromRows, hA]
    · simp [B, M, mul_apply, toBlocks₁₂, Matrix.one_apply]
  have h_det : (A.submatrix (π ∘ ρ ∘ Sum.inr) (ρ ∘ Sum.inr)).det = B.det * M.det := by
    rw [← det_mul, hBM, det_fromBlocks_zero₂₁, det_one, one_mul]
  -- The sign of `π` squares to `1`.
  rw [h_det, hB, hM, ← mul_assoc, ← mul_assoc, ← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one,
    one_mul]

omit [Fintype Φ] in
/-- For an enumeration `e` of the rows, every family `A` of square matrices is the square part
`New.GL.squarePart e y` of some array `y`, the family whose matrix at `τ` has the entry
`y ((τ, a), e_τ b)` at `(a, b)`. -/
lemma GL.exists_squarePart_eq {R : Type} [CommRing R] (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ))
    (A : ∀ τ : Φ, Matrix (n τ) (n τ) R) :
    ∃ y : (Σ τ : Φ, n τ) × ℕ → R, squarePart e y = A := by
  refine ⟨fun ⟨⟨τ, b⟩, t⟩ ↦ ∑ a with e τ a = t, A τ b a, ?_⟩
  ext τ b a
  simp [squarePart, Fin.val_inj, filter_eq']

/-- The value at `(τ, 0)` of the weight of the diagram `κ` counts the columns of height `h` with
`0 < h < N τ`; the factor `min 1 h` drops the term `h = 0`. -/
lemma GL.diagramWeight_zero_eq_sum_min_mul (N : Φ → ℕ) (κ : Φ → ℕ → ℕ) (τ : Φ) :
    diagramWeight N κ (τ, 0) = ∑ h : Fin (N τ), min 1 (h : ℕ) * κ τ h := by
  have h_Ioo : Ioo 0 (N τ) = {h ∈ range (N τ) | 0 < h} := by grind
  rw [diagramWeight_apply, h_Ioo, sum_filter, sum_range]
  refine sum_congr rfl ?_
  rintro ⟨_ | h, -⟩ - <;> simp

variable [DecidableEq Φ]

lemma GL.map_intCast_mul {R a b c : Type*} [CommRing R] [Fintype b] (A : Matrix a b ℤ)
    (B : Matrix b c ℤ) :
    (A * B).map (Int.cast : ℤ → R) = A.map (Int.cast : ℤ → R) * B.map (Int.cast : ℤ → R) :=
  Matrix.map_mul (f := Int.castRingHom R)

/-- If `c'` counts the columns of the diagram complementary to that of `c`, then `c` counts those
of the diagram complementary to that of `c'`. -/
lemma GL.complementary_columns_symm {N : ℕ} {c c' : ℕ → ℕ}
    (hc : ∀ h ∈ Ico 1 N, c' h = c (N - h)) : ∀ h ∈ Ico 1 N, c h = c' (N - h) := by
  intro h hh
  rw [hc _ (by grind), Nat.sub_sub_self (mem_Ico.1 hh).2.le]

/-- A product over the columns of a diagram with `c h` columns of height `h < N` may be taken over
those of the complementary diagram, which has `c' h = c (N - h)` columns of height `h`: the factors
of matching columns agree, and the factors of empty columns are `1`. -/
lemma GL.prod_columns_eq_prod_complementary {M : Type*} [CommMonoid M] {N : ℕ} {c c' : ℕ → ℕ}
    (hc : ∀ h ∈ Ico 1 N, c' h = c (N - h)) (f : ∀ h : Fin N, Fin (c h) → M)
    (f' : ∀ h : Fin N, Fin (c' h) → M)
    (h_match : ∀ (h h' : Fin N) (j : Fin (c h)) (j' : Fin (c' h')),
      (h : ℕ) + h' = N → (j : ℕ) = j' → f h j = f' h' j')
    (h_empty : ∀ (h : Fin N) (j : Fin (c h)), (h : ℕ) = 0 → f h j = 1)
    (h_empty' : ∀ (h : Fin N) (j : Fin (c' h)), (h : ℕ) = 0 → f' h j = 1) :
    ∏ h : Fin N, ∏ j : Fin (c h), f h j = ∏ h : Fin N, ∏ j : Fin (c' h), f' h j := by
  -- Negation in `Fin N` fixes the height `0` and sends a positive height `h` to `N - h`.
  refine prod_equiv (.neg _) (by simp) ?_
  rintro ⟨_ | h, hh⟩ -
  · simp [Fin.neg_def, h_empty, h_empty']
  · let h' : Fin N := -⟨h + 1, hh⟩
    have h_neg : (h' : ℕ) = N - (h + 1) := by simp [h', Fin.neg_def, Nat.mod_eq_of_lt, hh.pos]
    have h_card : c (h + 1) = c' h' := by rw [h_neg, complementary_columns_symm hc _ (by grind)]
    exact Fintype.prod_equiv (finCongr h_card) _ _ fun j ↦ h_match ⟨h + 1, hh⟩ h' j _ (by grind) rfl

/-- The increasing sequence of the indices outside an increasing sequence. -/
noncomputable def columnComplement {N a b : ℕ} (hab : a + b = N) (I : IncreasingMap N a) :
    IncreasingMap N b :=
  have h_card : #(univ.image I.val)ᶜ = b := by
    simp [card_compl, card_image_of_injective _ I.property.injective, ← hab]
  ⟨(univ.image I.val)ᶜ.orderEmbOfFin h_card, OrderEmbedding.strictMono _⟩

lemma range_columnComplement {N a b : ℕ} (hab : a + b = N) (I : IncreasingMap N a) :
    Set.range (columnComplement hab I).val = (Set.range I.val)ᶜ := by
  simp [columnComplement]

lemma columnComplement_injective {N a b : ℕ} (hab : a + b = N) :
    (columnComplement hab : IncreasingMap N a → IncreasingMap N b).Injective := by
  intro I I' h_eq
  refine Subtype.ext ((I.property.range_inj_of_wellFoundedLT I'.property).1 (compl_injective ?_))
  rw [← range_columnComplement hab, ← range_columnComplement hab, h_eq]

/-- The rule of the Hodge star on one column. Number the columns by `e` and the rows by `pos`, and
let `I` be an increasing sequence of `a` row numbers. There is a sign `u` such that for every
invertible `A`, `u` times the minor of `A` on the rows outside `I` and the first `b` columns is
`det A` times the minor of `A⁻¹ᵀ` on the rows `I` and the last `a` columns in reverse order.

This is Jacobi's identity for complementary minors of a matrix and its inverse, for an arbitrary set
of rows and an initial segment of columns, with a sign that is independent of `A` but not
computed. -/
lemma GL.exists_sign_minor_columnComplement {m : Type*} [Fintype m] [DecidableEq m] {N a b : ℕ}
    (hab : a + b = N) (e pos : m ≃ Fin N) (I : IncreasingMap N a) :
    ∃ u : ℤˣ, ∀ {R : Type} [CommRing R] {A : Matrix m m R}, IsUnit A.det →
      (u : ℤ) * (A.submatrix (pos.symm ∘ (columnComplement hab I).val)
          (e.symm ∘ Fin.castLE (Nat.le_of_add_left_le hab.le))).det =
        A.det * (A⁻¹ᵀ.submatrix (pos.symm ∘ I.val)
          (e.symm ∘ Fin.rev ∘ Fin.castLE (Nat.le_of_add_right_le hab.le))).det := by
  -- `ρ` splits the columns into the last `a` and the first `b`, and `σ` splits the rows into `I`
  -- and its complement; `u` is the sign of the permutation between them in Jacobi's formula.
  let ρ : Fin a ⊕ Fin b ≃ m := ((Equiv.refl (Fin a)).sumCongr Fin.revPerm).trans
    (((finSumFinEquiv.trans (finCongr hab)).trans Fin.revPerm).trans e.symm)
  have h_inl (t : Fin a) : ρ (.inl t) = e.symm (Fin.castLE (by omega) t).rev := by
    simp [ρ, Fin.ext_iff]
  have h_inr (t : Fin b) : ρ (.inr t) = e.symm (Fin.castLE (by omega) t) := by
    have h_index : N - (a + (b - (t + 1)) + 1) = t := by omega
    simp [ρ, Fin.ext_iff, h_index]
  let I' : IncreasingMap N b := columnComplement hab I
  have h_bij : (Sum.elim I.val I'.val).Bijective := by
    refine (Fintype.bijective_iff_surjective_and_card _).2 ⟨?_, by simp [hab]⟩
    rw [← Set.range_eq_univ, Set.Sum.elim_range, range_columnComplement, Set.union_compl_self]
  let σ : Fin a ⊕ Fin b ≃ m := (Equiv.ofBijective _ h_bij).trans pos.symm
  let π : Equiv.Perm m := ρ.symm.trans σ
  have h_rows (s : Fin a ⊕ Fin b) : π (ρ s) = pos.symm (Sum.elim I.val I'.val s) := by simp [π, σ]
  refine ⟨π.sign, fun {R} _ {A} hA ↦ ?_⟩
  have h_jacobi : π.sign * (A.submatrix (pos.symm ∘ I'.val) (ρ ∘ Sum.inr)).det =
      A.det * (A⁻¹ᵀ.submatrix (pos.symm ∘ I.val) (ρ ∘ Sum.inl)).det := by
    simpa [Function.comp_def, h_rows] using sign_mul_det_complementary_minor hA ρ π
  simpa only [Function.comp_def, h_inl, h_inr] using h_jacobi

/-- For complementary diagrams `κ`, `κ'`, the filling of `κ'` whose column of height `h' > 0` is the
complement of the matching column of `T`, of height `|n_τ| - h'`. Columns of height `0` are
empty. -/
noncomputable def fillingComplement
    (hκ : ∀ τ : Φ, ∀ h ∈ Ico 1 (rankAt n τ), κ' τ h = κ τ (rankAt n τ - h))
    (T : ColumnFilling n κ) : ColumnFilling n κ' :=
  fun (τ : Φ) (h' : Fin (rankAt n τ)) (j : Fin (κ' τ h')) ↦
  if h_zero : (h' : ℕ) = 0 then ⟨Fin.elim0 ∘ Fin.cast h_zero, fun s ↦ (Fin.cast h_zero s).elim0⟩
  else columnComplement (a := rankAt n τ - h') (Nat.sub_add_cancel h'.is_le')
    (T τ ⟨rankAt n τ - h', by omega⟩
      (Fin.cast (hκ τ h' (mem_Ico.2 ⟨Nat.pos_of_ne_zero h_zero, h'.isLt⟩)) j))

omit [Fintype Φ] [DecidableEq Φ] [∀ τ, DecidableEq (n τ)] in
/-- The column `j` of height `h'` of the complementary filling is the complement of the column `j`
of height `h`, when `h + h' = |n_τ|`. -/
lemma fillingComplement_apply
    (hκ : ∀ τ : Φ, ∀ h ∈ Ico 1 (rankAt n τ), κ' τ h = κ τ (rankAt n τ - h))
    (T : ColumnFilling n κ) {τ : Φ} {h h' : Fin (rankAt n τ)} {j : Fin (κ τ h)}
    {j' : Fin (κ' τ h')} (hh : (h : ℕ) + h' = rankAt n τ) (hj : (j : ℕ) = j') :
    fillingComplement hκ T τ h' j' = columnComplement hh (T τ h j) := by
  obtain ⟨h, h_lt⟩ := h
  obtain ⟨j, j_lt⟩ := j
  obtain rfl : h = rankAt n τ - h' := Nat.eq_sub_of_add_eq hh
  obtain rfl : j = j' := hj
  exact dite_eq_right (by omega)

omit [∀ τ, DecidableEq (n τ)] in
/-- For complementary diagrams `κ`, `κ'`, replacing every column by its complement
(`New.fillingComplement`) is a bijection from the fillings of `κ` to those of `κ'`. -/
lemma fillingComplement_bijective
    (hκ : ∀ τ : Φ, ∀ h ∈ Ico 1 (rankAt n τ), κ' τ h = κ τ (rankAt n τ - h)) :
    (fillingComplement hκ).Bijective := by
  -- It is injective, and so is the map in the other direction; both sets are finite.
  have h_injective {c c' : Φ → ℕ → ℕ}
      (hc : ∀ τ : Φ, ∀ h ∈ Ico 1 (rankAt n τ), c' τ h = c τ (rankAt n τ - h)) :
      (fillingComplement hc : ColumnFilling n c → ColumnFilling n c').Injective := by
    intro T T' hT
    ext τ h j : 3
    by_cases h_zero : (h : ℕ) = 0
    · exact Subtype.ext (funext fun s ↦ (Fin.cast h_zero s).elim0)
    let h' : Fin (rankAt n τ) := ⟨rankAt n τ - h, by omega⟩
    have hh : (h : ℕ) + h' = rankAt n τ := Nat.add_sub_of_le h.is_le'
    have h_card : c τ h = c' τ h' := complementary_columns_symm (hc τ) h (by grind)
    refine columnComplement_injective hh ?_
    rw [← fillingComplement_apply hc T (j' := Fin.cast h_card j) hh rfl, hT,
      fillingComplement_apply hc T' hh rfl]
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨h_injective hκ, le_antisymm ?_ ?_⟩
  · exact Fintype.card_le_of_injective _ (h_injective hκ)
  · exact Fintype.card_le_of_injective _ (h_injective fun τ ↦ complementary_columns_symm (hκ τ))

/-- The product of the Hodge stars of all columns. Let `κ`, `κ'` be complementary diagrams and `e'`
the enumeration `e` of the rows reversed. There is an integer matrix `P` from the basis tensors of
`κ'` to those of `κ`, with `Pᵀ P = 1`, such that the following holds over every commutative ring.
If the square part `g` of the array `y` for `e` is invertible and the square part of `z` for `e'`
is `g⁻¹ᵀ`, then `P` sends the tensor of `y` to `∏_τ det (g_τ)^(λ_τ)` times the tensor of `z`, where
`λ_τ` is the value at `(τ, 0)` of the weight of `κ`. -/
lemma GL.exists_star_matrix (e e' : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ))
    (h_rev : ∀ (τ : Φ) (a : n τ), e' τ a = (e τ a).rev)
    (hκ : ∀ τ : Φ, ∀ h ∈ Ico 1 (rankAt n τ), κ' τ h = κ τ (rankAt n τ - h)) :
    ∃ P : Matrix (ColumnFilling n κ) (ColumnFilling n κ') ℤ,
      Pᵀ * P = 1 ∧
      ∀ (R : Type) [CommRing R] (y z : (Σ τ : Φ, n τ) × ℕ → R),
        (∀ τ : Φ, IsUnit (squarePart e y τ).det) →
        (∀ τ : Φ, squarePart e' z τ = (squarePart e y τ)⁻¹ᵀ) →
        P.map (Int.cast : ℤ → R) *ᵥ fillingMatrixOver R n κ' *ᵥ weylEval n κ' y =
          (∏ τ : Φ, (squarePart e y τ).det ^ diagramWeight (rankAt n) κ (τ, 0)) •
            fillingMatrixOver R n κ *ᵥ weylEval n κ z := by
  -- `P` is the signed bijection that takes the complement of each column, with the product of the
  -- signs `u` in Jacobi's formula. The exponent `min 1 h` drops the empty columns (`h = 0`), which
  -- go to empty columns and not to columns of full height.
  choose u hu using fun (τ : Φ) (h : Fin (rankAt n τ)) (I : IncreasingMap (rankAt n τ) h) ↦
    exists_sign_minor_columnComplement (Nat.add_sub_of_le h.is_le') (e τ) (rowEquivFin n τ) I
  let sign (T : ColumnFilling n κ) : ℤˣ :=
    ∏ τ : Φ, ∏ h : Fin (rankAt n τ), ∏ j : Fin (κ τ h), u τ h (T τ h j) ^ min 1 (h : ℕ)
  let P : Matrix (ColumnFilling n κ) (ColumnFilling n κ') ℤ :=
    of fun T T' ↦ if fillingComplement hκ T = T' then (sign T : ℤ) else 0
  refine ⟨P, ?_, fun R _ y z hy hz ↦ ?_⟩
  · ext T T'
    obtain ⟨S, rfl⟩ := (fillingComplement_bijective hκ).surjective T
    obtain ⟨S', rfl⟩ := (fillingComplement_bijective hκ).surjective T'
    simp [P, mul_apply, one_apply, (fillingComplement_bijective hκ).injective.eq_iff, eq_comm]
  ext T
  -- The minor of an array `x` on the rows listed by a column `I` at `τ`.
  let col (x : (Σ τ : Φ, n τ) × ℕ → R) (τ : Φ) {k : ℕ} (I : IncreasingMap (rankAt n τ) k) : R :=
    eval x (minor R (Sigma.mk τ ∘ (rowEquivFin n τ).symm ∘ I.val))
  -- Jacobi's formula in one column, read on the arrays of coordinates.
  have h_column (τ : Φ) (h : Fin (rankAt n τ)) (I : IncreasingMap (rankAt n τ) h) :
      (u τ h I : R) * col y τ (columnComplement (Nat.add_sub_of_le h.is_le') I) =
        (squarePart e y τ).det * col z τ I := by
    have h_jacobi := hu τ h I (hy τ)
    rw [← hz τ] at h_jacobi
    simpa [col, RingHom.map_det, submatrix, Matrix.map, minor, squarePart, h_rev, -Fin.val_rev]
      using h_jacobi
  -- The complements of the columns of `T` are the columns of the complementary filling.
  have h_reindex (τ : Φ) :
      ∏ h : Fin (rankAt n τ), ∏ j : Fin (κ τ h),
          col y τ (columnComplement (Nat.add_sub_of_le h.is_le') (T τ h j)) ^ min 1 (h : ℕ) =
        ∏ h : Fin (rankAt n τ), ∏ j : Fin (κ' τ h), col y τ (fillingComplement hκ T τ h j) := by
    refine prod_columns_eq_prod_complementary (hκ τ) _ _ ?_ (fun h j h_zero ↦ by simp [h_zero]) ?_
    · intro ⟨h, h_lt⟩ ⟨h', h'_lt⟩ j j' (hh : h + h' = rankAt n τ) hj
      obtain rfl : h' = rankAt n τ - h := by omega
      have h_min : min 1 h = 1 := by omega
      simp [h_min, fillingComplement_apply hκ T hh hj]
    · rintro ⟨_, h_lt⟩ j rfl
      simp [col, minor]
  -- An empty minor is `1`, so the exponent `min 1 h` does not change a minor of size `h`.
  have h_empty (τ : Φ) (h : Fin (rankAt n τ)) (I : IncreasingMap (rankAt n τ) h) :
      col z τ I ^ min 1 (h : ℕ) = col z τ I := by
    obtain ⟨_ | h, hh⟩ := h <;> simp [col, minor]
  have h_filling (x : (Σ τ : Φ, n τ) × ℕ → R) {c : Φ → ℕ → ℕ} (S : ColumnFilling n c) :
      eval x (fillingPoly R S) =
        ∏ τ : Φ, ∏ h : Fin (rankAt n τ), ∏ j : Fin (c τ h), col x τ (S τ h j) := by
    simp only [fillingPoly, tableauPoly, map_prod]
    rfl
  calc (P.map (Int.cast : ℤ → R) *ᵥ fillingMatrixOver R n κ' *ᵥ weylEval n κ' y) T
    _ = (sign T : R) * eval y (fillingPoly R (fillingComplement hκ T)) := by
      simp [P, mulVec, dotProduct, ← fillingMatrixOver_mulVec_weylEval, apply_ite]
    _ = ∏ τ : Φ, ∏ h : Fin (rankAt n τ), ∏ j : Fin (κ τ h),
        ((squarePart e y τ).det * col z τ (T τ h j)) ^ min 1 (h : ℕ) := by
      simp only [sign, Units.coe_prod, Units.val_pow_eq_pow_val, Int.cast_prod, Int.cast_pow,
        h_filling, ← h_reindex, ← prod_mul_distrib, ← _root_.mul_pow, h_column]
    _ = ((∏ τ : Φ, (squarePart e y τ).det ^ diagramWeight (rankAt n) κ (τ, 0)) •
          fillingMatrixOver R n κ *ᵥ weylEval n κ z) T := by
      simp [fillingMatrixOver_mulVec_weylEval, _root_.mul_pow, h_empty, prod_mul_distrib, ← pow_mul,
        prod_pow_eq_pow_sum, diagramWeight_zero_eq_sum_min_mul, h_filling]

/-- The star maps one Weyl module to the other. Let `κ`, `κ'` be complementary diagrams and `e'`
the enumeration `e` of the rows reversed. There are an integer matrix `P` between the basis tensors,
with `Pᵀ P = 1`, and an integer matrix `J`, from coordinates of weight `κ'` to those of weight `κ`,
that is the restriction of `P` along the embeddings `New.fillingMatrix`. Over every commutative ring
and for every invertible `g`, `J S_κ'(g) ev_e = ∏_τ det (g_τ)^(λ_τ) S_κ(g⁻¹ᵀ) ev_{e'}`. Here `S` is
`New.schur`, `ev_e` is the evaluation vector at the frame `permArray e`, and `λ_τ` is the value at
`(τ, 0)` of the weight of the diagram `κ`. -/
lemma GL.exists_int_duality_matrix (e e' : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ))
    (h_rev : ∀ (τ : Φ) (a : n τ), e' τ a = (e τ a).rev)
    (hκ : ∀ τ : Φ, ∀ h ∈ Ico 1 (rankAt n τ), κ' τ h = κ τ (rankAt n τ - h)) :
    ∃ (P : Matrix (ColumnFilling n κ) (ColumnFilling n κ') ℤ)
      (J : Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ') ℤ),
      Pᵀ * P = 1 ∧
      fillingMatrix n κ * J = P * fillingMatrix n κ' ∧
      ∀ (R : Type) [CommRing R] (g : ∀ τ : Φ, Matrix (n τ) (n τ) R), (∀ τ : Φ, IsUnit (g τ).det) →
        J.map (Int.cast : ℤ → R) *ᵥ schur κ' g *ᵥ weylEval n κ' (permArray e) =
          (∏ τ : Φ, (g τ).det ^ diagramWeight (rankAt n) κ (τ, 0)) •
            schur κ (fun τ : Φ ↦ (g τ)⁻¹ᵀ) *ᵥ weylEval n κ (permArray e') := by
  -- `J` is the star `P` on tensors, followed by an integral left inverse `Q` of the embedding.
  obtain ⟨P, hP, hP_rule⟩ := exists_star_matrix e e' h_rev hκ
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (WeylIndexFamily n κ) (ColumnFilling n κ) ℤ,
      Q * fillingMatrix n κ = 1 := exists_fillingMatrix_leftInverse
  have h_left (R : Type) [CommRing R] (v : WeylIndexFamily n κ → R) :
      Q.map (Int.cast : ℤ → R) *ᵥ fillingMatrixOver R n κ *ᵥ v = v := by
    simp [← map_intCast_mul, hQ]
  have h_tensor (R : Type) [CommRing R] (g : ∀ τ : Φ, Matrix (n τ) (n τ) R)
      (hg : ∀ τ : Φ, IsUnit (g τ).det) :
      P.map (Int.cast : ℤ → R) *ᵥ
          fillingMatrixOver R n κ' *ᵥ schur κ' g *ᵥ weylEval n κ' (permArray e) =
        (∏ τ : Φ, (g τ).det ^ diagramWeight (rankAt n) κ (τ, 0)) •
          fillingMatrixOver R n κ *ᵥ schur κ (fun τ : Φ ↦ (g τ)⁻¹ᵀ) *ᵥ
            weylEval n κ (permArray e') := by
    obtain ⟨z, hz⟩ := exists_squarePart_eq e' fun τ : Φ ↦ (g τ)⁻¹ᵀ
    obtain ⟨y, rfl⟩ := exists_squarePart_eq e g
    rw [← hz, schur_squarePart_mulVec, schur_squarePart_mulVec]
    exact hP_rule R y z hg (congrFun hz)
  refine ⟨P, Q * (P * fillingMatrix n κ'), hP, map_injective (Int.cast_injective (α := ℂ)) ?_,
    fun R _ g hg ↦ ?_⟩
  · -- Compare both sides over `ℂ` on the vectors `S(g) ev_e`, which span the Weyl module.
    refine toLin'.injective (ext_schur_weylEval e fun g ↦ ?_)
    have hg (τ : Φ) : IsUnit (g τ).val.det := (isUnit_iff_isUnit_det _).1 (g τ).isUnit
    simp only [toLin'_apply, map_intCast_mul, ← mulVec_mulVec, h_tensor ℂ _ hg, mulVec_smul, h_left]
  · simp only [map_intCast_mul, ← mulVec_mulVec, h_tensor R g hg, mulVec_smul, h_left]

/-- For an enumeration `e` of the rows, the integer matrix `J`, from coordinates of weight `κ'` to
those of weight `κ`, identifies the lattice of weight `κ'` with that of weight `κ` composed with
`g ↦ g⁻¹ᵀ` (this is the dual only over `ℚ`, since the Gram matrix is not unimodular): it is
unimodular and isometric for the Gram matrices `New.weylGram`, sends the evaluation vector at the
frame `e` to that at the reversed frame, and intertwines `g` with its inverse transpose up to a
power of the determinant. -/
structure GL.IsDualIsometry (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ))
    (J : Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ') ℤ) : Prop where
  /-- `J` has a two-sided integer inverse. -/
  exists_inv : ∃ K : Matrix (WeylIndexFamily n κ') (WeylIndexFamily n κ) ℤ, J * K = 1 ∧ K * J = 1
  /-- `J` is an isometry for the Gram matrices: `Jᵀ G_κ J = G_κ'`. -/
  gram_eq : Jᵀ * weylGram n κ * J = weylGram n κ'
  /-- Over a field of characteristic zero, `J` sends the evaluation vector at the frame `e` to
  that at the reversed frame. -/
  mulVec_weylEval (R : Type) [Field R] [CharZero R] :
    J.map (Int.cast : ℤ → R) *ᵥ weylEval n κ' (permArray e) =
      weylEval n κ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a).rev)
  /-- Over a field of characteristic zero, `S_κ(g⁻¹ᵀ) J = ∏_τ det (g_τ)^(-d_τ) J S_κ'(g)` for
  invertible `g`, where `S` is `New.schur` and `d_τ = ∑_{1 ≤ h < |n_τ|} κ_τ(h)`. -/
  equivariant {R : Type} [Field R] [CharZero R] (g : ∀ τ : Φ, GL (n τ) R) :
    schur κ (fun τ : Φ ↦ (g τ)⁻¹.valᵀ) * J.map (Int.cast : ℤ → R) =
      J.map (Int.cast : ℤ → R) * weylRep κ' (fun τ : Φ ↦ -(∑ h ∈ Ico 1 (rankAt n τ), κ τ h : ℕ)) g

/-- Suppose `κ' τ h = κ τ (|n_τ| - h)` for `1 ≤ h < |n_τ|` at every place `τ`. Then for every
enumeration `e` of the rows there is an integer matrix `J`, from coordinates of weight `κ'` to those
of weight `κ`, with the properties `New.GL.IsDualIsometry`. That is, `J` is unimodular and isometric
for the Gram matrices, sends the evaluation vector at the frame `e` to that at the reversed frame,
and intertwines `g` with its inverse transpose up to a power of the determinant. This is the
description of the dual of a Weyl module by the Hodge star in each column. -/
lemma exists_isDualIsometry (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ))
    (hκ : ∀ τ : Φ, ∀ h ∈ Ico 1 (rankAt n τ), κ' τ h = κ τ (rankAt n τ - h)) :
    ∃ J : Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ') ℤ, IsDualIsometry e J := by
  -- `e'` is the enumeration `e` reversed; reversal is symmetric, and so is the relation `hκ`.
  obtain ⟨e', h_rev⟩ : ∃ e' : ∀ τ, n τ ≃ Fin (rankAt n τ), ∀ τ a, e' τ a = (e τ a).rev :=
    ⟨fun τ ↦ (e τ).trans Fin.revPerm, fun _ _ ↦ rfl⟩
  -- Up to a power of `det g`, `J` and `K` turn `g` into `g⁻¹ᵀ` on the vectors `S(g) ev`, which
  -- span (`ext_schur_weylEval`); so `J * K = 1`, `K * J = 1` and the rule are checked on these
  -- vectors.
  obtain ⟨P, J, hP, hPJ, hJ⟩ := exists_int_duality_matrix e e' h_rev hκ
  obtain ⟨-, K, -, -, hK⟩ := exists_int_duality_matrix e' e (by simp [h_rev])
    fun τ ↦ complementary_columns_symm (hκ τ)
  -- The exponents of the determinant in `hJ` and `hK` agree.
  have h_exp (τ : Φ) : diagramWeight (rankAt n) κ (τ, 0) = ∑ h ∈ Ico 1 (rankAt n τ), κ τ h := by
    simp [diagramWeight_apply, ← Ico_add_one_left_eq_Ioo]
  have h_exp' (τ : Φ) : diagramWeight (rankAt n) κ' (τ, 0) = ∑ h ∈ Ico 1 (rankAt n τ), κ τ h := by
    simp +contextual [diagramWeight_apply, ← Ico_add_one_left_eq_Ioo, hκ, sum_Ico_reflect]
  -- Identities of integer matrices are checked over `ℂ`.
  have hJK : J * K = 1 := by
    refine map_injective (Int.cast_injective (α := ℂ)) (toLin'.injective (ext_schur_weylEval e' ?_))
    simp +contextual [map_intCast_mul, hJ, hK, h_exp, h_exp',
      GeneralLinearGroup.det_ne_zero, transpose_nonsing_inv, prod_eq_zero_iff]
  have hKJ : K * J = 1 := by
    refine map_injective (Int.cast_injective (α := ℂ)) (toLin'.injective (ext_schur_weylEval e ?_))
    simp +contextual [map_intCast_mul, hJ, hK, h_exp, h_exp',
      GeneralLinearGroup.det_ne_zero, transpose_nonsing_inv, prod_eq_zero_iff]
  have h_ev (R : Type) [Field R] :
      J.map (Int.cast : ℤ → R) *ᵥ weylEval n κ' (permArray e) = weylEval n κ (permArray e') := by
    simpa using hJ R 1
  have h_rule (R : Type) [Field R] [CharZero R] (g : ∀ τ, GL (n τ) R) :
      schur κ (fun τ ↦ (g τ)⁻¹.valᵀ) * J.map (Int.cast : ℤ → R) =
        J.map (Int.cast : ℤ → R) *
          weylRep κ' (fun τ ↦ -(∑ h ∈ Ico 1 (rankAt n τ), κ τ h : ℕ)) g := by
    refine toLin'.injective (ext_schur_weylEval e ?_)
    simp +contextual [hJ, h_exp, Units.smul_def, Matrix.mul_inv_rev, -Nat.cast_sum,
      GeneralLinearGroup.det_ne_zero, weylRep, mul_pow, prod_mul_distrib, smul_smul,
      prod_eq_zero_iff]
  refine ⟨J, ⟨K, hJK, hKJ⟩, ?_, fun R _ _ ↦ by simpa only [h_rev] using h_ev R, h_rule _⟩
  -- Isometry: the Gram matrices are restricted from tensors, and `J` is the restriction of `P`,
  -- which has `Pᵀ P = 1`.
  rw [← fillingMatrix_transpose_mul_self, ← fillingMatrix_transpose_mul_self]
  calc Jᵀ * ((fillingMatrix n κ)ᵀ * fillingMatrix n κ) * J
    _ = (fillingMatrix n κ * J)ᵀ * (fillingMatrix n κ * J) := by simp [Matrix.mul_assoc]
    _ = (fillingMatrix n κ')ᵀ * (Pᵀ * P) * fillingMatrix n κ' := by simp [hPJ, Matrix.mul_assoc]
    _ = (fillingMatrix n κ')ᵀ * fillingMatrix n κ' := by rw [hP, Matrix.mul_one]

/-- Let `e'` be the enumeration `e` of the rows reversed, and let `κ'_τ(h) = κ_τ(|n_τ| - h)` for
`1 ≤ h < |n_τ|`. There are integer matrices `J` and `K`, inverse to each other, such that `J` is an
isometry for the Gram matrices `New.weylGram`, and over every field of characteristic zero `J`
sends the evaluation vector at the frame `e` to that at `e'` and satisfies
`S_κ(g⁻¹ᵀ) J = J W(g)`, where `S` is `New.schur` and `W = New.weylRep κ' (-d)` is
`∏_τ det(g_τ)^(-d_τ)` times `S_κ'`, with `d_τ = ∑_{1 ≤ h < |n_τ|} κ_τ(h)`. These are the fields of
`New.GL.IsDualIsometry` written out. -/
lemma exists_dual_isometry (e e' : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ))
    (h_rev : e' = fun τ : Φ ↦ (e τ).trans Fin.revPerm)
    (hκ : ∀ τ : Φ, ∀ h ∈ Ico 1 (rankAt n τ), κ' τ h = κ τ (rankAt n τ - h)) :
    ∃ (J : Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ') ℤ)
      (K : Matrix (WeylIndexFamily n κ') (WeylIndexFamily n κ) ℤ),
      J * K = 1 ∧ K * J = 1 ∧
      Jᵀ * weylGram n κ * J = weylGram n κ' ∧
      ∀ (R : Type) [Field R] [CharZero R],
        J.map (Int.cast : ℤ → R) *ᵥ weylEval n κ' (permArray e) = weylEval n κ (permArray e') ∧
        ∀ g : ∀ τ : Φ, GL (n τ) R,
          schur κ (fun τ : Φ ↦ (g τ)⁻¹.valᵀ) * J.map (Int.cast : ℤ → R) =
            J.map (Int.cast : ℤ → R) *
              weylRep κ' (fun τ : Φ ↦ -(∑ h ∈ Ico 1 (rankAt n τ), κ τ h : ℕ)) g := by
  subst h_rev
  obtain ⟨J, hJ⟩ := exists_isDualIsometry e hκ
  obtain ⟨K, hJK, hKJ⟩ := hJ.exists_inv
  exact ⟨J, K, hJK, hKJ, hJ.gram_eq, fun R _ _ ↦ ⟨hJ.mulVec_weylEval R, hJ.equivariant⟩⟩

/-- Let the column counts of `κ'` be those of `κ` reversed. Then the hook number
`hookNumber κ' (rankAt n)` of `κ'`, by which the matrix of Fock pairings inverts the Gram matrix of
`κ'`, times the inverse of the Gram matrix of `κ` is an integer matrix. -/
lemma GL.exists_weylGram_mul_eq_hookNumber_dual_smul
    (hκ : ∀ τ : Φ, ∀ h ∈ Ico 1 (rankAt n τ), κ' τ h = κ τ (rankAt n τ - h)) :
    ∃ B : Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ) ℤ,
      weylGram n κ * B = hookNumber κ' (rankAt n) • 1 := by
  -- The duality `J` is unimodular and carries the Gram matrix of `κ` to that of `κ'`, which the
  -- matrix `F` of Fock pairings inverts up to the hook number of `κ'`.
  obtain ⟨J, K, hJK, -, h_gram, -⟩ := exists_dual_isometry (rowEquivFin n) _ rfl hκ
  let F : Matrix (WeylIndexFamily n κ') (WeylIndexFamily n κ') ℤ :=
    of fun i j ↦ fockPairing ℤ (nablaBasis ℤ n κ' i) (nablaBasis ℤ n κ' j)
  have h_fock : weylGram n κ' * F = hookNumber κ' (rankAt n) • 1 := weylGram_mul_fockPairing
  have h_inv : Kᵀ * Jᵀ = 1 := by rw [← transpose_mul, hJK, transpose_one]
  refine ⟨J * F * Jᵀ, ?_⟩
  calc weylGram n κ * (J * F * Jᵀ) = Kᵀ * Jᵀ * weylGram n κ * (J * F * Jᵀ) := by
        rw [h_inv, Matrix.one_mul]
    _ = Kᵀ * (Jᵀ * weylGram n κ * J * F) * Jᵀ := by simp only [Matrix.mul_assoc]
    _ = hookNumber κ' (rankAt n) • 1 := by
        rw [h_gram, h_fock, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h_inv]

/-- The hook number of the dual weight clears denominators. Let `κ'` be `κ` with its column counts
reversed, `κ' τ h = κ τ (|n_τ| - h)` for `1 ≤ h < |n_τ|`, and let `f` be a Borel semi-invariant
polynomial of weight `κ` over a commutative ring `R` (`f ∈ nablaFamily R n κ`). Then
`hookNumber κ' (rankAt n) • f` equals `toPoly n κ ζ = Σ_i (Gζ)_i b_i` for some vector `ζ` of the
Weyl module, where `ζ` has coordinates indexed by `WeylIndexFamily n κ`, `G` is the integer Gram
matrix `weylGram`, `b_i` are the basis minor products `nablaBasis`, and the hook number is the Fock
norm `F(∂)F(0)` of the product `F` of the leading principal `h×h` minors raised to `κ'_τ(h)`. -/
lemma GL.exists_toPoly_eq_hookNumber_dual_smul {R : Type} [CommRing R]
    (hκ : ∀ τ : Φ, ∀ h ∈ Ico 1 (rankAt n τ), κ' τ h = κ τ (rankAt n τ - h))
    {f : MatrixPoly (Sigma n) R} (hf : f ∈ nablaFamily R n κ) :
    ∃ ζ : WeylIndexFamily n κ → R, toPoly n κ ζ = hookNumber κ' (rankAt n) • f := by
  -- With `G B = hookNumber • 1` for the Gram matrix `G` and `c` the coordinates of `f` in
  -- `nablaBasis`, take `ζ = B *ᵥ c`.
  obtain ⟨B, hB⟩ := exists_weylGram_mul_eq_hookNumber_dual_smul hκ
  obtain ⟨c, rfl⟩ : f ∈ (nablaCombination κ).range := range_nablaCombination.ge hf
  refine ⟨B.map (↑) *ᵥ c, ?_⟩
  rw [← nablaCombination_weylGramOver_mulVec, mulVec_mulVec, ← map_mul_intCast, hB]
  simp [Matrix.map_intCast, ← C_mul']

end Duality

/-!
## Integral embedding of a mixed weight into a tensor product with an inverse-transpose twist

The embedding is the product of the multiplication table `New.GL.comulMatrix` of the bases of minor
products and the duality matrix of `New.exists_isDualIsometry`. Here `WeylIndex n κ` is
`WeylIndexFamily (fun _ : Φ ↦ n) κ`, with the same rows `n` at every place.
-/

section MixedCartan

open Finset Matrix Kronecker Fintype «GL»

variable {Φ : Type _} (n : Type _) [Fintype Φ] [DecidableEq Φ] [Fintype n] [DecidableEq n]
  (kp km l : Φ → ℕ → ℕ)

/-- The column multiplicity function sending (τ,i) to kp_τ(i) + km_τ(|n|−i), with truncated
subtraction of natural numbers. -/
abbrev mixedWeight (τ : Φ) (i : ℕ) : ℕ := kp τ i + km τ (Fintype.card n - i)

/-- The vector of values of the basis of weight `κ` (`New.weylEval`) at the array over `R` that
has, for every index `τ`, a `1` in row `(τ, a)` and column `p (equivFin n a)` and `0` elsewhere
(`New.permArray`). -/
noncomputable abbrev GL.weylEvalAt (R : Type) [CommRing R] (κ : Φ → ℕ → ℕ)
    (p : Fin (Fintype.card n) → ℕ) : WeylIndex n κ → R :=
  weylEval (R := R) (fun _ : Φ ↦ n) κ (permArray fun (_ : Φ) (a : n) ↦ p (Fintype.equivFin n a))

/-- For rows `n` and weights `kp`, `km` and `l`, the integer matrix `M` embeds the lattice of weight
`l` into the tensor product of those of weights `kp` and `km`: it has an integral left inverse, is
an isometry for the Gram matrices, and over every field of characteristic zero it matches the
evaluation vectors and intertwines the Schur matrices up to a determinant power. -/
structure GL.MixedCartanEmbedding where
  /-- The integer matrix `M` from the basis of weight `l` to the tensor product of the bases of
  weights `kp` and `km`. -/
  matrix : Matrix (WeylIndex n kp × WeylIndex n km) (WeylIndex n l) ℤ
  /-- `M` has an integral left inverse. -/
  hasLeftInv : HasLeftInv matrix
  /-- `M` is an isometry for the Gram matrices: the tensor product of those of `kp` and `km` pulls
  back to that of `l`. -/
  gram_eq :
    matrixᵀ * weylGram (fun _ : Φ ↦ n) kp ⊗ₖ weylGram (fun _ : Φ ↦ n) km * matrix =
      weylGram (fun _ : Φ ↦ n) l
  /-- Over a field of characteristic zero, M ev₁ = ev₁ ⊗ ev_{w₀}: `M` sends the evaluation vector
  `New.GL.weylEvalAt` of weight `l` at the identity to the tensor of that of weight `kp` at the
  identity and that of weight `km` at the reversal w₀. Here `(vecMulVec x y).vec` has the entry
  `x j * y i` at `(i, j)`. -/
  top (R : Type) [Field R] [CharZero R] :
      matrix.map ((↑) : ℤ → R) *ᵥ weylEvalAt n R l Fin.val =
        (vecMulVec (weylEvalAt n R km fun i : Fin (Fintype.card n) ↦ (i.rev : ℕ))
          (weylEvalAt n R kp Fin.val)).vec
  /-- Over a field of characteristic zero, `M` intertwines the Schur matrix of `g` for `l`, twisted
  by ∏_τ det(g_τ)^(-∑_{1 ≤ i < |n|} km τ i), with S_kp(g) ⊗ S_km(g⁻ᵀ). This identity of matrices is
  stated after applying both sides to an arbitrary vector `v`. -/
  intertwines {R : Type} [Field R] [CharZero R] (g : Φ → GL n R)
    (v : WeylIndexFamily (fun _ : Φ ↦ n) l → R) :
      matrix.map ((↑) : ℤ → R) *ᵥ
          weylRep l (fun τ : Φ ↦ -((∑ i ∈ Ico 1 (Fintype.card n), km τ i : ℕ) : ℤ)) g *ᵥ v =
        schur kp (fun τ : Φ ↦ (g τ : Matrix n n R)) ⊗ₖ schur km (fun τ : Φ ↦ (g τ)⁻¹.valᵀ) *ᵥ
          matrix.map ((↑) : ℤ → R) *ᵥ v

/-- For rows `n` and column multiplicities `kp`, `km`, let `mixedWeight n kp km` be the weight with
`kp τ i + km τ (card n - i)` columns of height `i` (truncated subtraction). Then there is an integer
matrix embedding its lattice into the tensor product of the lattices of weights `kp` and `km`, in
the sense of `New.GL.MixedCartanEmbedding`. That is, the matrix has an integral left inverse, is an
isometry for the Gram matrices, and over every field of characteristic zero matches the evaluation
vectors and intertwines the Schur matrices up to a power of the determinant. -/
lemma nonempty_mixedCartanEmbedding :
    Nonempty (MixedCartanEmbedding n kp km (mixedWeight n kp km)) := by
  -- Let `kc` be `km` with reversed columns, so that `mixedWeight n kp km` is `kp + kc`. A witness
  -- is `(1 ⊗ J) * C`: the transposed multiplication matrix `C = comulMatrix` splits the weight
  -- `kp + kc` into `kp` and `kc`, and the duality matrix `J` of `exists_isDualIsometry`
  -- identifies the factor `kc`, up to a power of the determinant, with the factor `km` composed
  -- with `g ↦ g⁻¹ᵀ`.
  let kc : Φ → ℕ → ℕ := fun τ i ↦ km τ (card n - i)
  obtain ⟨J, hJ⟩ : ∃ J : Matrix (WeylIndex n km) (WeylIndex n kc) ℤ,
      IsDualIsometry (rowEquivFin fun _ : Φ ↦ n) J :=
    exists_isDualIsometry _ fun _ _ _ ↦ rfl
  obtain ⟨J', -, h_J'_mul_J⟩ := hJ.exists_inv
  obtain ⟨P, h_P_mul_C⟩ : HasLeftInv (comulMatrix ℤ (fun _ : Φ ↦ n) kp kc) := hasLeftInv_comulMatrix
  -- The witness over a ring `R`; `mulLinearMap R A B` is the matrix product `A * B`.
  let K (R : Type) [CommRing R] :
      Matrix (WeylIndex n kp × WeylIndex n km) (WeylIndex n (kp + kc)) R :=
    mulLinearMap R (kronecker (diagonal 1) (J.map (↑))) (comulMatrix R (fun _ : Φ ↦ n) kp kc)
  -- The entries of `comulMatrix R` and of `J.map` are casts of integers, so `K R` is the cast of
  -- `K ℤ`.
  have hK_map (R : Type) [CommRing R] : (K ℤ).map ((↑) : ℤ → R) = K R := by
    aesop (add simp mul_apply) (add simp Matrix.one_apply)
  have h_cast : (Int.cast : ℤ → ℤ) = fun x : ℤ ↦ x := funext fun _ ↦ Int.cast_id
  suffices h_emb : MixedCartanEmbedding n kp km (kp + kc) from ⟨h_emb⟩
  exact
    { matrix := K ℤ
      -- `J' * J = 1` and `P * comulMatrix = 1`.
      hasLeftInv := ⟨mulLinearMap ℤ P (1 ⊗ₖ J'), by
        simp [K, ← (_ ⊗ₖ _).mul_assoc, ← mul_kronecker_mul, h_cast, h_J'_mul_J, h_P_mul_C,
          Matrix.mul_assoc]⟩
      gram_eq := by
        -- `J` is an isometry, and so is `comulMatrix`.
        refine .trans ?_ comulMatrix_isometry
        simp [K, ← (_ ⊗ₖ _).mul_assoc, ← mul_kronecker_mul, ← kroneckerMap_transpose, h_cast,
          ← hJ.gram_eq, Matrix.mul_assoc]
      top R _ _ := by
        -- `comulMatrix` splits the evaluation vector, and `J` reverses the second factor.
        rw [hK_map R]
        simp [K, weylEvalAt, comulMatrix_mulVec_weylEval, ← mulVec_mulVec (weylEval _ _ _),
          hJ.mulVec_weylEval R, kronecker_mulVec_vec, mul_vecMulVec]
      intertwines {R} _ _ g v := by
        -- The equivariance of `J` up to the power of the determinant, then that of `comulMatrix`.
        have hJ_law : schur km (fun τ : Φ ↦ (g τ).val⁻¹ᵀ) * J.map (Int.cast : ℤ → R) =
            (∏ τ : Φ, (g τ).det ^ ∑ i ∈ Ico 1 (card n), (km τ i : ℤ))⁻¹ •
              (J.map (Int.cast : ℤ → R) * schur kc fun τ : Φ ↦ (g τ).val) := by
          simpa [weylRep] using hJ.equivariant g
        rw [hK_map R]
        simp [hJ_law, K, weylRep, ← (_ ⊗ₖ _).mul_assoc, ← mul_kronecker_mul,
          ← comulMatrix_equivariant, kronecker_smul, Matrix.mul_assoc] }

/-- A chosen embedding with the properties `New.GL.MixedCartanEmbedding`, from the lattice of the
weight `New.mixedWeight n kp km`, with `kp τ i + km τ (card n - i)` columns of height `i`, into the
tensor product of the lattices of weights `kp` and `km`. -/
noncomputable def mixedCartan : MixedCartanEmbedding n kp km (mixedWeight n kp km) :=
  (nonempty_mixedCartanEmbedding n kp km).some

end MixedCartan

end New

/-!
## The Cartan product in the mixed Weyl module

A splitting `ε : N ⊕ m ≃ n` of the letters `n` gives a product of a vector of weight `kp` in the
letters `N` and a vector of weight `km` in the letters `m`, with values in the mixed weight.

* `New.Rows.HasColumnsBelow`: `card N ≤ card n`, and the weight has no column of height h with
  `card N ≤ h < card n`.
* `New.Rows.cartanProduct`: the product, moved by a tuple `g` of invertible matrices.
* `New.Rows.mixedCartan_mulVec_cartanProduct`: `New.mixedCartan` sends the product to the tensor
  product of the two factors.
-/

namespace New.Rows

open Finset Matrix Fintype Kronecker Sum «GL»

variable {Φ n N m R L : Type} [CommRing R] [Fintype Φ] [DecidableEq Φ] [Fintype n]
  [Fintype N] [Fintype m] {kp km : Φ → ℕ → ℕ} [NormedField L] [IsUltrametricDist L]

omit [Fintype n] in
/-- Casting an integer matrix product entrywise to `R` and applying it to `v` is applying the
casts of the two factors in turn. -/
lemma _root_.New.map_intCast_mul_mulVec (A : Matrix n m ℤ) (B : Matrix m N ℤ) (v : N → R) :
    (A * B).map (↑) *ᵥ v = A.map (↑) *ᵥ B.map (↑) *ᵥ v := by
  simp [← Int.coe_castRingHom]

/-- A chosen left inverse, with integer entries, of the matrix of `mixedCartan n kp km`. -/
noncomputable def mixedCartanLeftInv {Φ : Type} (n : Type) [Fintype Φ] [DecidableEq Φ] [Fintype n]
    [DecidableEq n] (kp km : Φ → ℕ → ℕ) :
    Matrix (WeylIndex n (mixedWeight n kp km)) (WeylIndex n kp × WeylIndex n km) ℤ :=
  (mixedCartan n kp km).hasLeftInv.choose

/-- `mixedCartan n kp km` embeds the lattice of weight `mixedWeight n kp km` into the tensor product
of the lattices of weights `kp` and `km`. The chosen integer matrix `mixedCartanLeftInv n kp km` is
a left inverse of the matrix of this embedding. -/
lemma mixedCartanLeftInv_mul [DecidableEq n] :
    mixedCartanLeftInv n kp km * (mixedCartan n kp km).matrix = 1 :=
  (mixedCartan n kp km).hasLeftInv.choose_spec

/-- The chosen integral left inverse of `New.mixedCartan` undoes it over any ring. -/
lemma mixedCartanLeftInv_mulVec_mixedCartan_mulVec [DecidableEq n]
    {η : WeylIndex n (mixedWeight n kp km) → R} :
    (mixedCartanLeftInv n kp km).map ((↑) : ℤ → R) *ᵥ
      (mixedCartan n kp km).matrix.map (↑) *ᵥ η = η := by
  rw [← map_intCast_mul_mulVec, mixedCartanLeftInv_mul]
  simp

/-- The Kronecker product `P ⊗ₖ Q` sends the tensor of `a` and `b`, written `(vecMulVec a b)ᵀ.vec`,
to the tensor of `P *ᵥ a` and `Q *ᵥ b`. -/
lemma _root_.Matrix.kronecker_mulVec_vec_transpose_vecMulVec {ι ι' κ κ' S : Type} [CommSemiring S]
    [Fintype ι] [Fintype κ] (P : Matrix ι' ι S) (Q : Matrix κ' κ S) (a : ι → S) (b : κ → S) :
    (P ⊗ₖ Q) *ᵥ (vecMulVec a b)ᵀ.vec = (vecMulVec (P *ᵥ a) (Q *ᵥ b))ᵀ.vec := by
  rw [kronecker_mulVec_vec, transpose_vecMulVec, transpose_vecMulVec, mul_vecMulVec, vecMulVec_mul,
    vecMul_transpose]

/-- The Hermitian product of the tensors of `a` and `b` and of `c` and `d`, each written
`(vecMulVec _ _)ᵀ.vec`, is the product of the Hermitian products of `a` with `c` and of `b`
with `d`. -/
lemma _root_.Matrix.star_vec_transpose_vecMulVec_dotProduct {ι κ S : Type} [CommSemiring S]
    [StarRing S] [Fintype ι] [Fintype κ] (a c : ι → S) (b d : κ → S) :
    star (vecMulVec a b)ᵀ.vec ⬝ᵥ (vecMulVec c d)ᵀ.vec = (star a ⬝ᵥ c) * (star b ⬝ᵥ d) := by
  simp only [dotProduct, Fintype.sum_prod_type, Finset.sum_mul_sum, Pi.star_apply, vec,
    transpose_apply, vecMulVec_apply, star_mul', mul_mul_mul_comm]

/-- Let `n × N` matrices act on the weight `kp` (`New.FitsRanks`: `card N ≤ card n` and `kp` has no
column of height strictly between the two). Over an ultrametric normed field, the Schur matrix
of such matrices with entries of norm at most `1` does not increase the sup norm. -/
lemma norm_schur_mulVec_le [DecidableEq n] [DecidableEq N]
    (hF : FitsRanks (fun _ : Φ ↦ N) (fun _ : Φ ↦ n) kp)
    {A : Φ → Matrix n N L} (hA : ∀ (τ : Φ) (i : n) (j : N), ‖A τ i j‖ ≤ 1)
    (v : WeylIndex N kp → L) : ‖schur kp A *ᵥ v‖ ≤ ‖v‖ := by
  -- `A` comes from the valuation ring, hence so does its Schur matrix: its entries have norm `≤ 1`.
  let 𝒪 : Subring L := (NormedField.valuation (K := L)).integer
  let A₀ (τ : Φ) : Matrix n N 𝒪 := fun i j ↦ ⟨A τ i j, hA τ i j⟩
  have h_entry (i : WeylIndex n kp) (j : WeylIndex N kp) : ‖schur kp A i j‖ ≤ 1 := by
    rw [show schur kp A = (schur kp A₀).map 𝒪.subtype from schur_map hF A₀ 𝒪.subtype]
    exact (schur kp A₀ i j).prop
  exact (norm_mulVec_le h_entry v).trans_eq (one_mul ‖v‖)

/-- `New.FitsRanks` holds and `New.schurDetExp` vanishes: `card N ≤ card n`, and `kp τ h = 0` for
every column height `h` with `card N ≤ h < card n`. -/
abbrev HasColumnsBelow {Φ : Type} (n N : Type) [Fintype n] [Fintype N] (kp : Φ → ℕ → ℕ) : Prop :=
  FitsRanks (fun _ : Φ ↦ N) (fun _ : Φ ↦ n) kp ∧
    schurDetExp (fun _ : Φ ↦ N) (fun _ : Φ ↦ n) kp = 0

omit [Fintype Φ] [DecidableEq Φ] in
/-- If `HasColumnsBelow n N kp`, then `kp` fits the ranks (`New.FitsRanks`): `card N ≤ card n`,
and `kp` has no column of height strictly between the two. -/
lemma HasColumnsBelow.fitsRanks (hkp : HasColumnsBelow n N kp) :
    FitsRanks (fun _ : Φ ↦ N) (fun _ : Φ ↦ n) kp :=
  hkp.left

omit [Fintype Φ] [DecidableEq Φ] in
/-- If `HasColumnsBelow n N kp`, then the determinant exponent `New.schurDetExp` of `kp` for
`n × N` matrices is zero. -/
lemma HasColumnsBelow.schurDetExp_eq_zero (hkp : HasColumnsBelow n N kp) :
    schurDetExp (fun _ : Φ ↦ N) (fun _ : Φ ↦ n) kp = 0 :=
  hkp.right

variable [DecidableEq n] [DecidableEq N] [DecidableEq m] (ε : N ⊕ m ≃ n)

/-- The product of a vector of weight `kp` in the letters `N` and a vector of weight `km` in the
letters `m`, for the splitting `ε : N ⊕ m ≃ n` of the letters, moved by `g`: apply the Schur
matrix of the `N`-columns of `g` to the first and that of the `m`-columns of the inverse
transpose of `g` to the second, take the tensor product, and apply the left inverse of
`mixedCartan`. -/
noncomputable def cartanProduct (g : Φ → GL n R) :
    (WeylIndex N kp → R) →ₗ[R] (WeylIndex m km → R) →ₗ[R] WeylIndex n (mixedWeight n kp km) → R :=
  ((vecMulVecBilin R R).compl₁₂ (schur kp fun τ : Φ ↦ (g τ).val.submatrix id (ε ∘ inl)).mulVecLin
      (schur km fun τ : Φ ↦ (g τ)⁻¹.valᵀ.submatrix id (ε ∘ inr)).mulVecLin).compr₂
    (((mixedCartanLeftInv n kp km).map (↑)).mulVecLin ∘ₗ
      LinearMap.pi fun p : WeylIndex n kp × WeylIndex n km ↦ entryLinearMap R R p.1 p.2)

/-- `cartanProduct ε g y η` is the left inverse of `New.mixedCartan` applied to the tensor
product of the Schur images of `y` and `η`. -/
lemma cartanProduct_apply (g : Φ → GL n R) (y : WeylIndex N kp → R) (η : WeylIndex m km → R) :
    cartanProduct ε g y η = (mixedCartanLeftInv n kp km).map (↑) *ᵥ
      (vecMulVec (schur kp (fun τ : Φ ↦ (g τ).val.submatrix id (ε ∘ inl)) *ᵥ y)
        (schur km (fun τ : Φ ↦ (g τ)⁻¹.valᵀ.submatrix id (ε ∘ inr)) *ᵥ η))ᵀ.vec :=
  rfl

/-- For a weight that is `HasColumnsBelow`, the Schur matrices are multiplicative with no
determinant factor: `S(A) S(B) = S(A B)` for `n × N` matrices `A τ` and square matrices `B τ`. -/
lemma HasColumnsBelow.schur_mul_schur (hkp : HasColumnsBelow n N kp) (A : Φ → Matrix n N R)
    (B : Φ → Matrix N N R) : schur kp A * schur kp B = schur kp fun τ : Φ ↦ A τ * B τ := by
  simp [schur_mul_right hkp.fitsRanks, hkp.schurDetExp_eq_zero]

/-- For weights that are `HasColumnsBelow`, a ring homomorphism `f` from `ℂ` to a field `K` of
characteristic zero, applied entrywise, commutes with the product at `g = 1`. -/
lemma map_cartanProduct (hkp : HasColumnsBelow n N kp) (hkm : HasColumnsBelow n m km)
    (ε : N ⊕ m ≃ n) {K : Type} [Field K] [CharZero K] (y : WeylIndex N kp → ℂ)
    (η : WeylIndex m km → ℂ) (f : ℂ →+* K) :
    f ∘ cartanProduct ε 1 y η = cartanProduct ε 1 (f ∘ y) (f ∘ η) := by
  ext p
  simp [cartanProduct, ← mul_inclMatrix, ← map_inclMatrix f, schur_map hkp.fitsRanks,
    schur_map hkm.fitsRanks, dotProduct, mulVec, vecMulVec_apply]

/-- Let `ε : N ⊕ m ≃ n` split the letters. Let `kp` satisfy `HasColumnsBelow n N kp`:
`card N ≤ card n` and `kp` has no columns of height `h` with `card N ≤ h < card n`; let `km`
likewise satisfy `HasColumnsBelow n m km`. Let `K` be a field of characteristic zero, `y` a vector
of weight `kp` in the letters `N` and `η` one of weight `km` in `m`, and take the images of `y` and
`η` under the Schur matrices of `inclMatrix K (ε ∘ inl)` and `inclMatrix K (ε ∘ inr)`. Then the
matrix of the embedding `mixedCartan n kp km` sends `cartanProduct ε 1 y η`, which is its left
inverse applied to the tensor product of these images, back to that tensor product (written
`(vecMulVec _ _)ᵀ.vec`), so the left inverse loses nothing. -/
lemma mixedCartan_mulVec_cartanProduct {Φ n N m : Type} [Fintype Φ] [DecidableEq Φ] [Fintype n]
    [DecidableEq n] [Fintype N] [DecidableEq N] [Fintype m] [DecidableEq m] {kp km : Φ → ℕ → ℕ}
    (hkp : HasColumnsBelow n N kp) (hkm : HasColumnsBelow n m km)
    (ε : N ⊕ m ≃ n) {K : Type} [Field K] [CharZero K] (y : WeylIndexFamily (fun _ : Φ ↦ N) kp → K)
    (η : WeylIndexFamily (fun _ : Φ ↦ m) km → K) :
    (mixedCartan n kp km).matrix.map (↑) *ᵥ cartanProduct ε 1 y η =
      (vecMulVec (schur kp (fun _ : Φ ↦ inclMatrix K (ε ∘ inl)) *ᵥ y)
        (schur km (fun _ : Φ ↦ inclMatrix K (ε ∘ inr)) *ᵥ η))ᵀ.vec := by
  -- Both sides are bilinear in `(y, η)`; `T` is the right side. By `ext_schur_weylEval` it suffices
  -- to take for `y` and `η` the translates of evaluation vectors by invertible `u` and `w`.
  let T : (WeylIndexFamily (fun _ : Φ ↦ N) kp → K) →ₗ[K] (WeylIndexFamily (fun _ : Φ ↦ m) km → K)
    →ₗ[K]
      WeylIndex n kp × WeylIndex n km → K :=
    ((vecMulVecBilin K K).compl₁₂ (schur kp fun _ : Φ ↦ inclMatrix K (ε ∘ inl)).mulVecLin
      (schur km fun _ : Φ ↦ inclMatrix K (ε ∘ inr)).mulVecLin).compr₂
        (.pi fun p : WeylIndex n kp × WeylIndex n km ↦ entryLinearMap K K p.1 p.2)
  have h_T (y' : WeylIndexFamily (fun _ : Φ ↦ N) kp → K)
    (η' : WeylIndexFamily (fun _ : Φ ↦ m) km → K) :
      T y' η' = (vecMulVec (schur kp (fun _ : Φ ↦ inclMatrix K (ε ∘ inl)) *ᵥ y')
        (schur km (fun _ : Φ ↦ inclMatrix K (ε ∘ inr)) *ᵥ η'))ᵀ.vec :=
    rfl
  suffices h_bilin :
      (cartanProduct ε 1).compr₂ ((mixedCartan n kp km).matrix.map (↑)).mulVecLin = T by
    rw [← h_T]
    exact LinearMap.congr_fun₂ h_bilin y η
  refine ext_schur_weylEval (rowEquivFin fun _ : Φ ↦ N) fun u ↦
    ext_schur_weylEval (rowEquivFin fun _ : Φ ↦ m) fun w ↦ ?_
  set y : WeylIndexFamily (fun _ : Φ ↦ N) kp → K := schur kp (fun τ : Φ ↦ (u τ).val) *ᵥ
    weylEval (fun _ : Φ ↦ N) kp
      (permArray fun (τ : Φ) (i : N) ↦ (rowEquivFin (fun _ : Φ ↦ N) τ i : ℕ)) with hy
  set η : WeylIndexFamily (fun _ : Φ ↦ m) km → K := schur km (fun τ : Φ ↦ (w τ).val) *ᵥ
    weylEval (fun _ : Φ ↦ m) km
      (permArray fun (τ : Φ) (i : m) ↦ (rowEquivFin (fun _ : Φ ↦ m) τ i : ℕ)) with hη
  -- `δ` puts the letters of `N` first, in order, and those of `m` last, in reverse order;
  -- `g τ` is the block matrix of `u τ` and `(w τ)ᵀ⁻¹`, with rows along `ε` and columns along `δ`.
  have h_card : card N + card m = card n := by simp [← card_congr ε]
  let δ : N ⊕ m ≃ n :=
    (((equivFin N).sumCongr ((equivFin m).trans Fin.revPerm)).trans finSumFinEquiv).trans
      ((finCongr h_card).trans (equivFin n).symm)
  have h_unit (τ : Φ) : IsUnit (reindex ε δ (fromBlocks (u τ).val 0 0 (w τ).valᵀ⁻¹)) := by simp
  let g (τ : Φ) : GL n K := (h_unit τ).unit
  -- The tensor is the image under `mixedCartan` of the translate by `g` of the evaluation vector.
  have h_range : T y η = (mixedCartan n kp km).matrix.map (↑) *ᵥ
      weylRep (mixedWeight n kp km) (fun τ : Φ ↦ -∑ i ∈ Ico 1 (card n), km τ i) g *ᵥ
        weylEval (fun _ : Φ ↦ n) (mixedWeight n kp km)
          (permArray fun (_ : Φ) (a : n) ↦ (equivFin n a).val) := by
    rw [MixedCartanEmbedding.intertwines, MixedCartanEmbedding.top]
    -- Each coordinate is a product of minors; compare the entries of the matrices, block by block.
    -- The columns read lie in the block of `N`, or of `m`, because `kp` and `km` are
    -- `HasColumnsBelow`.
    ext
    simp [hy, hη, hkp, hkm, g, T, inclMatrix, ← card_congr ε,
      schur_mulVec_weylEval_of_schurDetExp_eq_zero,
      inv_fromBlocks_zero₂₁_of_isUnit_iff, Matrix.one_apply, vecMulVec_apply, kronecker_mulVec_vec,
      mul_vecMulVec, vecMulVec_mul, vecMul_transpose, weylEvalAt]
    unfold weylEval nablaBasis tableauPoly minor
    simp [RingHom.map_det, Matrix.map]
    -- Each side is the product of the minors of the `N`-block and of the `m`-block, in the two
    -- orders; `congr!` matches them entry by entry, and each entry is closed by the case split on
    -- the block of `ε.symm`.
    refine (mul_comm _ _).trans ?_
    congr!
    all_goals
      simp [← ε.symm_apply_eq, permArray, reindex_equiv δ, δ]
      rcases ε.symm _ with i | i
      · simp
        grind [univ.sum_eq_zero, Fin]
      · simp
        grind [univ.sum_eq_zero, Fin]
  -- At `g = 1` the Schur matrices in `cartanProduct` are those of the inclusions of the letters.
  have h_one : cartanProduct ε 1 y η = (mixedCartanLeftInv n kp km).map (↑) *ᵥ T y η := by
    rw [cartanProduct_apply, h_T]
    simp [inclMatrix]
  -- On the image of `mixedCartan` the left inverse undoes `mixedCartan`.
  calc ((cartanProduct ε 1).compr₂ ((mixedCartan n kp km).matrix.map (↑)).mulVecLin) y η
      = (mixedCartan n kp km).matrix.map (↑) *ᵥ cartanProduct ε 1 y η := rfl
    _ = T y η := by rw [h_one, h_range, mixedCartanLeftInv_mulVec_mixedCartan_mulVec]

/-- Let `ε : N ⊕ m ≃ n` split the letters, suppose `kp` and `km` satisfy `HasColumnsBelow`
(`card N ≤ card n` with `kp τ h = 0` for `card N ≤ h < card n`, likewise for `m`, `km`), and let `K`
be a field of characteristic zero. Take `y` of weight `kp`, `η` of weight `km`, and
`g : Φ → GL n K`. Then `weylRep` of `g` for the weight `mixedWeight n kp km` (column multiplicities
`kp τ i + km τ (card n - i)`), twisted by `∏_τ det(g_τ)^(-∑_{1 ≤ i < card n} km τ i)` and applied to
`cartanProduct ε 1 y η`, equals `cartanProduct ε g y η`, where the Schur matrices of the `N`-columns
of `g` and of the `m`-columns of `g⁻ᵀ` first act on `y` and `η`. -/
lemma weylRep_mulVec_cartanProduct (hkp : HasColumnsBelow n N kp) (hkm : HasColumnsBelow n m km)
    (ε : N ⊕ m ≃ n) {K : Type} [Field K] [CharZero K] (y : WeylIndex N kp → K)
    (η : WeylIndex m km → K) (g : Φ → GL n K) :
    weylRep (mixedWeight n kp km) (fun τ : Φ ↦ -∑ i ∈ Ico 1 (Fintype.card n), km τ i)
        g *ᵥ cartanProduct ε 1 y η = cartanProduct ε g y η := by
  -- `MixedCartanEmbedding.intertwines` moves `g` across `mixedCartan`, and
  -- `mixedCartan_mulVec_cartanProduct` computes the vector it then acts on.
  have h_image : (mixedCartan n kp km).matrix.map (↑) *ᵥ weylRep (mixedWeight n kp km)
      (fun τ : Φ ↦ -∑ i ∈ Ico 1 (card n), km τ i) g *ᵥ cartanProduct ε 1 y η =
        (vecMulVec (schur kp (fun τ : Φ ↦ (g τ).val.submatrix id (ε ∘ inl)) *ᵥ y)
          (schur km (fun τ : Φ ↦ (g τ)⁻¹.valᵀ.submatrix id (ε ∘ inr)) *ᵥ η))ᵀ.vec := by
    calc _ = schur kp (fun τ : Φ ↦ (g τ).val) ⊗ₖ schur km (fun τ : Φ ↦ (g τ)⁻¹.valᵀ) *ᵥ
            (mixedCartan n kp km).matrix.map (↑) *ᵥ cartanProduct ε 1 y η := by
          simpa using (mixedCartan n kp km).intertwines g (cartanProduct ε 1 y η)
      _ = (vecMulVec
            (schur kp (fun τ : Φ ↦ (g τ).val) *ᵥ schur kp (fun _ : Φ ↦ inclMatrix K (ε ∘ inl)) *ᵥ y)
            (schur km (fun τ : Φ ↦ (g τ)⁻¹.valᵀ) *ᵥ
              schur km (fun _ : Φ ↦ inclMatrix K (ε ∘ inr)) *ᵥ η))ᵀ.vec := by
          rw [mixedCartan_mulVec_cartanProduct hkp hkm, kronecker_mulVec_vec_transpose_vecMulVec]
      _ = _ := by
          -- `S(g) S(ι) = S(g ι)`, and `g ι` is the block of columns of `g` picked by the inclusion.
          simp only [mulVec_mulVec, ← schur_mul_left hkp.fitsRanks, ← schur_mul_left hkm.fitsRanks,
            mul_inclMatrix]
  rw [cartanProduct_apply ε g, ← h_image, mixedCartanLeftInv_mulVec_mixedCartan_mulVec]

/-- Let ε : N ⊕ m ≃ n split the letters, and let `kp`, `km` satisfy `HasColumnsBelow`: card N, card
m ≤ card n, and there are no columns of height from card N (resp. card m) up to below card n. Then
for y, η of weights kp, km, the squared Gram norm `New.weylNormSq` of their product
`cartanProduct ε 1 y η` at g = 1 is `weylNormSq y * weylNormSq η`. -/
lemma weylNormSq_cartanProduct (hkp : HasColumnsBelow n N kp) (hkm : HasColumnsBelow n m km)
    (ε : N ⊕ m ≃ n) (y : WeylIndex N kp → ℂ) (η : WeylIndex m km → ℂ) :
    weylNormSq (cartanProduct ε 1 y η) = weylNormSq y * weylNormSq η := by
  -- `mixedCartan` is an isometry (`gram_eq`) that sends the product to the tensor of the images
  -- `a` of `y` and `b` of `η` (`mixedCartan_mulVec_cartanProduct`). The Gram form of the tensor
  -- product factors, and the inclusions of the letters keep each squared norm.
  let c : WeylIndex n (mixedWeight n kp km) → ℂ := cartanProduct ε 1 y η
  let G : Matrix (WeylIndex n kp × WeylIndex n km) (WeylIndex n kp × WeylIndex n km) ℂ :=
    (weylGram (fun _ : Φ ↦ n) kp).map (↑) ⊗ₖ (weylGram (fun _ : Φ ↦ n) km).map (↑)
  let M : Matrix (WeylIndex n kp × WeylIndex n km) (WeylIndex n (mixedWeight n kp km)) ℂ :=
    (mixedCartan n kp km).matrix.map (↑)
  let a : WeylIndex n kp → ℂ := schur kp (fun _ : Φ ↦ inclMatrix ℂ (ε ∘ inl)) *ᵥ y
  let b : WeylIndex n km → ℂ := schur km (fun _ : Φ ↦ inclMatrix ℂ (ε ∘ inr)) *ᵥ η
  have h_gram : (weylGram (fun _ : Φ ↦ n) (mixedWeight n kp km)).map (↑) = Mᴴ * G * M := by
    rw [← (mixedCartan n kp km).gram_eq]
    ext i j
    simp [M, G, mul_apply]
  -- An inclusion `ι` of letters has `ιᴴ ι = 1`, so `S(ι)ᴴ G S(ι) = G S(ιᴴ ι) = G`.
  have h_norm {k : Type} [Fintype k] [DecidableEq k] {κ : Φ → ℕ → ℕ} (hκ : HasColumnsBelow n k κ)
      {f : k → n} (hf : f.Injective) (v : WeylIndex k κ → ℂ) :
      weylNormSq (schur κ (fun _ : Φ ↦ inclMatrix ℂ f) *ᵥ v) = weylNormSq v := by
    have h_incl : (inclMatrix ℂ f)ᴴ * inclMatrix ℂ f = 1 := by
      ext i j
      simp [inclMatrix, mul_apply, Matrix.one_apply, hf.eq_iff, eq_comm]
    simp [weylNormSq, star_mulVec_dotProduct, schur_conjTranspose_weylGram_schur hκ.fitsRanks,
      hκ.schurDetExp_eq_zero, h_incl, schur_one]
  calc weylNormSq c
      = (star c ⬝ᵥ (Mᴴ * G * M) *ᵥ c).re := by rw [weylNormSq, h_gram]
    _ = (star (M *ᵥ c) ⬝ᵥ G *ᵥ M *ᵥ c).re := by
        simp only [star_mulVec_dotProduct, mulVec_mulVec, Matrix.mul_assoc]
    _ = (star (vecMulVec a b)ᵀ.vec ⬝ᵥ G *ᵥ (vecMulVec a b)ᵀ.vec).re := by
        rw [mixedCartan_mulVec_cartanProduct hkp hkm]
    _ = weylNormSq a * weylNormSq b := by
        rw [kronecker_mulVec_vec_transpose_vecMulVec, star_vec_transpose_vecMulVec_dotProduct,
          ← coe_weylNormSq, ← coe_weylNormSq, ← Complex.ofReal_mul, Complex.ofReal_re]
    _ = weylNormSq y * weylNormSq η := by
        rw [h_norm hkp (ε.injective.comp inl_injective),
          h_norm hkm (ε.injective.comp inr_injective)]

end New.Rows

/-!
## The invariant integral pairing of opposite weights

`New.IsHCParam κ e l` says that `l` lists twice the Harish-Chandra parameter of the weight `(κ, e)`.
`New.ofAlgForm` passes from vector-valued algebraic forms to functions on the adelic group.
-/

section DualWeights

open NumberField Matrix Finset Fintype

namespace New

section Parameter

variable {Φ n : Type} [Fintype Φ] [Fintype n] {κ κ' : Φ → ℕ → ℕ} {e e' : Φ → ℤ} {l : Φ → n → ℤ}

/-- In rank `N`, for `p + 1 < N`, entries `p` and `p + 1` of the parameter `New.hcParameter`
differ by twice the number `κ w (p + 1)` of columns of height `p + 1`, plus two. -/
lemma hcParameter_sub_succ {N p : ℕ} (w : Φ) (hp : p + 1 < N) :
    hcParameter κ e N w p - hcParameter κ e N w (p + 1) = 2 * κ w (p + 1) + 2 := by
  classical
  have h_row : diagramWeight (fun _ ↦ N) κ (w, p) =
      diagramWeight (fun _ ↦ N) κ (w, p + 1) + κ w (p + 1) := by
    rw [GL.diagramWeight_eq_succ_add, ite_eq_left hp]
  simp only [hcParameter, h_row]
  push_cast
  ring

/-- If `l` and `-l` list the parameters (`New.IsHCParam`) of `(κ, e)` and `(κ', e')`, then each
parameter is the negative of the other read backwards: for `p + q + 1 = card n`, entry `p` of the
parameter of `(κ', e')` is minus entry `q` of that of `(κ, e)`. -/
lemma IsHCParam.hcParameter_rev (hl : IsHCParam κ e l) (hl_neg : IsHCParam κ' e' (-l)) (w : Φ)
    {p q : ℕ} (hpq : p + q + 1 = card n) :
    hcParameter κ' e' (card n) w p = -hcParameter κ e (card n) w q := by
  classical
  -- Entry `q` of the parameter of `(κ, e)` sits at the index `i` of position `q` for `l`; for
  -- `-l` that index has the reversed position `p`.
  obtain ⟨f, hf⟩ : ∃ f : n ≃ Fin (card n), ∀ a : n,
      decreasingPosition (l w) a = f a ∧ decreasingPosition (-l w) a = (f a).rev :=
    exists_equiv_decreasingPosition (hl w).left
  obtain ⟨i, hi_pos, hi_val, -⟩ : ∃ i : n, decreasingPosition (l w) i = q ∧
      l w i = hcParameter κ e (card n) w q ∧ ∀ x < l w i, q < #{k : n | x < l w k} :=
    hl.exists_decreasingPosition_eq w (by omega)
  obtain ⟨hf_pos, hf_rev⟩ := hf i
  have hi_rev : decreasingPosition (-l w) i = p := by
    rw [hf_rev, Fin.val_rev, ← hf_pos, hi_pos]
    omega
  rw [← hi_val, ← hi_rev]
  exact (hl_neg.eq_hcParameter w i).symm

/-- If `l` and `-l` list the parameters of `(κ, e)` and `(κ', e')`, the diagrams are dual: for
`1 ≤ j < card n`, `κ` has as many columns of height `j` as `κ'` has of height `card n - j`. -/
lemma IsHCParam.columns_eq_of_neg (hl : IsHCParam κ e l) (hl_neg : IsHCParam κ' e' (-l)) (w : Φ)
    {j : ℕ} (hj : j ∈ Ico 1 (card n)) : κ w j = κ' w (card n - j) := by
  obtain ⟨hj_pos, hj_lt⟩ := mem_Ico.mp hj
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, j = q + 1 := ⟨j - 1, by omega⟩
  obtain ⟨p, hp⟩ : ∃ p : ℕ, card n - (q + 1) = p + 1 := ⟨card n - (q + 1) - 1, by omega⟩
  have h_step : hcParameter κ e (card n) w q - hcParameter κ e (card n) w (q + 1) =
      2 * κ w (q + 1) + 2 := hcParameter_sub_succ w hj_lt
  have h_step' : hcParameter κ' e' (card n) w p - hcParameter κ' e' (card n) w (p + 1) =
      2 * κ' w (p + 1) + 2 := hcParameter_sub_succ w (by omega)
  -- Both entries of the parameter of `(κ', e')` are minus the entries of that of `(κ, e)`, read
  -- backwards.
  have h_rev_p : hcParameter κ' e' (card n) w p = -hcParameter κ e (card n) w (q + 1) :=
    hl.hcParameter_rev hl_neg w (by omega)
  have h_rev_succ : hcParameter κ' e' (card n) w (p + 1) = -hcParameter κ e (card n) w q :=
    hl.hcParameter_rev hl_neg w (by omega)
  rw [hp]
  omega

/-- If `l` and `-l` list the parameters of `(κ, e)` and `(κ', e')`, the determinant exponents
add up to minus the length of the first row of `κ'`: `e' w + e w = -∑_{1 ≤ j < card n} κ' w j`. -/
lemma IsHCParam.add_eq_neg_sum_of_neg [Nonempty n] (hl : IsHCParam κ e l)
    (hl_neg : IsHCParam κ' e' (-l)) (w : Φ) : e' w + e w = -∑ j ∈ Ico 1 (card n), (κ' w j : ℤ) := by
  -- Compare the first entry of the parameter of `-l` with the last entry of that of `l`.
  obtain ⟨q, hq⟩ : ∃ q : ℕ, card n = q + 1 := Nat.exists_eq_succ_of_ne_zero card_ne_zero
  have h_first : diagramWeight (fun _ ↦ card n) κ' (w, 0) = ∑ j ∈ Ico 1 (card n), κ' w j := by
    simp [diagramWeight_apply, ← Ico_add_one_left_eq_Ioo]
  have h_last : diagramWeight (fun _ ↦ card n) κ (w, q) = 0 := by
    simp [diagramWeight_apply, ← Ico_add_one_left_eq_Ioo, hq]
  have h_rev : hcParameter κ' e' (card n) w 0 = -hcParameter κ e (card n) w q :=
    hl.hcParameter_rev hl_neg w (by omega)
  simp only [hcParameter, h_first, h_last, Nat.cast_sum] at h_rev
  omega

end Parameter

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  {κ κ' : InfinitePlace E → ℕ → ℕ} {e e' : InfinitePlace E → ℤ} {l : InfinitePlace E → n → ℤ}

variable (κ κ' e e' l) in
/-- The pairing `v' ⬝ᵥ A *ᵥ v` of the integer matrix `A` is a duality between the weights
`(κ', e')` and `(κ, e)`, normalised at the highest vector of `l`. -/
structure IsDualPairing (A : Matrix (WeylIndex n κ') (WeylIndex n κ) ℤ) : Prop where
  /-- The pairing is invariant under `GL n` at all places, over every field of characteristic
  zero. -/
  invariant (R : Type) [Field R] [CharZero R] (g : InfinitePlace E → GL n R)
    (v' : WeylIndex n κ' → R) (v : WeylIndex n κ → R) :
    weylRep κ' e' g *ᵥ v' ⬝ᵥ A.map (↑) *ᵥ weylRep κ e g *ᵥ v = v' ⬝ᵥ A.map (↑) *ᵥ v
  /-- The function of a form of weight `(κ', e')` is the pairing of its value with a translate of
  the highest vector of `l`. Here the pairing is written as a bilinear map; see
  `New.IsDualPairing.ofAlgForm_apply`. -/
  ofAlgForm_eq_bilin (s : n → ℤˣ) (η : AlgForm n κ' e') (x : GInf E s) (g : Gf E n) :
    ofAlgForm (-l) s η (x, g) = (dotProductBilin ℂ ℂ).compl₂ (A.map (↑)).mulVecLin (η.val g)
      (conjWeylRep κ e x (highestVector κ l))
  /-- `A` has an integral left inverse up to the hook number of `κ'`. -/
  exists_mul_eq_hookNumber :
    ∃ C : Matrix (WeylIndex n κ) (WeylIndex n κ') ℤ, ∀ v : WeylIndex n κ → ℂ,
      C.map (↑) *ᵥ A.map (↑) *ᵥ v = (hookNumber κ' (rankAt fun _ ↦ n) : ℂ) • v
  /-- Pairing with `v` is the Hermitian product with a vector of the same norm as `v`. -/
  exists_eq_gramForm (v : WeylIndex n κ → ℂ) :
    ∃ v' : WeylIndex n κ' → ℂ, weylNormSq v' = weylNormSq v ∧
      ∀ u : WeylIndex n κ' → ℂ, u ⬝ᵥ A.map (↑) *ᵥ v = gramForm v' u

lemma IsDualPairing.ofAlgForm_apply {A : Matrix (WeylIndex n κ') (WeylIndex n κ) ℤ}
    (hA : IsDualPairing κ κ' e e' l A) (s : n → ℤˣ) (η : AlgForm n κ' e') (x : GInf E s)
    (g : Gf E n) :
    ofAlgForm (-l) s η (x, g) = η.val g ⬝ᵥ A.map (↑) *ᵥ conjWeylRep κ e x (highestVector κ l) :=
  hA.ofAlgForm_eq_bilin s η x g

/-- Let `l` list twice the Harish-Chandra parameter of `(κ, e)`, and `-l` that of `(κ', e')`, in the
sense of `New.IsHCParam`: at each place the entries are distinct values of `hcParameter` at
positions `< card n`. Then some integer matrix `A` makes `v' ⬝ᵥ A *ᵥ v` a duality between the
weights `(κ', e')` and `(κ, e)`, normalised at the highest vector of `l` (`New.IsDualPairing`). It
does so invariantly, computing `New.ofAlgForm` at `-l`, invertibly up to the hook number, and
isometrically. -/
lemma exists_isDualPairing_of_isHCParam [Nonempty n] (hl : IsHCParam κ e l)
    (hl_neg : IsHCParam κ' e' (-l)) :
    ∃ A : Matrix (WeylIndex n κ') (WeylIndex n κ) ℤ, IsDualPairing κ κ' e e' l A := by
  -- Numbering the indices by decreasing `l` numbers them backwards for `-l`, so `κ'` is dual to
  -- `κ`. The pairing is `A = G * J`, with `G` the Gram matrix and `J` the duality of frames.
  have h_enum (w : InfinitePlace E) : ∃ f : n ≃ Fin (card n), ∀ a : n,
      decreasingPosition (l w) a = f a ∧ decreasingPosition (-l w) a = (f a).rev :=
    exists_equiv_decreasingPosition (hl w).left
  choose p hp using h_enum
  -- `J` is a unimodular isometry, and over a field it matches the evaluation vectors at the two
  -- numberings and intertwines `g` with its inverse transpose.
  obtain ⟨J, hJ⟩ : ∃ J : Matrix (WeylIndex n κ') (WeylIndex n κ) ℤ, GL.IsDualIsometry p J :=
    exists_isDualIsometry p (hl.columns_eq_of_neg hl_neg)
  obtain ⟨J', -, h_left_inv⟩ := hJ.exists_inv
  let G : Matrix (WeylIndex n κ') (WeylIndex n κ') ℤ := weylGram (fun _ ↦ n) κ'
  let A : Matrix (WeylIndex n κ') (WeylIndex n κ) ℤ := G * J
  have h_inv (R : Type) [Field R] [CharZero R] (g : InfinitePlace E → GL n R)
      (v' : WeylIndex n κ' → R) (v : WeylIndex n κ → R) :
      weylRep κ' e' g *ᵥ v' ⬝ᵥ A.map (↑) *ᵥ weylRep κ e g *ᵥ v = v' ⬝ᵥ A.map (↑) *ᵥ v := by
    -- The determinant power in the duality is `e' + e`.
    let j : Matrix (WeylIndex n κ') (WeylIndex n κ) R := J.map (↑)
    have h_dual : schur κ' (fun τ ↦ (g τ)⁻¹.valᵀ) * j = j * weylRep κ (fun τ ↦ e' τ + e τ) g := by
      simpa only [hl.add_eq_neg_sum_of_neg hl_neg, ← Nat.cast_sum] using hJ.equivariant g
    -- Move the determinant powers to the side of the inverse transpose.
    have h_schur : (∏ τ, (g τ).det ^ e τ)⁻¹ • (∏ τ, (g τ).det ^ e' τ)⁻¹ •
        (schur κ' (fun τ ↦ (g τ)⁻¹.valᵀ) * j) = j * schur κ fun τ ↦ (g τ).val := by
      simpa [weylRep, ← inv_smul_eq_iff, mul_smul, _root_.zpow_add, prod_mul_distrib] using h_dual
    -- Move `schur κ' g` across `G` by `weylGramOver_mul_schur`; it cancels the inverse transpose.
    rw [map_intCast_mul_mulVec, map_intCast_mul_mulVec]
    change weylRep κ' e' g *ᵥ v' ⬝ᵥ weylGramOver *ᵥ j *ᵥ weylRep κ e g *ᵥ v =
      v' ⬝ᵥ weylGramOver *ᵥ j *ᵥ v
    simp [weylRep, weylGramOver_mul_schur, dotProduct_mulVec, vecMul_mulVec,
      ← transpose_mul, ← h_schur, ← Matrix.mul_assoc]
  -- Pairing with `A *ᵥ v` is the Hermitian product with `star (J *ᵥ v)`, as `G` is symmetric.
  have h_pair (v : WeylIndex n κ → ℂ) (u : WeylIndex n κ' → ℂ) :
      u ⬝ᵥ A.map (↑) *ᵥ v = gramForm (star (J.map (↑) *ᵥ v)) u := by
    rw [map_intCast_mul_mulVec, gramForm_apply, star_star, ← dotProduct_transpose_mulVec,
      weylGram_isSymm.map]
  refine ⟨A, h_inv, fun s η x g ↦ ?ofAlgForm, ?left_inverse,
    fun v ↦ ⟨star (J.map (↑) *ᵥ v), ?norm, h_pair v⟩⟩
  case ofAlgForm =>
    calc ofAlgForm (-l) s η (x, g)
      _ = conjWeylRep κ' e' x⁻¹ (η.val g) ⬝ᵥ A.map (↑) *ᵥ highestVector κ l := by
        -- `J` sends the highest vector of `l` to the highest vector of `-l`.
        rw [algFormCoeff_apply, ← star_highestVector]
        simp [hp, h_pair, hJ.mulVec_weylEval, highestVector]
      _ = conjWeylRep κ' e' x (conjWeylRep κ' e' x⁻¹ (η.val g)) ⬝ᵥ
            A.map (↑) *ᵥ conjWeylRep κ e x (highestVector κ l) := (h_inv ℂ ..).symm
      _ = η.val g ⬝ᵥ A.map (↑) *ᵥ conjWeylRep κ e x (highestVector κ l) := by simp
  case left_inverse =>
    -- The matrix `F` of Fock pairings inverts `G` up to the hook number, and `J'` inverts `J`.
    let F : Matrix (WeylIndex n κ') (WeylIndex n κ') ℤ := of fun i j ↦
      fockPairing ℤ (nablaBasis ℤ (fun _ ↦ n) κ' i) (nablaBasis ℤ (fun _ ↦ n) κ' j)
    have h_fock : Fᵀ * G = hookNumber κ' (rankAt fun _ ↦ n) • 1 :=
      transpose_injective (by simp [F, G, weylGram_isSymm.eq, weylGram_mul_fockPairing])
    have h_left : J' * Fᵀ * A = hookNumber κ' (rankAt fun _ ↦ n) • 1 := by
      rw [Matrix.mul_assoc, ← Fᵀ.mul_assoc, h_fock, smul_mul, Matrix.one_mul, J'.mul_smul,
        h_left_inv]
    refine ⟨J' * Fᵀ, fun v ↦ ?_⟩
    rw [← map_intCast_mul_mulVec, h_left]
    simp [← diagonal_intCast]
  case norm =>
    -- Both squared norms are the real part of `star v ⬝ᵥ Jᵀ G J *ᵥ v`, as `J` is an isometry.
    calc weylNormSq (star (J.map (↑) *ᵥ v))
      _ = (star (J.map (↑) *ᵥ v) ⬝ᵥ A.map (↑) *ᵥ v).re := by rw [h_pair, gramForm_apply, weylNormSq]
      _ = weylNormSq v := by
        simp only [weylNormSq, ← hJ.gram_eq, A, G, map_intCast_mul_mulVec]
        -- `J` has integer entries, so `star (J *ᵥ v) ⬝ᵥ w = star v ⬝ᵥ Jᵀ *ᵥ w`.
        simp [star_mulVec_dotProduct, conjTranspose, transpose_map, Function.comp_def]

end New

end DualWeights
