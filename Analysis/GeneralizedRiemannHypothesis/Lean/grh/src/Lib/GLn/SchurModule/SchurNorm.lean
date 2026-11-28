import Lib.Adelic.AutomorphicForms.SmoothAlgebraicForms

/-!
# Norm bound for Schur matrices and basic facts on the weight representations

Let `S(z) = New.schur κ z` be the Schur matrix of rectangular complex matrices `z τ` of size
`n' τ × n τ`, assuming `New.FitsRanks n n' κ`. Let `G` and `G'` be the integral Gram matrices
`New.weylGram` for `n` and for `n'`. The file gives a formula for `S(w)ᴴ G' S(z)` and bounds the
norm of `S(z)` for these forms. It then proves base change, integrality and invariance of the Gram
pairing for the matrices `New.weylRep` and the action `New.Space.weightRep` of the rational unitary
group of `New.stdSpace`.

## Main definitions and results

* `New.GL.schur_conjTranspose_weylGram_schur`: `S(w)ᴴ G' S(z) = ∏ det(wᴴ z) ^ d · G S(wᴴ z)`, with
  `d = New.schurDetExp n n' κ` the number of columns of height `#(n τ)` if `#(n τ) < #(n' τ)`, and
  `0` otherwise.
* `New.weylNormSq_schur_le`: there are numbers `ρ τ i ≥ 0` (in the proof, the squares of the sorted
  singular values). Their sum over `i < #(n τ)` is at most the sum of the squared absolute values of
  the entries of `z τ`. The Schur matrix multiplies the squared norm by at most the product of the
  `ρ τ i`, to the powers given by the weight `New.diagramWeight`.
* `New.stdSpace_weightRep_apply`, `New.map_weightRep`: γ acts by `New.weylRep` at the matrices
  Φ_τ(γ̄), also after a ring map σ out of ℂ. Here Φ_τ is the embedding that the CM type chooses at
  τ.
* `New.gramForm_conjWeylRep`, `New.gramForm_map_weightRep`: the Gram pairing `New.gramForm` is
  invariant under the compact unitary groups, and under rational γ after any ring endomorphism σ of
  ℂ.

Notions from other files:
* `New.schur`: The Schur matrix S_κ(z) of matrices z_τ of size n'_τ×n_τ. Row i holds chosen
  coordinates of b'_i(zy) in the family b_j(y)·∏_τ det(y_τ)^{d_τ}. Here b'_i and b_j are the
  standard basis polynomials in the rows n' and n, and d is given by `New.schurDetExp`.
* `New.conjWeylRep`: The action of ∏_τ U(s) on coordinate vectors of weight κ by `New.weylRep` at
  the complex conjugate matrices; `New.Space.weightRep` is its restriction to rational points.

## Relation to the literature

Known result: The contravariant form on Weyl's lattice, the Fischer product, and irreducibility
under U(n). This file treats only the contravariant form: its adjoint formula, its invariance under
U(n), and a bound of operator norms by singular values. Source: Jantzen, Representations of
Algebraic Groups, 2nd ed. 2003; Goodman, Wallach, Symmetry, Representations, and Invariants, 2009,
ch. 5; Howe, Perspectives on invariant theory, 1995.
-/

/-!
## Adjoint formula for Schur matrices and the norm bound

The Hermitian forms are `New.weylNormSq` (`ξ ↦ re (ξ* G ξ)`), and `z τ` has size `n' τ × n τ`.
`New.FitsRanks n n' κ` is assumed: `#(n τ) ≤ #(n' τ)`, and `κ τ` has no column of height strictly
between the two.
-/

namespace New

open Finset Matrix ComplexOrder MatrixOrder «GL» Complex

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ]
  {n n' : Φ → Type} [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)]
  [∀ τ : Φ, Fintype (n' τ)] [∀ τ : Φ, DecidableEq (n' τ)] {κ : Φ → ℕ → ℕ}

/-- The adjoint formula: let `w`, `z` be families of complex `n' τ × n τ` matrices, and assume
`FitsRanks n n' κ`: at each `τ`, `#(n τ) ≤ #(n' τ)` and `κ τ h = 0` for `#(n τ) < h < #(n' τ)`. Let
`G` and `G'` be the integer Gram matrices `weylGram` for `n` and `n'`, taken in `ℂ`, and let
`S = schur κ` be the Schur matrix map between the Weyl coordinate spaces for `n` and `n'`. Then
`S(w)ᴴ G' S(z) = (∏ τ, det ((w τ)ᴴ z τ) ^ d τ) • G S(wᴴ z)`, where `d τ = schurDetExp n n' κ τ` is
`κ τ (#(n τ))` if `#(n τ) < #(n' τ)` and `0` otherwise. -/
lemma GL.schur_conjTranspose_weylGram_schur (hF : FitsRanks n n' κ)
    (w z : ∀ τ : Φ, Matrix (n' τ) (n τ) ℂ) :
    (schur κ w)ᴴ * ((weylGram n' κ).map (Int.cast : ℤ → ℂ) * schur κ z) =
      (∏ τ : Φ, ((w τ)ᴴ * z τ).det ^ schurDetExp n n' κ τ) •
        (weylGramOver * schur κ fun τ : Φ ↦ (w τ)ᴴ * z τ) := by
  -- Apply both sides to a vector `ξ`. By `vecMul_schur_eq_iff` and `toPoly_schur` the claim becomes
  -- an identity of polynomials: substituting `zᵀ` and then the conjugate `w'` of `w` is
  -- substituting `zᵀ * w'`, which multiplies `D` by the product of determinants.
  refine ext_iff_mulVec.mpr fun ξ ↦ ?_
  let w' (τ : Φ) : Matrix (n' τ) (n τ) ℂ := (w τ).map (starRingEnd ℂ)
  let D : MatrixPoly ((τ : Φ) × n τ) ℂ := detPow ℂ n (schurDetExp n n' κ)
  have h_sub : rowSubst w' (rowSubst (fun τ ↦ (z τ)ᵀ) (toPoly n κ ξ * D)) =
      (∏ τ, ((w' τ)ᵀ * z τ).det ^ schurDetExp n n' κ τ) •
        (rowSubst (fun τ ↦ (z τ)ᵀ * w' τ) (toPoly n κ ξ) * D) := by
    have h_det (τ : Φ) : ((z τ)ᵀ * w' τ).det = ((w' τ)ᵀ * z τ).det := by
      rw [← det_transpose, transpose_mul, transpose_transpose]
    simp [D, rowSubst_rowSubst, h_det]
  -- Rewritten by `vecMul_schur_eq_iff` and `nablaCombination_weylGramOver_mulVec`, the two sides
  -- applied to `ξ` are the two sides of `h_sub` (with `rowSubst` of the product split).
  simpa [conjTranspose, hF, transpose_map, vecMul_schur_eq_iff,
    nablaCombination_weylGramOver_mulVec, ← mulVec_mulVec, mulVec_transpose, smul_mulVec] using
    h_sub

/-- Sorting: for numbers `d a ≥ 0`, `a ∈ S`, there is a sequence `ρ 0, ρ 1, …` whose first `#S`
terms sum to `∑ a ∈ S, d a`. Also, the product of `d` over any `A ⊆ S` is at most the product of the
first `#A` terms. -/
lemma exists_enum_prod_le {ι : Type*} [DecidableEq ι] (d : ι → NNReal) (S : Finset ι) :
    ∃ ρ : ℕ → NNReal,
      ∑ i ∈ range #S, ρ i = ∑ a ∈ S, d a ∧ ∀ A ⊆ S, ∏ a ∈ A, d a ≤ ∏ i ∈ range #A, ρ i := by
  induction S using induction_on_max_value d with
    | empty => simp
    | insert a S ha h_max ih =>
      obtain ⟨ρ, h_sum, h_prod⟩ := ih
      -- Put the largest value `d a` in front of the list for `S`.
      let ρ' : ℕ → NNReal
        | 0 => d a
        | i + 1 => ρ i
      refine ⟨ρ', by simp [ρ', sum_range_succ', add_comm, h_sum, ha], fun A h_A_subset ↦ ?_⟩
      obtain rfl | ⟨c, hc⟩ : A = ∅ ∨ A.Nonempty := A.eq_empty_or_nonempty
      · simp
      -- Remove from `A` one element `b` (namely `a`, if present) so that the rest lies in `S`.
      obtain ⟨b, hb, h_sub⟩ : ∃ b ∈ A, A.erase b ⊆ S := by grind
      rw [← prod_erase_mul A d hb, ← card_erase_add_one hb, prod_range_succ']
      show (∏ x ∈ A.erase b, d x) * d b ≤ (∏ i ∈ range #(A.erase b), ρ i) * d a
      exact mul_le_mul' (h_prod _ h_sub) (by grind)

omit [Fintype Φ] [DecidableEq Φ] [∀ τ : Φ, DecidableEq (n τ)] in
/-- The rows in one column of a column filling are distinct. -/
lemma fillingRows_injective (T : ColumnFilling n κ) (τ : Φ) (h : Fin (rankAt n τ))
    (j : Fin (κ τ h)) : Function.Injective (fillingRows T τ h j) :=
  (rowEquivFin n τ).symm.injective.comp (T τ h j).2.injective

omit [DecidableEq Φ] in
/-- Diagonal matrices act diagonally on tensors: `minorsMatrix` multiplies the basis tensor of a
column filling `T` by the product of the diagonal entries at the rows that occur in `T`. -/
lemma minorsMatrix_diagonal {R : Type} [CommRing R] (x : ∀ τ : Φ, n τ → R)
    [DecidableEq (ColumnFilling n κ)] :
    minorsMatrix κ (fun τ : Φ ↦ diagonal (x τ)) =
      diagonal fun T : ColumnFilling n κ ↦ ∏ τ : Φ, ∏ h : Fin (rankAt n τ), ∏ j : Fin (κ τ h),
        ∏ s : Fin h, x τ (fillingRows T τ h j s) := by
  ext T T'
  rw [minorsMatrix, of_apply, diagonal_apply]
  split_ifs with h_eq
  · subst h_eq
    simp [submatrix_diagonal _ _ (fillingRows_injective T _ _ _)]
  · -- Two different increasing sequences have different ranges, so that minor has a zero line.
    obtain ⟨τ, h, j, h_ne⟩ : ∃ τ h j, T τ h j ≠ T' τ h j := by simpa [funext_iff] using h_eq
    have h_range : Set.range (T τ h j).1 ≠ Set.range (T' τ h j).1 :=
      mt ((T τ h j).2.range_inj_of_wellFoundedLT (T' τ h j).2).1 (Subtype.coe_ne_coe.2 h_ne)
    refine prod_eq_zero (mem_univ τ) (prod_eq_zero (mem_univ h) (prod_eq_zero (mem_univ j) ?_))
    simp only [Ne, Set.Subset.antisymm_iff, not_and_or, Set.range_subset_iff, not_forall] at h_range
    obtain ⟨s, hs⟩ | ⟨t, ht⟩ := h_range
    · exact det_eq_zero_of_row_eq_zero s fun t ↦
        diagonal_apply_ne _ fun h_row ↦ hs ⟨t, ((Equiv.injective _) h_row).symm⟩
    · exact det_eq_zero_of_column_eq_zero t fun s ↦
        diagonal_apply_ne _ fun h_row ↦ ht ⟨s, (Equiv.injective _) h_row⟩

/-- Let `d τ a ≥ 0`, and let `ρ τ 0 ⋯ ρ τ (h - 1)` bound every product of `h` of the `d τ a`. For
the diagonal matrices `D τ` with entries `d τ a`, the form `η* G S(D) η` is at most `η* G η` times
the product of these bounds over the columns of the diagram of height `h < #(n τ)`, each taken at
its height. Here `G` is the Gram matrix, `S = schur κ`, and `κ τ h` is the number of columns of
height `h` at `τ`. -/
lemma dotProduct_weylGram_schur_diagonal_le (d : ∀ τ : Φ, n τ → NNReal) (ρ : Φ → ℕ → NNReal)
    (h_prod : ∀ (τ : Φ) (A : Finset (n τ)), ∏ a ∈ A, d τ a ≤ ∏ i ∈ range #A, ρ τ i)
    (η : WeylIndexFamily n κ → ℂ) :
    star η ⬝ᵥ (weylGramOver * schur κ fun τ : Φ ↦ diagonal fun a : n τ ↦ (d τ a : ℂ)) *ᵥ η ≤
      (∏ τ : Φ, ∏ h : Fin (rankAt n τ), (∏ i ∈ range h, ρ τ i) ^ κ τ h : NNReal) *
        weylNormSq η := by
  -- The form is restricted from tensors, where `D` acts diagonally in an orthonormal basis.
  let F : Matrix (ColumnFilling n κ) (WeylIndexFamily n κ) ℂ := fillingMatrixOver ℂ n κ
  let entry (T : ColumnFilling n κ) : NNReal :=
    ∏ τ : Φ, ∏ h : Fin (rankAt n τ), ∏ j : Fin (κ τ h), ∏ s : Fin h, d τ (fillingRows T τ h j s)
  have h_gram : (weylGramOver : Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ) ℂ) = Fᴴ * F := by
    simp [weylGramOver_eq_transpose_mul, F, conjTranspose, transpose_map, fillingMatrixOver,
      Function.comp_def]
  have h_form :
      star η ⬝ᵥ (weylGramOver * schur κ fun τ : Φ ↦ diagonal fun a : n τ ↦ (d τ a : ℂ)) *ᵥ η =
        ∑ T : ColumnFilling n κ, (entry T : ℂ) * (‖(F *ᵥ η) T‖ : ℂ) ^ 2 := by
    rw [h_gram, Matrix.mul_assoc, fillingMatrixOver_mul_schur, minorsMatrix_diagonal,
      ← mulVec_mulVec,
      dotProduct_mulVec, ← star_mulVec, ← mulVec_mulVec]
    simp [F, entry, dotProduct, mulVec_diagonal, mul_left_comm, conj_mul']
  have h_norm : (weylNormSq η : ℂ) = ∑ T : ColumnFilling n κ, (‖(F *ᵥ η) T‖ : ℂ) ^ 2 := by
    rw [coe_weylNormSq, h_gram, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
    simp [dotProduct, conj_mul']
  -- A column of height `h` has `h` distinct rows.
  have h_entry (T : ColumnFilling n κ) :
      entry T ≤ ∏ τ : Φ, ∏ h : Fin (rankAt n τ), (∏ i ∈ range h, ρ τ i) ^ κ τ h := by
    simp only [entry, ← Fin.prod_const]
    gcongr with τ _ h _ j
    simpa [prod_image (fillingRows_injective T τ h j).injOn,
      card_image_of_injective _ (fillingRows_injective T τ h j)] using
      h_prod τ (univ.image (fillingRows T τ h j))
  rw [h_form, h_norm, mul_sum]
  exact sum_le_sum fun T _ ↦
    mod_cast mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.2 (h_entry T)) (sq_nonneg _)

omit [∀ τ : Φ, DecidableEq (n τ)] [∀ τ : Φ, DecidableEq (n' τ)] in
/-- Count the boxes of the diagram by rows and by columns. Assume `FitsRanks n n' κ`. The exponent
`diagramWeight (rankAt n') κ (τ, i)` is the number of columns of height `h` with
`i < h < #(n' τ)`. For `i < #(n τ)` these are the `schurDetExp n n' κ τ` columns of height `#(n τ)`
(none if `#(n τ) = #(n' τ)`) and the columns of height `h` with `i < h < #(n τ)`. -/
lemma prod_pow_diagramWeight_eq (hF : FitsRanks n n' κ) (ρ : Φ → ℕ → NNReal) :
    ∏ τ : Φ, ∏ i ∈ range (rankAt n τ), ρ τ i ^ diagramWeight (rankAt n') κ (τ, i) =
      (∏ τ : Φ, (∏ i ∈ range (rankAt n τ), ρ τ i) ^ schurDetExp n n' κ τ) *
        ∏ τ : Φ, ∏ h : Fin (rankAt n τ), (∏ i ∈ range h, ρ τ i) ^ κ τ h := by
  have h_cols : ∏ τ : Φ, ∏ h : Fin (rankAt n τ), (∏ a ∈ range h, ρ τ a) ^ κ τ h =
      ∏ τ : Φ, ∏ h ∈ range (rankAt n τ), (∏ a ∈ range (min (rankAt n τ) h), ρ τ a) ^ κ τ h := by
    simp [prod_range (n := rankAt ..)]
  rw [diagramWeight_eq_of_fitsRanks hF]
  simp +contextual [pow_add, diagramWeight, ← prod_pow_eq_pow_sum, ite_and, prod_pow, field,
    Finsupp.single_apply, prod_comm, -mem_range, prod_mul_distrib, h_cols]

/-- Let `z τ` be complex `n' τ × n τ` matrices, and assume `FitsRanks n n' κ`: at each `τ`,
`#(n τ) ≤ #(n' τ)` and `κ τ h = 0` for `#(n τ) < h < #(n' τ)`. There are numbers `ρ τ i ≥ 0` (in the
proof, the squares of the sorted singular values of `z τ`) with two properties. (a)
`∑ i < #(n τ), ρ τ i` is at most `∑ a b, ‖z τ a b‖ ^ 2`. (b) For every complex coordinate vector `ξ`
on `WeylIndexFamily n κ`, the squared Gram norm `weylNormSq` of the Schur matrix image
`schur κ z *ᵥ ξ` is at most `∏ τ, ∏ i < #(n τ), ρ τ i ^ λ(τ, i)` times `weylNormSq ξ`, where
`λ(τ, i) = diagramWeight (rankAt n') κ (τ, i)` is the sum of `κ τ h` over `i < h < #(n' τ)`. -/
lemma weylNormSq_schur_le (hF : FitsRanks n n' κ) (z : ∀ τ : Φ, Matrix (n' τ) (n τ) ℂ) :
    ∃ ρ : Φ → ℕ → NNReal,
      -- (a)
      (∀ τ : Φ, (range (rankAt n τ)).sum (ρ τ) ≤ ∑ a : n' τ, ∑ b : n τ, ‖z τ a b‖ ^ 2) ∧
      -- (b)
      ∀ ξ : WeylIndexFamily n κ → ℂ,
        weylNormSq (schur κ z *ᵥ ξ) ≤
          (∏ τ : Φ, ∏ i ∈ range (rankAt n τ), ρ τ i ^ diagramWeight (rankAt n') κ (τ, i)) *
            weylNormSq ξ := by
  -- Write `zᴴ z = U D Uᴴ` with `U` unitary and `D` diagonal with entries `d ≥ 0`; the `ρ τ i` are
  -- these eigenvalues, sorted. On tensors a column of height `h` contributes at most
  -- `ρ τ 0 ⋯ ρ τ (h - 1)`.
  have h_herm (τ : Φ) : ((z τ)ᴴ * z τ).IsHermitian := (z τ).isHermitian_conjTranspose_mul_self
  let d (τ : Φ) (a : n τ) : NNReal :=
    ⟨(h_herm τ).eigenvalues a, (z τ).eigenvalues_conjTranspose_mul_self_nonneg a⟩
  have hd (τ : Φ) (a : n τ) : d τ a = (h_herm τ).eigenvalues a := rfl
  have h_enum (τ : Φ) : ∃ ρ : ℕ → NNReal,
      ∑ i ∈ range #(univ : Finset (n τ)), ρ i = ∑ a : n τ, d τ a ∧
        ∀ A ⊆ (univ : Finset (n τ)), ∏ a ∈ A, d τ a ≤ ∏ i ∈ range #A, ρ i :=
    exists_enum_prod_le (d τ) univ
  choose ρ h_sum h_prod using h_enum
  refine ⟨ρ, fun τ ↦ ?_, fun ξ ↦ ?_⟩
  · have h_trace : ∑ a, (d τ a : ℝ) = ∑ a, ∑ b, ‖z τ a b‖ ^ 2 := by
      simpa [← ofReal_inj, hd, conj_mul'] using
        (h_herm τ).trace_eq_sum_eigenvalues.symm.trans sum_comm
    exact le_of_le_of_eq (mod_cast (h_sum τ).le) h_trace
  let D (τ : Φ) : Matrix (n τ) (n τ) ℂ := diagonal fun a : n τ ↦ (d τ a : ℂ)
  let U (τ : Φ) : Matrix (n τ) (n τ) ℂ := (h_herm τ).eigenvectorUnitary
  have h_spec (τ : Φ) : U τ * (D τ * star (U τ)) = (z τ)ᴴ * z τ := by
    simpa [mul_assoc, U, D, hd, Function.comp_def] using (h_herm τ).spectral_theorem.symm
  -- The columns of height `#(n τ)` give powers of `det (zᴴ z)`, the product of all eigenvalues.
  let c : NNReal := ∏ τ : Φ, (∏ a : n τ, d τ a) ^ schurDetExp n n' κ τ
  have h_det : ∏ τ : Φ, ((z τ)ᴴ * z τ).det ^ schurDetExp n n' κ τ = c := by
    simp [c, hd, (h_herm _).det_eq_prod_eigenvalues]

  -- By `schur_conjTranspose_weylGram_schur`, conjugation by `schur κ U` passes inside `schur κ`.
  let G : Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ) ℂ := weylGramOver
  let η : WeylIndexFamily n κ → ℂ := schur κ (star U) *ᵥ ξ
  have h_form (g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ) : star η ⬝ᵥ (G * schur κ g) *ᵥ η =
      star ξ ⬝ᵥ (G * schur κ fun τ ↦ U τ * (g τ * star (U τ))) *ᵥ ξ := by
    simp [η, G, star_mulVec_dotProduct, schur_conjTranspose_weylGram_schur, mul_assoc,
      ← star_eq_conjTranspose (star _)]
  have h_norm : (weylNormSq η : ℂ) = weylNormSq ξ := by
    simpa [U, G, coe_weylNormSq] using h_form fun _ ↦ 1
  let N : NNReal := ∏ τ : Φ, ∏ h : Fin (rankAt n τ), (∏ i ∈ range h, ρ τ i) ^ κ τ h
  -- Pass from `ξ` and `zᴴ z` to `η` and the diagonal `D`.
  have h_bound : (weylNormSq (schur κ z *ᵥ ξ) : ℂ) ≤ c * (N * weylNormSq ξ) := calc
    _ = c * star η ⬝ᵥ (G * schur κ D) *ᵥ η := by
      rw [h_form D, ← h_det]
      simp [h_spec, coe_weylNormSq, star_mulVec_dotProduct,
        schur_conjTranspose_weylGram_schur hF, smul_mulVec, G]
    _ ≤ c * (N * weylNormSq ξ) := by
      rw [← h_norm]
      exact mul_le_mul_of_nonneg_left (dotProduct_weylGram_schur_diagonal_le d ρ
        (fun τ A ↦ h_prod τ A (subset_univ A)) η) (mod_cast c.coe_nonneg)
  have h_le : c * N ≤
      ∏ τ : Φ, ∏ i ∈ range (rankAt n τ), ρ τ i ^ diagramWeight (rankAt n') κ (τ, i) := by
    rw [prod_pow_diagramWeight_eq hF]
    exact mul_le_mul' (prod_le_prod fun τ _ ↦ pow_le_pow_left' (h_prod τ univ subset_rfl) _) le_rfl
  calc weylNormSq (schur κ z *ᵥ ξ)
    _ ≤ c * (N * weylNormSq ξ) := mod_cast h_bound
    _ ≤ _ := by
      rw [← mul_assoc, ← NNReal.coe_mul]
      exact mul_le_mul_of_nonneg_right (mod_cast h_le) (weylNormSq_nonneg ξ)

end New

/-!
## Base change, integrality and invariant metric of weight representations

`New.weylRep κ e g` is ∏_τ det(g_τ)^e_τ times the Schur matrix of g.
-/

section WeightRepBasic

open Matrix ComplexConjugate Units

namespace New

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  {T R S : Type} [CommRing R] [CommRing S] [Fintype T] [DecidableEq T]
  {κ : NumberField.InfinitePlace E → ℕ → ℕ} {e : NumberField.InfinitePlace E → ℤ}
  (γ : U (stdSpace E n).J) (v : WeylIndex n κ → ℂ)

/-- Base change: applying a ring map f entrywise to the matrices g_τ applies f entrywise to the
matrix `New.weylRep` κ e g (∏_τ det(g_τ)^{e_τ} times the Schur matrix of g). -/
lemma weylRep_map {κ : T → ℕ → ℕ} {e : T → ℤ} (f : R →+* S) (g : T → GL n R) :
    weylRep κ e (fun τ : T ↦ GeneralLinearGroup.map f (g τ)) = (weylRep κ e g).map f := by
  -- `coe_units_zpow` is left out: with it this simp call does not close the goal.
  exact ext (by simp [weylRep, schur_map, ← map_zpow, Units.smul_def, f.map_det, -coe_units_zpow])

/-- Integrality: if every g_τ is an invertible matrix over the subring A (with inverse over A,
`New.intGL`), then every entry of `New.weylRep` κ e g lies in A. -/
lemma weylRep_entry_mem {κ : T → ℕ → ℕ} {e : T → ℤ} (A : Subring R) {g : T → GL n R}
    (h_mem_intGL : ∀ τ : T, g τ ∈ intGL n A) (i j : WeylIndexFamily (fun _ : T ↦ n) κ) :
    weylRep κ e g i j ∈ A := by
  -- Each `g τ` is the image of an invertible matrix over `A`, and `weylRep` commutes with
  -- ring maps.
  choose g₀ hg₀ using (h_mem_intGL : ∀ τ : T, ∃ g₀ : GL n A,
    GeneralLinearGroup.map A.subtype g₀ = g τ)
  simp [← funext hg₀, weylRep_map]

/-- The component at the infinite place w of the rational embedding of γ, as a matrix, is γ with
the embedding Φ_w chosen by the CM type applied to its entries. -/
lemma stdSpace_ratEmbed_apply (w : NumberField.InfinitePlace E) :
    (((stdSpace E n).ratEmbed γ).1 w).val.val = (Φ w).mapMatrix γ := by
  -- `erw`: the rational embedding is a composite of equivalences, and the subtype literal it
  -- produces only matches `Subtype.coe_mk` after unfolding them.
  erw [Subtype.coe_mk]
  aesop

/-- On the definite space `New.stdSpace`, γ acts by `New.weylRep` at the family of matrices
Φ_τ(γ̄). -/
lemma stdSpace_weightRep_apply :
    (stdSpace E n).weightRep κ e γ v =
      weylRep κ e (fun τ : NumberField.InfinitePlace E ↦
        GeneralLinearGroup.map ((Φ τ).comp conj) γ) *ᵥ v := by
  refine congrArg (fun g ↦ weylRep κ e g *ᵥ v) ?_
  ext
  simp [stdSpace_ratEmbed_apply, starRingEnd_apply (R := E)]

/-- The Gram pairing on coordinate vectors of weight κ is invariant under the product of the
compact groups U(n), acting in weight (κ, e). -/
lemma gramForm_conjWeylRep {κ : T → ℕ → ℕ} {e : T → ℤ} (x : T → USign 1) (ξ η : WeylIndex n κ → ℂ) :
    gramForm (n := n) (conjWeylRep κ e x ξ) (conjWeylRep κ e x η) = gramForm ξ η := by
  -- `conjWeylRep` acts through the entrywise conjugates `g τ` of the `x τ`, again unitary.
  let g (τ : T) : Matrix n n ℂ := (x τ : Matrix n n ℂ).map conj
  have h_unitary (τ : T) : (g τ)ᴴ * g τ = 1 := by
    simpa [U.map, g] using mem_U.mp (U.map conj (by simp) rfl (x τ)).prop
  have h_det (τ : T) : (g τ).det * conj (g τ).det = 1 := by
    simpa [mul_comm] using congrArg det (h_unitary τ)
  have h_rep (ζ : WeylIndex n κ → ℂ) :
      conjWeylRep κ e x ζ = (∏ τ, (g τ).det ^ e τ) • schur κ g *ᵥ ζ := by
    simp [conjWeylRep, weylRep, Units.smul_def, g]
  -- The determinant factor has absolute value one.
  have h_factor : (∏ τ, (g τ).det ^ e τ) * ∏ τ, conj (g τ).det ^ e τ = 1 := by
    simp [← Finset.prod_mul_distrib, ← mul_zpow, h_det]
  -- By `GL.schur_conjTranspose_weylGram_schur` the Schur matrix of unitary matrices keeps the Gram
  -- matrix.
  have h_gram : (schur κ g)ᴴ * ((weylGram _ κ).map (↑) * schur κ g) = (weylGram _ κ).map (↑) := by
    simp [GL.schur_conjTranspose_weylGram_schur .refl, h_unitary]
  simp [h_rep, gramForm, star_mulVec, dotProduct_mulVec, h_gram, ← mul_assoc, h_factor]

/-- After a ring map σ out of ℂ, γ acts by `New.weylRep` at the matrices σ(Φ_τ(γ̄)). -/
lemma map_weightRep (σ : ℂ →+* R) (γ : U (stdSpace E n).J) (v : WeylIndex n κ → ℂ) :
    σ ∘ (stdSpace E n).weightRep κ e γ v =
      weylRep κ e (fun τ : NumberField.InfinitePlace E ↦
        GeneralLinearGroup.map ((σ.comp (Φ τ)).comp conj) γ) *ᵥ σ ∘ v := by
  ext
  simp [stdSpace_weightRep_apply, σ.map_mulVec, weylRep_map]

/-- The Gram pairing of the σ-conjugates of two coordinate vectors, σ a ring endomorphism of ℂ,
is unchanged when a rational unitary matrix γ acts on both vectors first. -/
lemma gramForm_map_weightRep (σ : ℂ →+* ℂ) (γ : U (stdSpace E n).J) (u v : WeylIndex n κ → ℂ) :
    gramForm (σ ∘ (stdSpace E n).weightRep κ e γ u) (σ ∘ (stdSpace E n).weightRep κ e γ v) =
      gramForm (σ ∘ u) (σ ∘ v) := by
  -- The images `x τ` of `γ` under the embeddings `σ ∘ Φ τ` are unitary, and after `σ` the element
  -- `γ` acts as `x` does in `conjWeylRep`, because embeddings of the CM field commute with
  -- conjugation.
  let x (τ : NumberField.InfinitePlace E) : USign (1 : n → ℤˣ) :=
    U.map (σ.comp (Φ τ)) (by simp) (by simp [stdSpace]) γ
  have h_rep (w : WeylIndex n κ → ℂ) :
      σ ∘ (stdSpace E n).weightRep κ e γ w = conjWeylRep κ e x (σ ∘ w) := by
    rw [map_weightRep]
    refine congrArg (fun g ↦ weylRep κ e g *ᵥ σ ∘ w) ?_
    ext τ i j
    exact map_star_complex (σ.comp (Φ τ)) _
  rw [h_rep, h_rep, gramForm_conjWeylRep]

end New

end WeightRepBasic
