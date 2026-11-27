import Lib.General.LinearAlgebra.Eigenvalues

/-!
# Amitsur's formula and Ribet's method for matrices over an algebra

This file proves Amitsur's formula for block matrices and derives Ribet's method from the
Cayley–Hamilton theorem. Here `u x` (`x : Y`) is a family of matrix representations of `G`. The
coefficients of their characteristic polynomials, as functions of `x`, lie in an algebra `S` of
functions `Y → L`. 'In the image of `R`' is written `∈ (algebraMap R L).range`. The file ends with
Ribet's element for a square matrix of tied rows, a matrix whose rows give relations modulo a left
ideal whose traces are controlled.

## Main definitions and results

* `New.Selmer.exists_ribet_polynomial`: Ribet's method. Let `ρ` represent an `R`-algebra `Λ` with
  characteristic polynomials over `R`, let `𝔞` be a two-sided ideal containing its kernel, and let
  `I` be the left ideal spanned by a vector `y`. If `B y` has entries in `𝔞 + I ρ₀`, then some
  polynomial `P` has constant term `det B`, read through `ρ`, and `I P(ρ₀) ⊆ 𝔞`.
* `New.amitsur_charpoly_comp_coeff_mem_range`: Amitsur's formula for block matrices. If all
  characteristic polynomials of the `ρ w` have their coefficients in the image of `R`, the same
  holds for every square matrix `P` over `Λ`, read as the block matrix with blocks `ρ (P i j)`.
* `New.Selmer.exists_ribet_element_of_tied_rows`: Ribet's element for a matrix of tied rows, for
  representations `u x` (`x : Y`) of `O[G]` and an algebra `S` of functions `Y → L` that contains
  the constants from `O` and, as functions of `x`, the coefficients of the characteristic
  polynomials of the group elements.
-/

namespace New

open Matrix Algebra Submodule Polynomial MonoidAlgebra Finset

variable {O Y σ G L R N Λ : Type*} [CommRing O] [Fintype σ] [DecidableEq σ] [Group G] [CommRing L]
  [Algebra O L] [CommRing R] [Algebra R L]
  {S : Subalgebra R (Y → L)} [Fintype N] [DecidableEq N] [Ring Λ] [Algebra R Λ]

/-- The `R`-algebra isomorphism from `N × N` matrices whose entries are `σ × σ` matrices over `L`
onto `(N × σ) × (N × σ)` matrices over `L`, flattening blocks. -/
@[simps!]
def blockFlattenAlgEquiv (N : Type*) [Fintype N] [DecidableEq N] :
    Matrix N N (Matrix σ σ L) ≃ₐ[R] Matrix (N × σ) (N × σ) L :=
  { compRingEquiv N σ L with
    commutes' _ := comp_diagonal_diagonal _ }

/-- Amitsur's formula for block matrices. Let `ρ` be an `R`-algebra map from `Λ` to square matrices
over `L` such that all characteristic polynomials of the `ρ w` have their coefficients in the image
of `R`. The same then holds for every square matrix `P` over `Λ`, read as the block matrix with
blocks `ρ (P i j)`.

Known result: the integrality consequence of Amitsur's formula for the characteristic polynomial of
a sum of matrices. -/
lemma amitsur_charpoly_comp_coeff_mem_range (ρ : Λ →ₐ[R] Matrix σ σ L)
    (hρ : ∀ (w : Λ) (k : ℕ), (ρ w).charpoly.coeff k ∈ (algebraMap R L).range) (P : Matrix N N Λ)
    (k : ℕ) :
    (Matrix.comp N N σ σ L (P.map ρ)).charpoly.coeff k ∈ (algebraMap R L).range := by
  -- The matrices with a single nonzero row span. Under `φ`, the one with row `q` of `Q` is (block
  -- column `q` of `1`) times (block row `q` of `Q`); the product in the other order is `ρ (Q q q)`.
  let φ : Matrix N N Λ →ₐ[R] Matrix (N × σ) (N × σ) L :=
    (blockFlattenAlgEquiv N).toAlgHom.comp ρ.mapMatrix
  suffices h_row : ∀ (Q : Matrix N N Λ) (q : N) (m : ℕ),
      (φ (∑ j, single q j (Q q j))).charpoly.coeff m ∈ (algebraMap R L).range by
    refine amitsur_charpoly_mem_of_span φ (top_unique fun Q _ ↦ ?_) P k
    rw [matrix_eq_sum_single Q]
    exact sum_mem fun q _ ↦ subset_span (h_row Q q)
  intro Q q m
  have hφ (M : Matrix N N Λ) (i j : N) (a b : σ) : φ M (i, a) (j, b) = ρ (M i j) a b := rfl
  let col : Matrix (N × σ) σ L := (1 : Matrix (N × σ) (N × σ) L).submatrix id fun x ↦ (q, x)
  let row : Matrix σ (N × σ) L := (φ Q).submatrix (fun x ↦ (q, x)) id
  have h_factor : φ (∑ j, single q j (Q q j)) = col * row := by
    ext ⟨i, a⟩ ⟨j, b⟩
    rw [hφ]
    obtain rfl | hi := eq_or_ne q i
    · simp [col, row, hφ, one_apply, Matrix.sum_apply, Matrix.single, Matrix.mul_apply]
    · simp [col, hi, hi.symm, one_apply, Matrix.sum_apply, Matrix.mul_apply]
  have h_swap : row * col = ρ (Q q q) := by
    ext a b
    simp [col, row, hφ, one_apply, Matrix.mul_apply]
  -- The two characteristic polynomials agree up to powers of `X`.
  have h_charpoly : X ^ Fintype.card σ * (col * row).charpoly =
      X ^ Fintype.card (N × σ) * (ρ (Q q q)).charpoly := by
    rw [charpoly_mul_comm', h_swap]
  rw [h_factor, ← coeff_X_pow_mul _ (Fintype.card σ), h_charpoly, coeff_X_pow_mul']
  split_ifs
  exacts [hρ _ _, zero_mem _]

/-- Cramer's rule over `Λ[X]`, from the Cayley–Hamilton theorem, read through `ρ` coefficient by
coefficient. Let `ρ` be an `R`-algebra map from `Λ` to square matrices over `L` whose characteristic
polynomials all have their coefficients in the image of `R`. For a square matrix `B` over `Λ[X]`
there are a polynomial `P` over `R` and a matrix `B'` such that `P(0)` is the determinant of the
block matrix with blocks `ρ (B i j (0))`, and `B' B` is the scalar matrix `P` once `ρ` is applied to
the coefficients of the entries. -/
lemma Selmer.exists_adjugate_polynomial (ρ : Λ →ₐ[R] Matrix σ σ L)
    (h_coeff : ∀ (w : Λ) (k : ℕ), (ρ w).charpoly.coeff k ∈ (algebraMap R L).range)
    (B : Matrix N N Λ[X]) :
    ∃ (P : R[X]) (B' : Matrix N N Λ[X]),
      algebraMap R L (P.eval 0) = (comp N N σ σ L (B.map fun p : Λ[X] ↦ ρ (p.coeff 0))).det ∧
      ∀ (i j : N) (m : ℕ), ρ (((B' * B) i j).coeff m) =
        ρ (((diagonal fun _ : N ↦ P.map (algebraMap R Λ)) i j).coeff m) := by
  -- Extend `ρ` to `ρX` on `Λ[X]`, coefficient by coefficient. As `Λ` spans `Λ[X]` over `R[X]`,
  -- Amitsur's formula puts the characteristic polynomials of `ρX` over `R[X]`.
  let _ : Algebra R[X] Λ[X] := Polynomial.algebra R Λ
  let _ : Algebra R[X] L[X] := Polynomial.algebra R L
  let ρX : Λ[X] →ₐ[R[X]] Matrix σ σ L[X] :=
    { matPolyEquiv.symm.toRingEquiv.toRingHom.comp (mapRingHom ρ.toRingHom) with
      commutes' p := by
        ext i j m
        simp [algebraMap_matrix_apply, apply_ite (Polynomial.coeff · m)] }
  have hρX (p : Λ[X]) (i j : σ) (m : ℕ) : (ρX p i j).coeff m = ρ (p.coeff m) i j := by simp [ρX]
  have hρX_C (w : Λ) : ρX (C w) = (ρ w).map C := by simp [ρX]
  have h_coeffX : ∀ (p : Λ[X]) (k : ℕ), (ρX p).charpoly.coeff k ∈ (algebraMap R[X] L[X]).range := by
    refine amitsur_charpoly_mem_of_span ρX (top_unique fun p _ ↦ ?_)
    rw [p.as_sum_support]
    refine sum_mem fun i _ ↦ ?_
    have h_monomial : monomial i (p.coeff i) = (X ^ i : R[X]) • C (p.coeff i) := by
      simp [Algebra.smul_def, ← C_mul_X_pow_eq_monomial, X_pow_mul]
    rw [h_monomial]
    refine smul_mem _ _ (subset_span fun k ↦ ?_)
    obtain ⟨c, hc⟩ : ∃ c : R, algebraMap R L c = (ρ (p.coeff i)).charpoly.coeff k :=
      h_coeff (p.coeff i) k
    refine ⟨C c, ?_⟩
    rw [hρX_C, charpoly_map, Polynomial.coeff_map, ← hc]
    simp
  -- Cayley–Hamilton for the block matrix `φX B` gives `B'` and the determinant `P`.
  let φX : Matrix N N Λ[X] →ₐ[R[X]] Matrix (N × σ) (N × σ) L[X] :=
    (blockFlattenAlgEquiv N).toAlgHom.comp ρX.mapMatrix
  obtain ⟨B', P, hP, hB', -⟩ : ∃ (B' : Matrix N N Λ[X]) (P : R[X]),
      (φX B).det = algebraMap R[X] L[X] P ∧ φX B' * φX B = P • 1 ∧ φX B * φX B' = P • 1 :=
    exists_adjugate_of_charpoly_mem φX (amitsur_charpoly_comp_coeff_mem_range ρX h_coeffX) B
  have h_mul : φX (B' * B) = φX (P • 1) := by rw [map_mul, hB', map_smul, map_one]
  have hφX (M : Matrix N N Λ[X]) (i j : N) (a b : σ) : φX M (i, a) (j, b) = ρX (M i j) a b := rfl
  have h_entry (i j : N) : ρX ((B' * B) i j) = ρX ((P • (1 : Matrix N N Λ[X])) i j) :=
    Matrix.ext fun a b ↦ by rw [← hφX, ← hφX, h_mul]
  have h_one : P • (1 : Matrix N N Λ[X]) = diagonal fun _ ↦ P.map (algebraMap R Λ) := by
    ext i j
    by_cases h_ij : i = j
    · simp [h_ij, Algebra.smul_def]
    · simp [h_ij, one_apply]
  refine ⟨P, B', ?_, fun i j m ↦ ?_⟩
  · -- The constant terms: `P(0)` and the determinant of `φX B` at `X = 0`.
    have h_map : (φX B).map constantCoeff = comp N N σ σ L (B.map fun p ↦ ρ (p.coeff 0)) := by
      ext ⟨i, a⟩ ⟨j, b⟩
      simp [φX, hρX]
    calc algebraMap R L (P.eval 0) = constantCoeff (algebraMap R[X] L[X] P) := by
          simp [← coeff_zero_eq_eval_zero]
      _ = constantCoeff (φX B).det := by rw [hP]
      _ = (comp N N σ σ L (B.map fun p ↦ ρ (p.coeff 0))).det := by
          rw [RingHom.map_det, RingHom.mapMatrix_apply, h_map]
  · ext a b
    rw [← hρX, ← hρX, h_entry, h_one]

/-- Let `Λ[X]` act on `Q` through a ring homomorphism `π : Λ → Q`, with `Λ` acting by left
multiplication and `X` by right multiplication with `π ρ₀`. Suppose that `B - X B₁` kills the image
of the vector `y`, that is, `B y` and `(B₁ y) ρ₀` have the same image, and that `B' (B - X B₁)` is
the scalar matrix `P`, with `P` a polynomial over `R`, once `π` is applied to the coefficients of
the entries. Then `π (y i P(ρ₀)) = 0`. -/
lemma Selmer.mul_aeval_eq_zero_of_adjugate {Q : Type*} [Ring Q] (π : Λ →+* Q) (y : N → Λ)
    (ρ₀ : Λ) (B B₁ : Matrix N N Λ) (h_kill : ∀ i : N, π ((B *ᵥ y) i) = π ((B₁ *ᵥ y) i * ρ₀))
    (P : R[X]) (B' : Matrix N N Λ[X])
    (h_adj : ∀ (i j : N) (m : ℕ), π (((B' * (B.map C - (X : Λ[X]) • B₁.map C)) i j).coeff m) =
      π (((diagonal fun _ : N ↦ P.map (algebraMap R Λ)) i j).coeff m))
    (i : N) :
    π (y i * aeval ρ₀ P) = 0 := by
  let left : Λ →+* AddMonoid.End Q := (Module.toAddMonoidEnd Q Q).comp π
  let right : AddMonoid.End Q := AddMonoid.End.mulRight (π ρ₀)
  have h_comm (r : Λ) : Commute (left r) right :=
    AddMonoidHom.ext fun q ↦ (mul_assoc (π r) q (π ρ₀)).symm
  let ev : Λ[X] →+* AddMonoid.End Q := eval₂RingHom' left right h_comm
  let _ : Module Λ[X] Q := .compHom Q ev
  have h_smul (c : Λ[X]) (q : Q) : c • q = eval₂ left right c q := rfl
  have hC (r : Λ) (q : Q) : (C r : Λ[X]) • q = π r * q := by
    rw [h_smul, eval₂_C]
    rfl
  have hX (q : Q) : (X : Λ[X]) • q = q * π ρ₀ := by
    rw [h_smul, eval₂_X]
    rfl
  -- The action sees the coefficients only through `π`.
  have h_act (c c' : Λ[X]) (h : ∀ m : ℕ, π (c.coeff m) = π (c'.coeff m)) (q : Q) :
      c • q = c' • q := by
    have h_zero : eval₂ left right (c - c') = 0 := by
      rw [eval₂_eq_sum, Polynomial.sum_def]
      exact Finset.sum_eq_zero fun m _ ↦ by simp [left, h m]
    rw [← sub_eq_zero, ← sub_smul, h_smul, h_zero]
    rfl
  have h_poly (p : R[X]) (r : Λ) : p.map (algebraMap R Λ) • π r = π (r * aeval ρ₀ p) := by
    induction p using Polynomial.induction_on with
    | C a => rw [map_C, hC, aeval_C, ← map_mul, Algebra.commutes]
    | add p q hp hq => simp only [Polynomial.map_add, add_smul, hp, hq, map_add, mul_add]
    | monomial j a ih =>
      calc (C a * X ^ (j + 1)).map (algebraMap R Λ) • π r
        _ = (X : Λ[X]) • (C a * X ^ j).map (algebraMap R Λ) • π r := by
          rw [pow_succ, ← mul_assoc, Polynomial.map_mul, map_X, ← X_mul, mul_smul]
        _ = π (r * aeval ρ₀ (C a * X ^ j) * ρ₀) := by rw [ih, hX, ← map_mul]
        _ = π (r * aeval ρ₀ (C a * X ^ (j + 1))) := by simp [pow_succ, mul_assoc]
  have h_row (l : N) : ∑ j, (B.map C - (X : Λ[X]) • B₁.map C) l j • π (y j) = 0 := by
    calc _ = ∑ j, (π (B l j * y j) - π (B₁ l j * y j * ρ₀)) := by
          simp [sub_smul, mul_smul, hC, hX, mul_assoc]
      _ = π ((B *ᵥ y) l) - π ((B₁ *ᵥ y) l * ρ₀) := by
          simp [mulVec, dotProduct, Finset.sum_mul]
      _ = 0 := sub_eq_zero.2 (h_kill l)
  calc π (y i * aeval ρ₀ P) = ∑ j, (diagonal fun _ ↦ P.map (algebraMap R Λ)) i j • π (y j) := by
        simp [diagonal_apply, h_poly]
    _ = ∑ j, (B' * (B.map C - (X : Λ[X]) • B₁.map C)) i j • π (y j) :=
        Finset.sum_congr rfl fun j _ ↦ (h_act _ _ (h_adj i j) _).symm
    _ = 0 := by
        simp only [Matrix.mul_apply, Finset.sum_smul, mul_smul]
        rw [Finset.sum_comm]
        simp only [← Finset.smul_sum, h_row, smul_zero, Finset.sum_const_zero]

/-- Ribet's method. Let `ρ` represent the `R`-algebra `Λ` by matrices over `L` such that the
characteristic polynomials of a spanning set have coefficients in the image of `R`, and let `𝔞` be
a two-sided ideal of `Λ` that contains the kernel of `ρ`. Let `I` be the left ideal spanned by `y`,
and `B` a square matrix over `Λ` such that the entries of `B y` lie in `𝔞 + I ρ₀`. Then some
polynomial `P` over `R` has constant term `det B`, read through `ρ` as a block matrix, and
`I P(ρ₀) ⊆ 𝔞`. Moreover the traces of the `ρ (ρ₁ P(ρ₀))` lie in the image of `R`, and for `δ : R`
such that some `z ∈ I` has `ρ z = δ` (the scalar matrix), `δ` times such a trace is the trace of
`ρ a` for some `a ∈ 𝔞`. -/
lemma Selmer.exists_ribet_polynomial [Nonempty σ] (ρ : Λ →ₐ[R] Matrix σ σ L)
    (hρ_span : span R {w : Λ | ∀ k : ℕ, (ρ w).charpoly.coeff k ∈ (algebraMap R L).range} = ⊤)
    (𝔞 : TwoSidedIdeal Λ) (hρ_ker : ∀ w : Λ, ρ w = 0 → w ∈ 𝔞) (y : N → Λ) (ρ₀ : Λ)
    (B : Matrix N N Λ)
    (hB : ∀ i : N, ∃ a ∈ 𝔞, ∃ z ∈ span Λ (Set.range y), (B *ᵥ y) i = a + z * ρ₀) :
    ∃ P : R[X],
      algebraMap R L (P.eval 0) = (comp N N σ σ L (B.map ρ)).det ∧
      (∀ z ∈ span Λ (Set.range y), z * aeval ρ₀ P ∈ 𝔞) ∧
      (∀ ρ₁ : Λ, (ρ (ρ₁ * aeval ρ₀ P)).trace ∈ (algebraMap R L).range) ∧
      ∀ (ρ₁ : Λ) (δ : R), (∃ z ∈ span Λ (Set.range y), ρ z = algebraMap R (Matrix σ σ L) δ) →
        ∃ a ∈ 𝔞, algebraMap R L δ * (ρ (ρ₁ * aeval ρ₀ P)).trace = (ρ a).trace := by
  -- Write `B y = B₁ y ρ₀` modulo `𝔞`. Then `B_X = B - X B₁` kills `y` in `Λ / 𝔞`, where `X` acts as
  -- right multiplication with `ρ₀`. As `B' B_X = P` after applying `ρ`, `P` kills `y` too.
  have h_coeff : ∀ (w : Λ) (k : ℕ), (ρ w).charpoly.coeff k ∈ (algebraMap R L).range :=
    amitsur_charpoly_mem_of_span ρ hρ_span
  have h_rows : ∀ i : N, ∃ a ∈ 𝔞, ∃ c : N → Λ, (B *ᵥ y) i = a + (c ⬝ᵥ y) * ρ₀ := by
    intro i
    obtain ⟨a, ha, z, hz, h_split⟩ := hB i
    obtain ⟨c, rfl⟩ : ∃ c : N → Λ, ∑ j, c j • y j = z := (mem_span_range_iff_exists_fun Λ).1 hz
    exact ⟨a, ha, c, h_split⟩
  choose a ha B₁ h_split using h_rows
  let B_X : Matrix N N Λ[X] := B.map C - (X : Λ[X]) • (of B₁).map C
  obtain ⟨P, B', hP, hB'⟩ : ∃ (P : R[X]) (B' : Matrix N N Λ[X]),
      algebraMap R L (P.eval 0) = (comp N N σ σ L (B_X.map fun p ↦ ρ (p.coeff 0))).det ∧
      ∀ (i j : N) (m : ℕ), ρ (((B' * B_X) i j).coeff m) =
        ρ (((diagonal fun _ ↦ P.map (algebraMap R Λ)) i j).coeff m) :=
    Selmer.exists_adjugate_polynomial ρ h_coeff B_X
  let π : Λ →+* 𝔞.ringCon.Quotient := 𝔞.ringCon.mk'
  have hπ (w w' : Λ) : π w = π w' ↔ w - w' ∈ 𝔞 := (RingCon.eq _).trans (𝔞.rel_iff w w')
  have hπρ (w w' : Λ) (h : ρ w = ρ w') : π w = π w' :=
    (hπ w w').2 (hρ_ker _ (by rw [map_sub, h, sub_self]))
  have h_kill (i : N) : π ((B *ᵥ y) i) = π ((of B₁ *ᵥ y) i * ρ₀) := by
    have h_row : (of B₁ *ᵥ y) i = B₁ i ⬝ᵥ y := rfl
    rw [hπ, h_split, h_row, add_sub_cancel_right]
    exact ha i
  have hy (i : N) : y i * aeval ρ₀ P ∈ 𝔞 := by
    rw [← sub_zero (y i * aeval ρ₀ P), ← hπ, map_zero]
    exact Selmer.mul_aeval_eq_zero_of_adjugate π y ρ₀ B (of B₁) h_kill P B'
      (fun i j m ↦ hπρ _ _ (hB' i j m)) i
  have h_mem (w : Λ) (hw : w ∈ span Λ (Set.range y)) : w * aeval ρ₀ P ∈ 𝔞 := by
    obtain ⟨c, rfl⟩ : ∃ c : N → Λ, ∑ j, c j • y j = w := (mem_span_range_iff_exists_fun Λ).1 hw
    rw [Finset.sum_mul]
    refine sum_mem fun i _ ↦ ?_
    rw [smul_eq_mul, mul_assoc]
    exact 𝔞.mul_mem_left _ _ (hy i)
  refine ⟨P, ?_, h_mem, fun ρ₁ ↦ ?_, fun ρ₁ δ ⟨z₀, hz₀, hz₀_eq⟩ ↦ ?_⟩
  · have h_const : (B_X.map fun p ↦ ρ (p.coeff 0)) = B.map ρ := by
      ext i j : 2
      simp [B_X]
    rw [hP, h_const]
  · rw [trace_eq_neg_charpoly_coeff]
    exact neg_mem (h_coeff _ _)
  · -- With `ρ z₀ = δ` and `z₀ ∈ I`, the element `ρ₁ (z₀ P(ρ₀))` of `𝔞` has trace `δ tr (ρ₁ P(ρ₀))`.
    refine ⟨ρ₁ * (z₀ * aeval ρ₀ P), 𝔞.mul_mem_left _ _ (h_mem _ hz₀), ?_⟩
    have h_prod : ρ (ρ₁ * (z₀ * aeval ρ₀ P)) = δ • ρ (ρ₁ * aeval ρ₀ P) := by
      rw [map_mul ρ ρ₁, map_mul ρ z₀, hz₀_eq, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
        one_mul, mul_smul_comm, ← map_mul ρ ρ₁ (aeval ρ₀ P)]
    rw [h_prod, trace_smul, Algebra.smul_def]

/-- Let `u x` (`x : Y`) be representations of `O[G]` such that the coefficients of the
characteristic polynomials of the group elements, as functions `Y → L` of `x`, lie in the subalgebra
`S`, and let `κ : O → S` send an element of `O` to the constant function. Then the family lifts to
an `S`-algebra map `ρ` from `S[G]` to matrices over `Y → L` which (a) is `u x` at the point `x` on
elements coming from `O[G]`, and (b) has all its characteristic polynomials with coefficients in
`S` (Amitsur's formula passes from the group elements to their span). -/
lemma exists_family_algHom_charpoly_mem (u : Y → O[G] →ₐ[O] Matrix σ σ O)
    (κ : O →+* S) (hκ : (algebraMap S (Y → L)).comp κ = algebraMap O (Y → L))
    (h_coeff : ∀ (g : G) (k : ℕ),
      (fun x : Y ↦ ((u x (.single g 1)).map (algebraMap O L)).charpoly.coeff k) ∈ S) :
    ∃ ρ : S[G] →ₐ[S] Matrix σ σ (Y → L),
      -- (a)
      (∀ (x : Y) (r : O[G]) (i j : σ), ρ (mapRingHom G κ r) i j x = algebraMap O L (u x r i j)) ∧
      -- (b)
      ∀ (a : S[G]) (k : ℕ), (ρ a).charpoly.coeff k ∈ (algebraMap S (Y → L)).range := by
  let uL (x : Y) : G →* Matrix σ σ L :=
    (lift O (Matrix σ σ L) G).symm ((ofId O L).mapMatrix.comp (u x))
  let ρ : S[G] →ₐ[S] Matrix σ σ (Y → L) :=
    lift S (Matrix σ σ (Y → L)) G (piRingEquiv.symm.toMonoidHom.comp (.pi uL))
  have hρ (x : Y) (g : G) (i j : σ) :
      ρ (.single g 1) i j x = algebraMap O L (u x (.single g 1) i j) := by
    simp [ρ, uL]
  have hκ_apply (c : O) (x : Y) : (κ c : Y → L) x = algebraMap O L c :=
    congrFun (RingHom.congr_fun hκ c) x
  refine ⟨ρ, fun x r i j ↦ ?_, amitsur_charpoly_mem_of_span ρ ?_⟩
  · induction r using induction_on with
    | of g => simpa using hρ x g i j
    | add r r' hr hr' => simp [hr, hr']
    | smul c r hr =>
      have h_smul : mapRingHom G κ (c • r) = κ c • mapRingHom G κ r := by
        ext g
        simp
      simp [h_smul, S.smul_def, hκ_apply, hr]
  · -- The group elements span `S[G]`.
    refine eq_top_mono (span_mono ?_) (basis G S).span_eq
    rintro _ ⟨g, rfl⟩ k
    refine ⟨⟨_, h_coeff g k⟩, funext fun x ↦ ?_⟩
    have h_eval : (u x (.single g 1)).map (algebraMap O L) =
        (ρ (.single g 1)).map (Pi.evalRingHom (fun _ ↦ L) x) := by
      ext i j
      exact (hρ x g i j).symm
    change ((u x (.single g 1)).map (algebraMap O L)).charpoly.coeff k =
      (ρ (.single g 1)).charpoly.coeff k x
    rw [h_eval, charpoly_map, Polynomial.coeff_map, Pi.evalRingHom_apply]

/-- Suppose that every matrix `χ c` is, after reindexing along `blockEquiv`, the block `ψ c` plus
the diagonal matrix of the `η e c`. Then the determinant of a matrix `M` over `A`, read through `χ`
as a block matrix, is the product of its determinants through `ψ` and through the `η e`. -/
lemma Selmer.det_comp_map_eq_mul_prod {R A ι r : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    [Fintype r] [DecidableEq r] {t : ℕ} (blockEquiv : r ⊕ Fin t ≃ σ) {χ : A → Matrix σ σ R}
    {ψ : A → Matrix r r R} {η : Fin t → A → R}
    (hχ : ∀ c : A, χ c = reindex blockEquiv blockEquiv
      (fromBlocks (ψ c) 0 0 (diagonal fun e : Fin t ↦ η e c)))
    (M : Matrix ι ι A) :
    (Matrix.comp ι ι σ σ R (M.map χ)).det =
      (Matrix.comp ι ι r r R (M.map ψ)).det * ∏ e : Fin t, (M.map (η e)).det := by
  let blockEquiv' : ι × r ⊕ ι × Fin t ≃ ι × σ :=
    (Equiv.prodSumDistrib ι r (Fin t)).symm.trans (.prodCongr (.refl ι) blockEquiv)
  have h_blocks : (Matrix.comp ι ι σ σ R (M.map χ)).submatrix blockEquiv' blockEquiv' =
      fromBlocks (Matrix.comp ι ι r r R (M.map ψ)) 0 0 (blockDiagonal fun e ↦ M.map (η e)) := by
    ext1 (a | a) (b | b) <;> simp [blockEquiv', hχ, blockDiagonal, diagonal]
  rw [← det_submatrix_equiv_self blockEquiv', h_blocks, det_fromBlocks_zero₂₁, det_blockDiagonal]

/-- Let `u x` (`x : Y`) be representations of `O[G]`, and let `κ : O → S` send an element of `O` to
the constant function. If the coefficients of the characteristic polynomials of the group elements,
as functions `Y → L` of `x`, lie in the subalgebra `S`, then so does the determinant of every
`w : O[G]`. -/
lemma Selmer.det_mem_of_coeff_mem (u : Y → O[G] →ₐ[O] Matrix σ σ O) (κ : O →+* S)
    (hκ : (algebraMap S (Y → L)).comp κ = algebraMap O (Y → L))
    (h_coeff : ∀ (g : G) (k : ℕ),
      (fun x : Y ↦ ((u x (.single g 1)).map (algebraMap O L)).charpoly.coeff k) ∈ S)
    (w : O[G]) :
    (fun x : Y ↦ algebraMap O L (u x w).det) ∈ S := by
  -- The determinant of the lift `ρ` to `S[G]` lies in `S`, like its characteristic polynomials.
  obtain ⟨ρ, hρ, h_charpoly⟩ : ∃ ρ : S[G] →ₐ[S] Matrix σ σ (Y → L),
      (∀ (x : Y) (r : O[G]) (i j : σ), ρ (mapRingHom G κ r) i j x = algebraMap O L (u x r i j)) ∧
      ∀ (a : S[G]) (k : ℕ), (ρ a).charpoly.coeff k ∈ (algebraMap S (Y → L)).range :=
    exists_family_algHom_charpoly_mem u κ hκ h_coeff
  have h_det : (fun x : Y ↦ algebraMap O L (u x w).det) = (ρ (mapRingHom G κ w)).det := by
    ext x
    simp [hρ, det_apply']
  obtain ⟨-, D, hD, -, -⟩ := exists_adjugate_of_charpoly_mem ρ h_charpoly (mapRingHom G κ w)
  rw [h_det, hD, S.algebraMap_apply]
  exact D.property

/-- The elements of `Λ` whose traces against every element of `Λ`, through `ρ`, lie in `𝒥`. They
form a two-sided ideal, as traces are cyclic. -/
def Selmer.traceIdeal (ρ : Λ →ₐ[R] Matrix σ σ L) (𝒥 : Submodule R L) : TwoSidedIdeal Λ :=
  .mk' {w | ∀ s : Λ, (ρ (w * s)).trace ∈ 𝒥}
    (fun s ↦ by simp)
    (fun hw hw' s ↦ by simpa [add_mul] using add_mem (hw s) (hw' s))
    (fun hw s ↦ by simpa [neg_mul] using neg_mem (hw s))
    (fun {w w'} hw' s ↦ by simpa [mul_assoc, trace_mul_comm (ρ w)] using hw' (s * w))
    (fun {w w'} hw s ↦ by simpa [mul_assoc] using hw (w' * s))

/-- An element `w` lies in `traceIdeal ρ 𝒥` if and only if the traces of all `ρ (w s)` lie in
`𝒥`. -/
lemma Selmer.mem_traceIdeal {ρ : Λ →ₐ[R] Matrix σ σ L} {𝒥 : Submodule R L} {w : Λ} :
    w ∈ Selmer.traceIdeal ρ 𝒥 ↔ ∀ s : Λ, (ρ (w * s)).trace ∈ 𝒥 := by
  rw [Selmer.traceIdeal, TwoSidedIdeal.mem_mk', Set.mem_ofPred_eq]

/-- Let `u x` (`x : Y`) be representations of `O[G]`, and let `ρ` be a representation of `S[G]` over
`Y → L` that is `u x` at the point `x` on elements coming from `O[G]` along `κ`. If `r` lies in the
left ideal spanned by the `w` such that the trace of `u x (w g)`, as a function of `x`, lies in `𝒥`
for every group element `g`, then the trace of `ρ (b r)` lies in `𝒥` for every `b : S[G]`. -/
lemma Selmer.trace_mul_mem_of_mem_span (u : Y → O[G] →ₐ[O] Matrix σ σ O) (κ : O →+* S)
    (ρ : S[G] →ₐ[S] Matrix σ σ (Y → L))
    (hρ : ∀ (x : Y) (r : O[G]) (i j : σ), ρ (mapRingHom G κ r) i j x = algebraMap O L (u x r i j))
    (𝒥 : Submodule S (Y → L)) {r : O[G]}
    (hr : r ∈ span O[G] {w : O[G] | ∀ g : G,
      (fun x : Y ↦ algebraMap O L (u x w * u x (.single g 1)).trace) ∈ 𝒥})
    (b : S[G]) :
    (ρ (b * mapRingHom G κ r)).trace ∈ 𝒥 := by
  induction hr using span_induction generalizing b with
  | mem r hr =>
    induction b using induction_on with
    | of g =>
      have h_trace : (ρ (MonoidAlgebra.of S G g * mapRingHom G κ r)).trace =
          fun x : Y ↦ algebraMap O L (u x r * u x (.single g 1)).trace := by
        ext x
        rw [trace_mul_comm (u x r)]
        simp [← hρ, Matrix.trace, Matrix.mul_apply]
      rw [h_trace]
      exact hr g
    | add b b' hb hb' => simpa [add_mul] using add_mem hb hb'
    | smul c b hb => simpa using 𝒥.smul_mem c hb
  | zero => simp
  | add r r' _ _ hr hr' => simpa [mul_add] using add_mem (hr b) (hr' b)
  | smul s r _ hr => simpa [mul_assoc] using hr (b * mapRingHom G κ s)

/-- Where `ρ₁ ρ₀` acts as `0`, `ρ₁ P(ρ₀)` acts as `P(0) ρ₁`: at a point `x` where every entry of
`ρ (ρ₁ ρ₀)` vanishes, the trace of `ρ (ρ₁ P(ρ₀))` is `P(0)` times the trace of `ρ ρ₁`. -/
lemma Selmer.trace_mul_aeval_apply (ρ : S[G] →ₐ[S] Matrix σ σ (Y → L)) (ρ₀ ρ₁ : S[G]) (P : S[X])
    (x : Y) (h_zero : ∀ i j : σ, ρ (ρ₁ * ρ₀) i j x = 0) :
    (ρ (ρ₁ * aeval ρ₀ P)).trace x = (P.coeff 0 : Y → L) x * (ρ ρ₁).trace x := by
  have h_split : ρ₁ * aeval ρ₀ P = ρ₁ * ρ₀ * aeval ρ₀ P.divX + P.coeff 0 • ρ₁ := by
    conv_lhs => rw [← P.X_mul_divX_add]
    rw [aeval_add, aeval_mul, aeval_X, aeval_C, mul_add, mul_assoc, Algebra.smul_def,
      Algebra.commutes]
  have h_vanish : (ρ (ρ₁ * ρ₀) * ρ (aeval ρ₀ P.divX)).trace x = 0 := by
    simp only [Matrix.trace, diag_apply, Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply, h_zero,
      zero_mul, sum_const_zero]
  rw [h_split, map_add, map_mul ρ (ρ₁ * ρ₀), map_smul, trace_add, trace_smul, Pi.add_apply,
    h_vanish, zero_add, S.smul_def, smul_eq_mul, Pi.mul_apply]

/-- Cayley–Hamilton for a family. Map `O[G]` to `S[G]` along `κ : O → S`. Let `ρ` be a
representation of `S[G]` over `Y → L` that is `u x` on `O[G]` at each point `x` and has its
characteristic polynomials over `S`. Then for `w : O[G]` the function `x ↦ det (u x w)` is an
element `D` of `S`, and `ρ` sends some left multiple of `w` to the scalar matrix `D`. -/
lemma Selmer.exists_mul_eq_algebraMap_det (u : Y → O[G] →ₐ[O] Matrix σ σ O) (κ : O →+* S)
    (ρ : S[G] →ₐ[S] Matrix σ σ (Y → L))
    (hρ : ∀ (x : Y) (r : O[G]) (i j : σ), ρ (mapRingHom G κ r) i j x = algebraMap O L (u x r i j))
    (h_charpoly : ∀ (a : S[G]) (k : ℕ), (ρ a).charpoly.coeff k ∈ (algebraMap S (Y → L)).range)
    (w : O[G]) :
    ∃ D : S, ((D : Y → L) = fun x : Y ↦ algebraMap O L (u x w).det) ∧
      ∃ v : S[G], ρ (v * mapRingHom G κ w) = algebraMap S (Matrix σ σ (Y → L)) D := by
  obtain ⟨v, D, hD, hv, -⟩ : ∃ (v : S[G]) (D : S),
      (ρ (mapRingHom G κ w)).det = algebraMap S (Y → L) D ∧
      ρ v * ρ (mapRingHom G κ w) = D • 1 ∧ ρ (mapRingHom G κ w) * ρ v = D • 1 :=
    exists_adjugate_of_charpoly_mem ρ h_charpoly (mapRingHom G κ w)
  refine ⟨D, funext fun x ↦ ?_, v, ?_⟩
  · simpa [hρ, det_apply'] using (congrFun hD x).symm
  · rw [map_mul, hv, Algebra.algebraMap_eq_smul_one]

/-- A ring homomorphism `f` sends the left ideal spanned by the `y i` into the left ideal spanned by
the `f (y i)`. -/
lemma Selmer.map_mem_span_range {A B ι : Type*} [Ring A] [Ring B] [Fintype ι] (f : A →+* B)
    (y : ι → A) {w : A} (hw : w ∈ span A (Set.range y)) :
    f w ∈ span B (Set.range (f ∘ y)) := by
  obtain ⟨c, rfl⟩ : ∃ c : ι → A, ∑ i : ι, c i • y i = w := (mem_span_range_iff_exists_fun A).1 hw
  rw [map_sum]
  refine sum_mem fun i _ ↦ ?_
  rw [smul_eq_mul, map_mul]
  exact smul_mem _ (f (c i)) (subset_span ⟨i, rfl⟩)

/-- Let `χ` be, after reindexing by `blockEquiv`, the block sum of `ψ` and the characters `η e`. If
`ρ₁` vanishes under `ψ` and under every character but `η 0`, and `ρ₀` vanishes under `η 0`, then
`χ (ρ₁ ρ₀) = 0`. -/
lemma Selmer.map_mul_eq_zero_of_blocks {A r : Type*} [Ring A] [Algebra O A] [Fintype r]
    [DecidableEq r] {t : ℕ} [NeZero t] (blockEquiv : r ⊕ Fin t ≃ σ) (χ : A →ₐ[O] Matrix σ σ O)
    (ψ : A →ₐ[O] Matrix r r O) (η : Fin t → A →ₐ[O] O)
    (hχ : ∀ w : A, χ w = reindex blockEquiv blockEquiv
      (fromBlocks (ψ w) 0 0 (diagonal fun e : Fin t ↦ η e w)))
    {ρ₀ ρ₁ : A} {μ₀ : O} (hψ₁ : ψ ρ₁ = 0) (hη₁ : ∀ e : Fin t, η e ρ₁ = if e = 0 then μ₀ else 0)
    (hη₀ : η 0 ρ₀ = 0) :
    χ (ρ₁ * ρ₀) = 0 := by
  have h_η (e : Fin t) : η e (ρ₁ * ρ₀) = 0 := by
    rw [map_mul, hη₁]
    split_ifs with he
    · rw [he, hη₀, mul_zero]
    · rw [zero_mul]
  have h_ψ : ψ (ρ₁ * ρ₀) = 0 := by rw [map_mul, hψ₁, zero_mul]
  simp only [hχ, h_ψ, h_η, diagonal_zero, fromBlocks_zero, reindex_apply, submatrix_zero,
    Pi.zero_apply]

/-- Ribet's element for a matrix of tied rows. Let `u x` (`x : Y`) be representations of `O[G]`, and
let `S` be an algebra of functions `Y → L` that contains the constants from `O` and, as functions of
`x`, the coefficients of the characteristic polynomials of the group elements. Let `𝒥` be an
`S`-module of functions `Y → L`, `I` the left ideal spanned by `y`, and `𝔞` the left ideal spanned
by the elements whose traces against every group element lie in `𝒥`. Let `B` be a square matrix,
indexed like `y` by the finite type `N`, of tied rows: the entries of `B y` lie in `𝔞 + I ρ₀`.
Suppose that for `x ∈ 𝓧`, `u x` is, after reindexing along `blockEquiv`, the block `ψ x` plus the
characters `η e`, that `ρ₁` is `μ₀` on `η 0` and zero on the other summands, and that `ρ₀` is zero
on `η 0`. Then one `f : S` multiplies `det (u x w)` into `𝒥` for every `w ∈ I`, and its value at
`x ∈ 𝓧` is `μ₀ det (ψ x B) ∏ det (η e B)`. -/
lemma Selmer.exists_ribet_element_of_tied_rows {r : Type*} [Fintype r] [DecidableEq r] {t : ℕ}
    [NeZero t] (blockEquiv : r ⊕ Fin t ≃ σ) (u : Y → O[G] →ₐ[O] Matrix σ σ O) (κ : O →+* S)
    (hκ : (algebraMap S (Y → L)).comp κ = algebraMap O (Y → L))
    (h_coeff : ∀ (g : G) (k : ℕ),
      (fun x : Y ↦ ((u x (.single g 1)).map (algebraMap O L)).charpoly.coeff k) ∈ S)
    (𝒥 : Submodule S (Y → L)) (y : N → O[G]) (ρ₀ ρ₁ : O[G]) (B : Matrix N N O[G])
    (hB_tied : ∀ i : N,
      ∃ a ∈ span O[G] {w : O[G] | ∀ g : G,
        (fun x : Y ↦ algebraMap O L (u x w * u x (.single g 1)).trace) ∈ 𝒥},
      ∃ z ∈ span O[G] (Set.range y), (B *ᵥ y) i = a + z * ρ₀)
    {𝓧 : Set Y} (ψ : 𝓧 → O[G] →ₐ[O] Matrix r r O) (η : Fin t → O[G] →ₐ[O] O)
    (hu_block : ∀ (x : 𝓧) (w : O[G]),
      u x w = reindex blockEquiv blockEquiv
        (fromBlocks (ψ x w) 0 0 (diagonal fun e : Fin t ↦ η e w)))
    (hψ₁ : ∀ x : 𝓧, ψ x ρ₁ = 0) {μ₀ : O} (hη₁ : ∀ e : Fin t, η e ρ₁ = if e = 0 then μ₀ else 0)
    (hη₀ : η 0 ρ₀ = 0) :
    ∃ f : S,
      (∀ w ∈ span O[G] (Set.range y),
        (f : Y → L) * (fun x : Y ↦ algebraMap O L (u x w).det) ∈ 𝒥) ∧
      ∀ x : 𝓧, (f : Y → L) x = algebraMap O L
        (μ₀ * (comp N N r r O (B.map (ψ x))).det * ∏ e : Fin t, (B.map (η e)).det) := by
  -- Lift `u` to one representation `ρ` of `S[G]` and apply Ribet's method with the two-sided ideal
  -- `𝔞` of the elements whose traces against all of `S[G]` lie in `𝒥`; take `f = tr ρ (ρ₁ P(ρ₀))`.
  have : Nonempty σ := blockEquiv.symm.nonempty
  let ι : O[G] →+* S[G] := mapRingHom G κ
  obtain ⟨ρ, hρι, h_charpoly⟩ : ∃ ρ : S[G] →ₐ[S] Matrix σ σ (Y → L),
      (∀ (x : Y) (r : O[G]) (i j : σ), ρ (ι r) i j x = algebraMap O L (u x r i j)) ∧
      ∀ (a : S[G]) (k : ℕ), (ρ a).charpoly.coeff k ∈ (algebraMap S (Y → L)).range :=
    exists_family_algHom_charpoly_mem u κ hκ h_coeff
  let 𝔞 : TwoSidedIdeal S[G] := Selmer.traceIdeal ρ 𝒥
  have mem_𝔞 (w : S[G]) : w ∈ 𝔞 ↔ ∀ s : S[G], (ρ (w * s)).trace ∈ 𝒥 := Selmer.mem_traceIdeal
  have h_span (w : O[G]) (hw : w ∈ span O[G] (Set.range y)) :
      ι w ∈ span S[G] (Set.range (ι ∘ y)) :=
    Selmer.map_mem_span_range ι y hw
  have h_rows (i : N) : ∃ a ∈ 𝔞, ∃ z ∈ span S[G] (Set.range (ι ∘ y)),
      (B.map ι *ᵥ ι ∘ y) i = a + z * ι ρ₀ := by
    obtain ⟨a, ha, z, hz, h_eq⟩ := hB_tied i
    have h_a : ι a ∈ 𝔞 := (mem_𝔞 _).2 fun s ↦ by
      rw [map_mul, trace_mul_comm, ← map_mul]
      exact Selmer.trace_mul_mem_of_mem_span u κ ρ hρι 𝒥 ha s
    refine ⟨ι a, h_a, ι z, h_span z hz, ?_⟩
    rw [← map_mul, ← map_add, ← h_eq]
    simp [mulVec, dotProduct]
  have h_top : span S {w : S[G] | ∀ k : ℕ,
      (ρ w).charpoly.coeff k ∈ (algebraMap S (Y → L)).range} = ⊤ :=
    top_unique fun w _ ↦ subset_span (h_charpoly w)
  have h_ker (w : S[G]) (hw : ρ w = 0) : w ∈ 𝔞 := (mem_𝔞 w).2 fun s ↦ by simp [hw]
  obtain ⟨P, hP, -, h_tr, h_δ⟩ : ∃ P : S[X],
      algebraMap S (Y → L) (P.eval 0) = (comp N N σ σ (Y → L) ((B.map ι).map ρ)).det ∧
      (∀ z ∈ span S[G] (Set.range (ι ∘ y)), z * aeval (ι ρ₀) P ∈ 𝔞) ∧
      (∀ c : S[G], (ρ (c * aeval (ι ρ₀) P)).trace ∈ (algebraMap S (Y → L)).range) ∧
      ∀ (c : S[G]) (δ : S),
        (∃ z ∈ span S[G] (Set.range (ι ∘ y)), ρ z = algebraMap S (Matrix σ σ (Y → L)) δ) →
        ∃ a ∈ 𝔞, algebraMap S (Y → L) δ * (ρ (c * aeval (ι ρ₀) P)).trace = (ρ a).trace :=
    Selmer.exists_ribet_polynomial ρ h_top 𝔞 h_ker (ι ∘ y) (ι ρ₀) (B.map ι) h_rows
  obtain ⟨f, hf⟩ : ∃ f : S, (f : Y → L) = (ρ (ι ρ₁ * aeval (ι ρ₀) P)).trace := h_tr (ι ρ₁)
  refine ⟨f, fun w hw ↦ ?_, fun x ↦ ?_⟩
  · -- `det (u x w)` is an element `D` of `S`, and the scalar matrix `D` is `ρ (v * ι w)` with
    -- `v * ι w` in the left ideal spanned by `ι ∘ y`. So `D f` is the trace of an element of `𝔞`.
    obtain ⟨D, hD, v, hv⟩ := Selmer.exists_mul_eq_algebraMap_det u κ ρ hρι h_charpoly w
    obtain ⟨b, hb, hb_eq⟩ :
        ∃ b ∈ 𝔞, (D : Y → L) * (ρ (ι ρ₁ * aeval (ι ρ₀) P)).trace = (ρ b).trace :=
      h_δ (ι ρ₁) D ⟨v * ι w, smul_mem _ v (h_span w hw), hv⟩
    rw [← hD, mul_comm, hf, hb_eq, ← mul_one b]
    exact (mem_𝔞 b).1 hb 1
  · -- At `x ∈ 𝓧`, `ρ₁ ρ₀` acts as `0`, so `f` is `P(0) tr ρ₁` there.
    have h_zero : u x (ρ₁ * ρ₀) = 0 :=
      Selmer.map_mul_eq_zero_of_blocks blockEquiv (u x) (ψ x) η (hu_block x) (hψ₁ x) hη₁ hη₀
    have h_zero_x (i k : σ) : ρ (ι ρ₁ * ι ρ₀) i k x = 0 := by
      rw [← map_mul, hρι, h_zero, Matrix.zero_apply, map_zero]
    have h_value : (f : Y → L) x = (P.coeff 0 : Y → L) x * algebraMap O L (u x ρ₁).trace := by
      rw [hf, Selmer.trace_mul_aeval_apply ρ (ι ρ₀) (ι ρ₁) P x h_zero_x]
      simp [Matrix.trace, Finset.sum_apply, hρι]
    have h_coeff0 :
        (P.coeff 0 : Y → L) x = algebraMap O L (comp N N σ σ O (B.map (u x))).det := by
      simpa [hρι, coeff_zero_eq_eval_zero, det_apply'] using congrFun hP x
    have h_μ : (u x ρ₁).trace = μ₀ := by
      simp [hu_block, hψ₁, hη₁, Matrix.trace, ← blockEquiv.sum_comp, Fintype.sum_sum_type]
    have h_det : (comp N N σ σ O (B.map (u x))).det =
        (comp N N r r O (B.map (ψ x))).det * ∏ e : Fin t, (B.map (η e)).det :=
      Selmer.det_comp_map_eq_mul_prod blockEquiv (hu_block x) B
    rw [h_value, h_coeff0, h_μ, h_det, ← map_mul, mul_comm, mul_assoc]

end New
