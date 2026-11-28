import Lib.Adelic.Witt.WittTheorem

/-!
# Hermite forms over valuation pairs and integral matrices over valued fields

We reduce the columns and rows of matrices over a ring `A` by invertible matrices over a subring
`R`, under the hypothesis `New.IsValuationPair`. It says that any two elements `a, b` of `A` are
`R`-multiples of `a - e * (a - b)` for some idempotent `e` of `R`. It holds for a valuation domain
`A` with `R = ⊤`. For a field with a valuation into `ℤᵐ⁰`, we bound the entries of matrix products
and give a determinant test for integral invertible matrices.

## Main definitions and results

* `New.IsValuationPair.hermite`: Hermite form `y = U_ι * D` with `U ∈ GL_n(R)`, `D` block
  triangular.
* `New.IsValuationPair.exists_isPrimitiveMatrix_mul`: a matrix with a left inverse becomes primitive
  (`New.IsPrimitiveMatrix`) after multiplication by an invertible block triangular matrix.
* `New.IsValuationPair.exists_mul_clear_cols`: the transposed form, clearing the columns outside
  the image of `ι`.
* `New.mem_intGL_iff_det`: `g` lies in `New.intGL n 𝒪[F]` (the image of `GL n 𝒪[F]` in `GL n F`) iff
  its entries are integral and `v (det g) = 1`.

Notions from other files:
* `New.intGL n R`: the subgroup `GL_n(R)` of `GL_n(A)` of matrices that have their entries and
  those of their inverse in the subring `R`.
* `New.transvectionGL`: for distinct indices `i, j` and `a` in `A`, the element `1 + aE_{ij}` of
  `GL_n(A)`, with inverse `1 − aE_{ij}`.
* `New.IsPrimitiveMatrix R X`: `X` has entries in `R` and a left inverse with entries in `R`.

## Relation to the literature

The property `New.IsValuationPair` and the Smith normal form are in
`Lib.General.LinearAlgebra.IntegralLattices`.
-/

/-!
## Hermite forms over valuation pairs

`New.intGL` is `GL_n(R)` inside `GL_n(A)`; `wt` orders the columns, and an embedding `ι` picks the
pivot row of each column.
-/

section Hermite

open Matrix Finset ValuationRing

namespace New

variable {A n k : Type*} [CommRing A] {R : Subring A} [Fintype n] [DecidableEq n]

/-- The transvection `1 + a E_{ij}` with `a` in the subring `R` lies in `GL_n(R)`. -/
lemma transvectionGL_mem_intGL {i j : n} {a : A} (hij : i ≠ j) (ha : a ∈ R) :
    transvectionGL hij a ∈ intGL n R := by
  -- the entries of `1 ± a E_{ij}` are `0`, `1` or `±a`
  refine mem_intGL.2 ⟨fun r c ↦ ?_, fun r c ↦ ?_⟩ <;>
    aesop (add simp [one_apply, single, transvection, transvectionGL])

/-- A valuation domain `A` with the subring `R = ⊤` is a valuation pair: any two elements `a`, `b`
are multiples of `a - e * (a - b)` for some idempotent `e`. -/
lemma isValuationPair_top [IsDomain A] [ValuationRing A] : IsValuationPair (⊤ : Subring A) := by
  intro a b
  obtain ⟨c, rfl⟩ | ⟨c, rfl⟩ := dvd_total a b
  · -- if `a ∣ b`, take `e = 0`: both elements are multiples of `a`
    exact ⟨0, by simp, by simp [Submodule.mem_span_singleton, Subring.smul_def, mul_comm a]⟩
  · -- if `b ∣ a`, take `e = 1`: both elements are multiples of `b`
    exact ⟨1, by simp, by simp [Submodule.mem_span_singleton, Subring.smul_def, mul_comm b]⟩

/-- Let `(A, R)` be a valuation pair: any `u, v` in `A` are `R`-multiples of `u - e * (u - v)` for
some idempotent `e` of `R`. For rows `i₀ ≠ i` of a matrix `y` over `A` and a column `a`, some `W`
in `GL_n(R)` makes the entry `(i, a)` of `W * y` zero, changes no row other
than `i₀` and `i`, and changes no column in which both rows vanish. -/
lemma IsValuationPair.exists_row_op (hR : IsValuationPair R) {i₀ i : n} (hne : i₀ ≠ i)
    (y : Matrix n k A) (a : k) :
    ∃ W ∈ intGL n R,
      (W.val * y) i a = 0 ∧
      (∀ (r : n) (j : k), r ≠ i₀ → r ≠ i → (W.val * y) r j = y r j) ∧
      ∀ (r : n) (j : k), y i₀ j = 0 → y i j = 0 → (W.val * y) r j = y r j := by
  -- both entries are multiples of the combination `g = y i₀ a - e * (y i₀ a - y i a)`
  obtain ⟨e, e_idem, ⟨x, hx, y₀_eq⟩, he, z, hz, y_eq⟩ :
      ∃ e : A, e * e = e ∧ (∃ x ∈ R, y i₀ a = (y i₀ a - e * (y i₀ a - y i a)) * x) ∧ e ∈ R ∧
        ∃ z ∈ R, y i a = (y i₀ a - e * (y i₀ a - y i a)) * z := by
    simpa using hR (y i₀ a) (y i a)
  -- adding `e - e * x` times row `i` puts `g` at `(i₀, a)`; then subtract `z` times row `i₀`
  let W : GL n A := transvectionGL hne.symm (-z) * transvectionGL hne (e - e * x)
  have g_eq : y i₀ a + (e - e * x) * y i a = y i₀ a - e * (y i₀ a - y i a) := by
    linear_combination e * y₀_eq - x * (y i₀ a - y i a) * e_idem
  have row_i₀ (j : k) : (W.val * y) i₀ j = y i₀ j + (e - e * x) * y i j := by
    simp [W, Matrix.mul_assoc, hne]
  have row_i (j : k) : (W.val * y) i j = y i j - z * (y i₀ j + (e - e * x) * y i j) := by
    simp [W, Matrix.mul_assoc, hne.symm, sub_eq_add_neg]
  have other_rows (r : n) (j : k) (hr₀ : r ≠ i₀) (hr : r ≠ i) : (W.val * y) r j = y r j := by
    simp [W, Matrix.mul_assoc, hr₀, hr]
  refine ⟨W, mul_mem (transvectionGL_mem_intGL _ (neg_mem hz))
    (transvectionGL_mem_intGL _ (sub_mem he (mul_mem he hx))), ?_, other_rows, fun r j _ _ ↦ ?_⟩
  · linear_combination row_i a + y_eq - z * g_eq
  · -- `r` is `i`, `i₀` or neither: each new entry is then the old one
    grind [eq_or_ne r i, eq_or_ne r i₀]

/-- Let `(A, R)` be a valuation pair (any `u, v` in `A` are `R`-multiples of `u - e * (u - v)` for
some idempotent `e` of `R`). For a matrix `y` over `A`, a column `a`, a row `i₀` and a
finite set `t` of other rows, some `W` in `GL_n(R)` makes the entries of `W * y` in column `a` and
rows `t` zero, and changes no column in which `i₀` and all rows in `t` vanish. -/
lemma IsValuationPair.exists_clear_col (hR : IsValuationPair R) (y : Matrix n k A) (a : k)
    {i₀ : n} {t : Finset n} (hi₀ : i₀ ∉ t) :
    ∃ W ∈ intGL n R, (∀ i ∈ t, (W.val * y) i a = 0) ∧
      ∀ j : k, y i₀ j = 0 → (∀ i ∈ t, y i j = 0) → ∀ r : n, (W.val * y) r j = y r j := by
  induction t using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by simp, by simp⟩
  | insert i t hi ih =>
    obtain ⟨hne, hi₀⟩ : i₀ ≠ i ∧ i₀ ∉ t := by simpa using hi₀
    obtain ⟨W, hW, W_zero, W_keep⟩ := ih hi₀
    obtain ⟨V, hV, V_zero, V_other, V_keep⟩ := hR.exists_row_op hne (W.val * y) a
    refine ⟨V * W, mul_mem hV hW, fun r hr ↦ ?_, fun j hj₀ hjt r ↦ ?_⟩ <;>
      rw [Units.val_mul, Matrix.mul_assoc]
    · -- row `i` is cleared by `V`; the rows in `t` are cleared by `W` and kept by `V`
      obtain rfl | hrt := mem_insert.1 hr
      · exact V_zero
      · rw [V_other r a (ne_of_mem_of_not_mem hrt hi₀) (ne_of_mem_of_not_mem hrt hi), W_zero r hrt]
    · -- `W` keeps column `j`, hence so does `V`
      obtain ⟨hji, hjt⟩ : y i j = 0 ∧ ∀ r ∈ t, y r j = 0 := by simpa using hjt
      have W_col : ∀ r : n, (W.val * y) r j = y r j := W_keep j hj₀ hjt
      rw [V_keep r j ((W_col i₀).trans hj₀) ((W_col i).trans hji), W_col]

variable [Fintype k]

/-- Hermite form: let `(A, R)` be a valuation pair (any `u, v` in `A` are `R`-multiples of
`u - e * (u - v)` for some idempotent `e` of `R`), and let `ι` embed `k` in `n`.
Then an `n × k` matrix `y` over `A` is `U_ι * D` with `U ∈ GL_n(R)` and `U_ι` its columns at `ι`.
Here `D` is the rows at `ι` of `U⁻¹ * y`, and it is block upper triangular for the weight `wt`. -/
lemma IsValuationPair.hermite (hR : IsValuationPair R) (ι : k ↪ n) (y : Matrix n k A)
    (wt : k → ℕ := 0) :
    ∃ᵉ (U ∈ intGL n R) (D : Matrix k k A),
      -- (a) `D` is block triangular for the weight
      D.BlockTriangular wt ∧
      -- (b) `y` is the product of the columns `ι` of `U` with `D`
      y = U.val.submatrix id ι * D ∧
      -- (c) `D` consists of the rows `ι` of `U⁻¹ * y`
      U⁻¹.val.submatrix ι id * y = D := by
  classical
  -- Treat the columns in order of increasing weight. In each column `j ∈ s` of a reduced `U * y`,
  -- only the rows `ι b` with `b ∈ s` and `wt b ≤ wt j` may be non-zero.
  let IsReduced (s : Finset k) (U : GL n A) : Prop :=
    ∀ j ∈ s, ∀ i : n, (∀ b ∈ s, i = ι b → wt j < wt b) → (U.1 * y) i j = 0
  have exists_reduced (s : Finset k) : ∃ U ∈ intGL n R, IsReduced s U := by
    induction s using Finset.induction_on_max_value wt with
    | empty => exact ⟨1, one_mem _, by simp [IsReduced]⟩
    | insert a s ha hmax ih =>
      obtain ⟨U, hU, hs⟩ := ih
      -- in the new column `a`, clear the rows outside `ι (insert a s)`
      obtain ⟨W, hW, hcol, hkeep⟩ := hR.exists_clear_col (U.1 * y) a (i₀ := ι a)
        (t := ((insert a s).map ι)ᶜ) (by simp)
      -- these rows and `ι a` vanish in the columns of `s`, so these columns do not change
      have s_cols : ∀ j ∈ s, ∀ r : n, (W.1 * (U.1 * y)) r j = (U.1 * y) r j := by grind [mem_compl]
      refine ⟨W * U, mul_mem hW hU, fun j hj r hr ↦ ?_⟩
      rw [Units.val_mul, Matrix.mul_assoc]
      obtain rfl | hjs := mem_insert.1 hj
      · -- as `wt j` is maximal, `r` is not in `ι (insert j s)`
        exact hcol r (by grind [mem_compl])
      · exact (s_cols j hjs r).trans (hs j hjs r (by grind))
  obtain ⟨U, hU, hzero⟩ := exists_reduced univ
  refine ⟨U⁻¹, inv_mem hU, (U.1 * y).submatrix ι id,
    fun i j hij ↦ hzero j (mem_univ j) (ι i) (by simpa), ?_, rfl⟩
  -- only the rows at `ι` of `U * y` contribute to the product `y = U⁻¹ * (U * y)`
  have hrows (i : n) (hi : i ∉ Set.range ι) (j : k) : (U.1 * y) i j = 0 :=
    hzero j (mem_univ j) i (by grind)
  calc y = U⁻¹.1 * (U.1 * y) := by simp [← Matrix.mul_assoc]
    _ = U⁻¹.1.submatrix id ι * (U.1 * y).submatrix ι id := ext fun i j ↦
      (Fintype.sum_of_injective ι ι.injective _ _ (by simp +contextual [hrows]) fun _ ↦ rfl).symm

/-- If (A, R) satisfies `New.IsValuationPair` (any u, v in A are R-multiples of u - e(u - v) for
some idempotent e of R) and the n × k matrix X over A has a left inverse, there is an invertible
b, block upper triangular for wt, such that X b has entries in R and a left inverse with entries
in R. -/
lemma IsValuationPair.exists_isPrimitiveMatrix_mul (hR : IsValuationPair R) [DecidableEq k]
    {X : Matrix n k A} (hX : HasLeftInv X) (wt : k → ℕ := 0) :
    ∃ b : GL k A, b.val.BlockTriangular wt ∧ IsPrimitiveMatrix R (X * b.val) := by
  -- Take the Hermite form of `X` with a zero block below it: `X = U₁₂ * D` for an integral `U`.
  -- `D` is invertible because `X` has a left inverse, so `X * D⁻¹ = U₁₂`; the zero block makes
  -- the lower left block of `U⁻¹` a left inverse of `U₁₂`.
  obtain ⟨L, hL⟩ := hX
  obtain ⟨U, hU, D, hD, (h_form : X.fromRows 0 = U.val.submatrix id Sum.inr * D),
    (h_inv : U⁻¹.val.submatrix Sum.inr id * X.fromRows 0 = D)⟩ :=
    hR.hermite .inr (X.fromRows 0) wt
  obtain rfl : X = U.1.toBlocks₁₂ * D :=
    ext fun i j ↦ by simpa [toBlocks₁₂, mul_apply] using congrFun₂ h_form (.inl i) j
  obtain ⟨b, rfl⟩ : IsUnit D := .of_mul_eq_one_right (L * U.1.toBlocks₁₂) (by rwa [L.mul_assoc])
  obtain ⟨hU_int, hU_inv_int⟩ := mem_intGL.1 hU
  refine ⟨b⁻¹, by simpa using blockTriangular_inv_of_blockTriangular hD,
    by simp [IsIntMatrix, toBlocks₁₂, hU_int], U⁻¹.1.toBlocks₂₁, fun i j ↦ hU_inv_int _ _, ?_⟩
  -- of the product in `h_inv` only the lower left block of `U⁻¹` meets a non-zero row
  have h_left : U⁻¹.1.toBlocks₂₁ * (U.1.toBlocks₁₂ * b.1) = b.1 :=
    ext fun i j ↦ by simpa [toBlocks₂₁, mul_apply] using congrFun₂ h_inv i j
  rw [← Matrix.mul_assoc, h_left, Units.mul_inv]

/-- Transposed Hermite form: if the subring R of A satisfies `New.IsValuationPair` (any u, v in A
are R-multiples of u - e(u - v) for some idempotent e of R), then for a k×n matrix M over A and an
injection ι: k → n, some V in GL_n(R) makes the columns of MV outside the image of ι vanish.

A weaker form of the Hermite normal form, without triangular shape, normalised pivots or
uniqueness. -/
lemma IsValuationPair.exists_mul_clear_cols (hR : IsValuationPair R) (M : Matrix k n A)
    (ι : k ↪ n) :
    ∃ V ∈ intGL n R, ∀ᵉ (a : k) (j ∉ Set.range ι), (M * V.val) a j = 0 := by
  -- The Hermite form of `Mᵀ` gives `U` such that `U⁻¹ * Mᵀ` vanishes off the rows `ι`; transpose.
  obtain ⟨U, hU, D, -, (h_form : Mᵀ = U.val.submatrix id ι * D), -⟩ := hR.hermite ι Mᵀ
  have h_rows : U⁻¹.1 * Mᵀ = (1 : Matrix n n A).submatrix id ι * D := by
    rw [h_form, ← Matrix.mul_assoc, ← U.inv_mul, submatrix_mul _ _ id id ι Function.bijective_id,
      submatrix_id_id]
  refine ⟨transposeGL U⁻¹, by simp_all [mem_intGL, transposeGL], fun a j hj ↦ ?_⟩
  have h_entry : ((1 : Matrix n n A).submatrix id ι * D) j a = 0 := by simp_all [mul_apply, ne_comm]
  simpa [mul_apply, mul_comm] using (congrFun₂ h_rows j a).trans h_entry

end New

end Hermite

/-!
## Integral invertible matrices

A fact on matrices over a field `F` with a valuation `v` into `ℤᵐ⁰`, written multiplicatively
(`v x ≤ 1` on the integers `𝒪[F]`): a determinant test for membership in `GL_n(𝒪[F])`.
-/

section ValuedMatrix

open Valued WithZero

/-- Let `F` be a field with a valuation into `ℤᵐ⁰`. If every entry of `A` has valuation at most `c`
and every entry of `B` has valuation at most `d`, then every entry of `A * B` has valuation at most
`c * d`. -/
lemma New.v_matrix_mul_le {n F : Type*} [Field F] [Valued F ℤᵐ⁰] [Fintype n] {m l : Type*}
    {A : Matrix m n F} {B : Matrix n l F} {c d : ℤᵐ⁰} (hA : ∀ (a : m) (b : n), v (A a b) ≤ c)
    (hB : ∀ (a : n) (b : l), v (B a b) ≤ d) (a : m) (b : l) :
    v ((A * B) a b) ≤ c * d :=
  v.map_sum_le fun i _ ↦ (map_mul v _ _).trans_le (mul_le_mul' (hA a i) (hB i b))

/-- Over a field F with a valuation v into ℤᵐ⁰, an invertible matrix g lies in GL_n(𝒪_F) if and
only if all its entries have valuation at most 1 and v(det g) = 1. -/
lemma New.mem_intGL_iff_det {n F : Type*} [Field F] [Valued F ℤᵐ⁰] [Fintype n] [DecidableEq n]
    {g : GL n F} :
    g ∈ intGL n 𝒪[F] ↔ (∀ a b : n, v (g a b) ≤ 1) ∧ v g.val.det = 1 := by
  have unit_iff (A : Matrix n n 𝒪[F]) : IsUnit A.det ↔ v (𝒪[F].subtype.mapMatrix A).det = 1 := by
    rw [← 𝒪[F].subtype.map_det]
    exact (Valuation.integer.integers v).isUnit_iff_valuation_eq_one
  refine ⟨?_, fun ⟨h_int, h_det⟩ ↦ ?_⟩
  · rintro ⟨u, rfl⟩
    exact ⟨fun a b ↦ (u a b).prop, (unit_iff u.1).1 ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit)⟩
  · let A : Matrix n n 𝒪[F] := fun a b ↦ ⟨g a b, h_int a b⟩
    exact ⟨.mk'' A ((unit_iff A).2 h_det), Units.ext rfl⟩

end ValuedMatrix
