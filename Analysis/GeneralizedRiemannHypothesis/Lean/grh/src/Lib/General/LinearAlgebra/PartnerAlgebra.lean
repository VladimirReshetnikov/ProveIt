import Lib.Adelic.Unitary.ComponentsAndBlockSums
import Lib.General.LinearAlgebra.HermiteForm

/-!
# Rows and columns of integral matrices, primitive matrices and the law of partners

This file develops linear algebra over a subring `O` of a commutative ring `R`, for the local
computations with partner functions. The index set `n` is split by `e : b ⊕ a ≃ n`. For
`k ∈ GL n R`, `New.firstCols e k` is the matrix of the columns `b` of `k`, and
`New.invLastRows e k`, `New.invFirstRows e k` are the matrices of the rows `a` and `b` of `k⁻¹`.

## Main definitions and results

* `New.AreMatched`: two functions `Φ`, `Ψ` supported on the blocks `New.invLastRows e k` and
  `New.firstCols e k` of `k ∈ GL n O`, whose values differ by the factor `χ (det k)`.
* `New.IsPrimitiveMatrix.mul_iff`: for primitive `y`, the matrix `y * x` is primitive exactly if `x`
  is primitive.
* `New.exists_firstCols_eq_mul`: multiplying `firstCols e k` by an element of `GL b O` and
  `invLastRows e k` by an element of `GL a O` gives the blocks of another element of `GL n O`,
  whose determinant is computed.
* `New.IsValuationPair.exists_firstCols_iff`: if `New.IsValuationPair O` holds, the primitive
  matrices are the `firstCols e k` with `k` in `GL n O`.
* `New.AreMatched.lift_of_reduction`: partners over `R` lift along a surjective local homomorphism
  `O → R`; here `O` is a subring of another ring `F`.
* `New.AreMatched.left_mul`, `New.AreMatched.right_mul`: the transformation laws of two partner
  functions.

Notions from other files:
* `New.intGL n O`: the group `GL n O` as a subgroup of `GL n R`.
* `New.IsPrimitiveMatrix O y`: the matrix `y` and some left inverse of it have entries in `O`.
* `New.HasLeftInv X`: the matrix `X` has a left inverse over `R`.
* `New.liftIntegralFn π f`: the function that is `f` at the image under `π` of a matrix over `O`
  and zero at every other matrix.
* `New.IsValuationPair O`: for all `u`, `v` in `R` there is an idempotent `ε` in `O` such that `u`
  and `v` are `O`-multiples of `(1 - ε) u + ε v`.

## Relation to the literature

Known; see `Lib.SiegelWeil.Tower.LargeSideConstantTerm` for sources.
-/

noncomputable section

/-! ## Invertibility detected after a local ring homomorphism -/

/-- A square matrix is invertible if its image under a local ring homomorphism is invertible. -/
lemma New.isUnit_of_mapMatrix {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n] {S : Type*}
    [CommRing S] (f : R →+* S) [IsLocalHom f] {M : Matrix n n R}
    (h_map : IsUnit (f.mapMatrix M)) : IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det] at h_map ⊢
  exact isUnit_of_map_unit f M.det (by rwa [f.map_det])

namespace New

open Matrix Function

section Blocks

variable {R a b n : Type} [CommRing R]
  [Fintype n] [DecidableEq n] (O : Subring R) {y : Matrix n b R} (e : b ⊕ a ≃ n) (k : GL n R)

/-! ### Blocks of an invertible matrix and partners -/

/-- For `k` invertible and the indices split by `e : b ⊕ a ≃ n`, the rows of `k⁻¹` indexed by the
block `a`. -/
abbrev invLastRows : Matrix a n R := k⁻¹.val.submatrix (e ∘ Sum.inr) id

/-- For `k` invertible and the indices split by `e : b ⊕ a ≃ n`, the columns of `k` indexed by the
block `b`. -/
abbrev firstCols : Matrix n b R := k.val.submatrix id (e ∘ Sum.inl)

/-- The functions `Φ` on `a × n` matrices and `Ψ` on `n × b` matrices are partners for the
multiplicative character `χ` over `O` if `Φ` vanishes off the matrices `invLastRows e k` and `Ψ` off
the matrices `firstCols e k`, for `k` in `GL_n(O)`, and
`Φ (invLastRows e k) = χ (det k) * Ψ (firstCols e k)` for all such `k`. -/
structure AreMatched (χ : MulChar R ℂ) (Φ : Matrix a n R → ℂ) (Ψ : Matrix n b R → ℂ) where
  /-- `Φ` vanishes off the matrices `invLastRows e k`, the rows `a` of `k⁻¹`, for `k` in
  `GL_n(O)`. -/
  supp_left (x : Matrix a n R) : Φ x ≠ 0 → ∃ k ∈ intGL n O, x = invLastRows e k
  /-- `Ψ` vanishes off the matrices `firstCols e k`, the columns `b` of `k`, for `k` in
  `GL_n(O)`. -/
  supp_right (y : Matrix n b R) : Ψ y ≠ 0 → ∃ k ∈ intGL n O, y = firstCols e k
  /-- For `k` in `GL_n(O)` the values of `Φ` and `Ψ` differ by the factor `χ (det k)`. -/
  apply_eq : ∀ k ∈ intGL n O, Φ (invLastRows e k) = χ k.val.det * Ψ (firstCols e k)

variable {O}

/-! ### Left inverses and primitive matrices -/

/-- For `k ∈ GL n R` and the indices split as `b ⊕ a`, the rows of `k⁻¹` indexed by `b`. -/
abbrev invFirstRows : Matrix b n R := k⁻¹.val.submatrix (e ∘ Sum.inl) id

/-- The rows `b` of `k⁻¹` form a left inverse of the columns `b` of `k`. -/
lemma invFirstRows_mul_firstCols [DecidableEq b] : invFirstRows e k * firstCols e k = 1 := by
  simp [← submatrix_mul, ← ext_iff, Matrix.one_apply]

/-- The rows `a` of the inverse of `invTransposeGL k = (kᵀ)⁻¹` are the transposed columns `a` of
`k`. -/
lemma invLastRows_invTransposeGL :
    invLastRows e (invTransposeGL k) = (firstCols ((Equiv.sumComm a b).trans e) k)ᵀ :=
  rfl

/-- The transposed rows `a` of `k⁻¹` are the columns `a` of `invTransposeGL k = (kᵀ)⁻¹`. -/
lemma transpose_invLastRows :
    (invLastRows e k)ᵀ = firstCols ((Equiv.sumComm a b).trans e) (invTransposeGL k) :=
  rfl

lemma hasLeftInv_invLastRows_transpose [DecidableEq a] : HasLeftInv (invLastRows e k)ᵀ := by
  rw [transpose_invLastRows]
  exact ⟨_, invFirstRows_mul_firstCols _ _⟩

omit [DecidableEq n] in
/-- Let `y` be primitive over `O`, that is, integral with an integral left inverse. Then `y * x` is
primitive if and only if `x` is. -/
lemma IsPrimitiveMatrix.mul_iff [DecidableEq a] [Fintype b] [DecidableEq b]
    {x : Matrix b a R} (hy_prim : IsPrimitiveMatrix O y) :
    IsPrimitiveMatrix O (y * x) ↔ IsPrimitiveMatrix O x := by
  obtain ⟨hy, L, hL_int, hL⟩ := hy_prim
  refine ⟨fun ⟨hyx, M, hM_int, hM⟩ ↦ ?_, fun ⟨hx, M, hM_int, hM⟩ ↦ ?_⟩
  · -- `x = L * (y * x)` is integral, and `M * y` is a left inverse of `x`
    have hx : L * (y * x) = x := by rw [← L.mul_assoc, hL, Matrix.one_mul]
    exact ⟨by simpa only [hx] using hL_int.mul hyx, M * y, hM_int.mul hy, by rwa [M.mul_assoc]⟩
  · -- `M * L` is a left inverse of `y * x`
    exact ⟨hy.mul hx, M * L, hM_int.mul hL_int, by simp [← L.mul_assoc, hL, hM, Matrix.mul_assoc]⟩

/-- An invertible matrix is primitive over `O` if and only if it lies in `GL n O`. -/
lemma isPrimitiveMatrix_iff_mem_intGL : IsPrimitiveMatrix O k.val ↔ k ∈ intGL n O := by
  simp [isPrimitiveMatrix_iff, Units.val_inj]

/-- A block of columns of a matrix in `GL n O` is primitive over `O`. -/
lemma isPrimitiveMatrix_firstCols [DecidableEq b] {k : GL n R} (hk : k ∈ intGL n O) :
    IsPrimitiveMatrix O (firstCols e k) :=
  -- `invFirstRows e k` is an integral left inverse.
  ⟨fun i j ↦ (mem_intGL.1 hk).1 i (e (Sum.inl j)), invFirstRows e k,
    fun i j ↦ (mem_intGL.1 hk).2 (e (Sum.inl i)) j, invFirstRows_mul_firstCols e k⟩

/-! ### Columns of a matrix and rows of its inverse -/

/-- A matrix consists of the rows `a` of `k⁻¹` for some `k ∈ GL n O` exactly if its transpose
consists of the columns `a` of some `k ∈ GL n O`. -/
lemma exists_invLastRows_iff_transpose {x : Matrix a n R} :
    (∃ k ∈ intGL n O, x = invLastRows e k) ↔
      ∃ k ∈ intGL n O, xᵀ = firstCols (Equiv.trans (Equiv.sumComm a b) e) k := by
  -- Reparametrise by the involution `invTransposeGL`, which preserves `GL n O`.
  refine invTransposeGL.exists_congr' fun k ↦ ?_
  change invTransposeGL k ∈ intGL n O ∧ x = invLastRows e (invTransposeGL k) ↔ _
  rw [invLastRows_invTransposeGL, invTransposeGL_mem_intGL, ← transpose_inj, transpose_transpose]

/-- The rows `a` of `k⁻¹` kill the columns `b` of `k`. -/
lemma invLastRows_mul_firstCols : invLastRows e k * firstCols e k = 0 := by
  simp [← submatrix_mul, ← ext_iff]

variable [Fintype a] [Fintype b]

/-- Complete the rows `invLastRows e k` by rows `s` to a square matrix. Its determinant times
`det k` is the determinant of `s * firstCols e k`. -/
lemma det_fromRows_invLastRows [DecidableEq a] [DecidableEq b] (s : Matrix b n R) :
    ((fromRows s (invLastRows e k)).submatrix e.symm id).det * k.val.det =
      (s * firstCols e k).det := by
  -- In the blocks given by `e`, the product with `k` is upper triangular with diagonal blocks
  -- `s * firstCols e k` and `1`, since the rows `invLastRows e k` are rows of `k⁻¹`.
  let lastCols : Matrix n a R := k.val.submatrix id (e ∘ Sum.inr)
  have h_one : invLastRows e k * lastCols = 1 := by
    simp [lastCols, ← submatrix_mul, ← ext_iff, Matrix.one_apply]
  have h_blocks : ((fromRows s (invLastRows e k)).submatrix e.symm id * k.val).submatrix e e =
      fromBlocks (s * firstCols e k) (s * lastCols) 0 1 := by
    have h_cols : k.val.submatrix id e = fromCols (firstCols e k) lastCols := by
      ext i (j | j) <;> rfl
    simp [submatrix_mul _ _ e id e bijective_id, h_cols,
      invLastRows_mul_firstCols, h_one]
  rw [← det_mul, ← det_submatrix_equiv_self e, h_blocks, det_fromBlocks_zero₂₁, det_one, mul_one]

/-- A matrix `y` that is killed by `invLastRows e k` is a combination of the columns
`firstCols e k`, with coefficients `invFirstRows e k * y`. -/
lemma firstCols_mul_invFirstRows_mul (h_kill : invLastRows e k * y = 0) :
    firstCols e k * (invFirstRows e k * y) = y := by
  let lastCols : Matrix n a R := k.val.submatrix id (e ∘ Sum.inr)
  -- Cut the product `k * k⁻¹ = 1` along `e`.
  have h_sum : firstCols e k * invFirstRows e k + lastCols * invLastRows e k = 1 := by
    rw [← k.mul_inv]
    ext i j
    simp [lastCols, mul_apply, ← e.sum_comp, Fintype.sum_sum_type]
  simpa [Matrix.add_mul, Matrix.mul_assoc, h_kill] using congrArg (· * y) h_sum

variable [DecidableEq a] [DecidableEq b]

/-- For `g ∈ GL b O`, `f ∈ GL a O` and `k ∈ GL n O`, the matrices `firstCols e k * g` and
`f * invLastRows e k` come from one `j ∈ GL n O`, with `det j * det f = det k * det g`. -/
lemma exists_firstCols_eq_mul (O : Subring R) (g : GL b R) (hg : g ∈ intGL b O) (f : GL a R)
    (hf : f ∈ intGL a O) (hk : k ∈ intGL n O) :
    ∃ j ∈ intGL n O,
      firstCols e j = firstCols e k * g.val ∧
      invLastRows e j = f.val * invLastRows e k ∧
      j.val.det * f.val.det = k.val.det * g.val.det := by
  -- Multiply `k` on the right by the block diagonal matrix `d` with blocks `g` and `f⁻¹`.
  let d : GL n R := reindexGL e (blockGL (g, f⁻¹))
  have hd : d ∈ intGL n O := by simp_all [d, mem_intGL, reindex_equiv e, ← map_inv]
  refine ⟨k * d, mul_mem hk hd, ?_, ?_, by simp [d, mul_assoc, Ring.inverse_mul_cancel]⟩ <;>
    simp [d, mul_apply, reindex_equiv e, ← map_inv, ← ext_iff]

/-- The set of the matrices `invLastRows e k` (rows `a` of `k⁻¹`) with `k ∈ GL n O` is stable under
left multiplication by `GL a O`. -/
lemma exists_mul_eq_invLastRows_iff {f : GL a R} (hf : f ∈ intGL a O) {x : Matrix a n R} :
    (∃ k ∈ intGL n O, f.val * x = invLastRows e k) ↔ ∃ k ∈ intGL n O, x = invLastRows e k := by
  refine ⟨fun ⟨k, hk, hx⟩ ↦ ?_, ?_⟩
  · obtain ⟨j, hj, -, hj_rows, -⟩ := exists_firstCols_eq_mul e k O 1 (one_mem _) _ (inv_mem hf) hk
    exact ⟨j, hj, by simp [hj_rows, ← hx]⟩
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨j, hj, -, hj_rows, -⟩ := exists_firstCols_eq_mul e k O 1 (one_mem _) f hf hk
    exact ⟨j, hj, hj_rows.symm⟩

/-- The set of the matrices `firstCols e k` (columns `b` of `k`) with `k ∈ GL n O` is stable under
right multiplication by `GL b O`. -/
lemma exists_mul_eq_firstCols_iff {g : GL b R} (hg : g ∈ intGL b O) :
    (∃ k ∈ intGL n O, y * g.val = firstCols e k) ↔ ∃ k ∈ intGL n O, y = firstCols e k := by
  refine ⟨fun ⟨k, hk, hy⟩ ↦ ?_, ?_⟩
  · obtain ⟨j, hj, hj_cols, -⟩ := exists_firstCols_eq_mul e k O g⁻¹ (inv_mem hg) 1 (one_mem _) hk
    exact ⟨j, hj, by simp [hj_cols, ← hy]⟩
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨j, hj, hj_cols, -⟩ := exists_firstCols_eq_mul e k O g hg 1 (one_mem _) hk
    exact ⟨j, hj, hj_cols.symm⟩

/-- If the subring `O` of `R` satisfies `New.IsValuationPair` (any two elements `u`, `v` of `R` are
`O`-multiples of `(1 - ε) u + ε v` for an idempotent `ε` of `O`), then an `n × b` matrix `y` is the
block of the columns `b` of an element of `GL n O` exactly when `y` has entries in `O` and a left
inverse over `O`. -/
lemma _root_.New.IsValuationPair.exists_firstCols_iff (hO : IsValuationPair O) :
    (∃ k ∈ intGL n O, y = firstCols e k) ↔ IsPrimitiveMatrix O y := by
  refine ⟨?_, fun hy ↦ ?_⟩
  · rintro ⟨k, hk, rfl⟩
    exact isPrimitiveMatrix_firstCols e hk
  -- Hermite form: `y = firstCols e k * D` with `k` integral and `D` square.
  obtain ⟨k, hk, D, -, rfl : y = firstCols e k * D, -⟩ :=
    hO.hermite (Embedding.inl.trans e.toEmbedding) y
  -- The square factor `D` is primitive, so it is an element `g` of `GL b O`.
  obtain ⟨g, hg, rfl⟩ := isPrimitiveMatrix_iff.1 ((isPrimitiveMatrix_firstCols e hk).mul_iff.1 hy)
  -- The factor `g` is absorbed into the basis.
  exact (exists_mul_eq_firstCols_iff e (inv_mem hg)).1 ⟨k, hk, by simp [Matrix.mul_assoc]⟩

end Blocks

/-! ### Lifting along a local homomorphism -/

section Lift

variable {R a b n : Type} [CommRing R] [Fintype n] [DecidableEq n] {F : Type} [CommRing F]
  {O : Subring F} {l m : Type} [Fintype l] [Fintype m]

/-- At a matrix `M` over the subring `O`, the lift `liftIntegralFn π f` takes the value of `f` at
the image of `M` under `π`. -/
lemma liftIntegralFn_map_coe (π : O →+* R) (f : Matrix l m R → ℂ) (M : Matrix l m O) :
    liftIntegralFn π f (M.map (↑)) = f (M.map π) :=
  dite_eq_left fun i j ↦ (M i j).property

/-- If the lift `liftIntegralFn π f` does not vanish at `S`, then `S` comes from a matrix `M` over
the subring `O`, and `f` does not vanish at the image of `M` under `π`. -/
lemma exists_map_coe_eq_of_liftIntegralFn_ne_zero {π : O →+* R} {f : Matrix l m R → ℂ}
    {S : Matrix l m F} (hS : liftIntegralFn π f S ≠ 0) :
    ∃ M : Matrix l m O, M.map (↑) = S ∧ f (M.map π) ≠ 0 := by
  have hS_int : ∀ (i : l) (j : m), S i j ∈ O := by_contra fun h_not ↦ hS (dite_eq_right h_not)
  exact ⟨of fun i j ↦ ⟨S i j, hS_int i j⟩, rfl, by rwa [← liftIntegralFn_map_coe π f]⟩

/-- Let `π : O → R` be a surjective local homomorphism from a subring `O` of `F`. If the image under
`π` of a matrix `y` over `O` is the block `firstCols e k` of columns of some `k ∈ GL n R`, then `y`
is the block `firstCols e j` of columns of some `j ∈ GL n O`. -/
lemma exists_map_coe_eq_firstCols {π : O →+* R} [IsLocalHom π] (hπ : Surjective π)
    {e : b ⊕ a ≃ n} {y : Matrix n b O} {k : GL n R} (hy_map : y.map π = firstCols e k) :
    ∃ j ∈ intGL n O, y.map (↑) = firstCols e j := by
  -- Lift the other columns of `k`; the resulting matrix is invertible as `π` is local.
  let M : Matrix n n O := of fun i ↦ extend (e ∘ Sum.inl) (y i) (surjInv hπ ∘ k i)
  have hM_cols (i : n) (j : b) : M i (e (Sum.inl j)) = y i j :=
    (e.injective.comp Sum.inl_injective).extend_apply (y i) (surjInv hπ ∘ k i) j
  have h_map : π.mapMatrix M = k := by
    refine Matrix.ext fun i c ↦ show π (M i c) = k.val i c from ?_
    by_cases hc : ∃ j : b, (e ∘ Sum.inl) j = c
    · obtain ⟨j, rfl⟩ := hc
      simpa [hM_cols] using congr_fun₂ hy_map i j
    · simp [M, extend_apply' (y i) (surjInv hπ ∘ k i) c hc, surjInv_eq hπ]
  obtain ⟨j, hj⟩ : IsUnit M := isUnit_of_mapMatrix π (by simp [h_map])
  refine ⟨GeneralLinearGroup.map O.subtype j, MonoidHom.mem_range.2 ⟨j, rfl⟩, ?_⟩
  simp [hj, hM_cols, ← ext_iff]

end Lift

/-! ### The laws of partners -/

namespace AreMatched

variable {R a b n : Type} [CommRing R] [Fintype a] [Fintype b] [Fintype n] [DecidableEq n]

/-- Let `π : O → R` be a surjective local homomorphism from a subring `O` of `F`, and let `χ'` agree
with `χ ∘ π` on the units of `O`. If `Φ`, `Ψ` are partners for `χ` over all of `R` (supported on the
rows `a` of `k⁻¹` and the columns `b` of `k` for `k ∈ GL n R`, with values differing by the
factor `χ (det k)`), then their lifts `New.liftIntegralFn` (read through `π` on matrices over `O`,
zero on other matrices) are partners for `χ'` over `O`. -/
lemma lift_of_reduction {e : b ⊕ a ≃ n} {χ : MulChar R ℂ} {Φ : Matrix a n R → ℂ}
    {Ψ : Matrix n b R → ℂ} {F : Type} [CommRing F] {O : Subring F} (π : O →+* R)
    (hπ_local : IsLocalHom π) (hπ : Surjective π) {χ' : MulChar F ℂ}
    (hχ : ∀ u : O, IsUnit u → χ' u = χ (π u)) (h : AreMatched ⊤ e χ Φ Ψ) :
    AreMatched O e χ' (liftIntegralFn π Φ) (liftIntegralFn π Ψ) := by
  refine ⟨fun x hx ↦ ?_, fun y hy ↦ ?_, ?_⟩
  · -- The rows of an inverse are treated as the columns of a matrix, by transposition.
    obtain ⟨X, rfl, hΦ⟩ := exists_map_coe_eq_of_liftIntegralFn_ne_zero hx
    obtain ⟨k, -, hk⟩ := (exists_invLastRows_iff_transpose e).1 (h.supp_left (X.map π) hΦ)
    rw [exists_invLastRows_iff_transpose, ← transpose_map]
    exact exists_map_coe_eq_firstCols hπ (by rwa [transpose_map])
  · obtain ⟨Y, rfl, hΨ⟩ := exists_map_coe_eq_of_liftIntegralFn_ne_zero hy
    obtain ⟨k, -, hk⟩ := h.supp_right (Y.map π) hΨ
    exact exists_map_coe_eq_firstCols hπ hk
  · -- For `k ∈ GL n O`, the identity at its image `j` over `F` is the identity of `h` at its
    -- image `m` over `R`.
    rintro _ ⟨k, rfl⟩
    let j : GL n F := GeneralLinearGroup.map O.subtype k
    let m : GL n R := GeneralLinearGroup.map π k
    have h_det : χ' j.val.det = χ m.val.det := by
      simpa [j, m, RingHom.map_det, ← O.subtype_apply] using hχ k.val.det (isUnits_det_units k)
    calc liftIntegralFn π Φ (invLastRows e j)
        = Φ (invLastRows e m) := liftIntegralFn_map_coe π Φ (invLastRows e k)
      _ = χ m.val.det * Ψ (firstCols e m) := h.apply_eq m (by simp [mem_intGL])
      _ = χ' j.val.det * liftIntegralFn π Ψ (firstCols e j) :=
        congrArg₂ (· * ·) h_det.symm (liftIntegralFn_map_coe π Ψ (firstCols e k)).symm

variable [DecidableEq a] [DecidableEq b]

variable {O : Subring R} {e : b ⊕ a ≃ n} {χ : MulChar R ℂ} {Φ : Matrix a n R → ℂ}
  {Ψ : Matrix n b R → ℂ}
/-- If `Φ`, `Ψ` are partners for `χ` over `O` (supported on the rows `a` of `k⁻¹` and the columns
`b` of `k` for `k ∈ GL n O`, with values differing by the factor `χ (det k)`), then
`χ (det g) * Φ (g * x) = Φ x` for all `g ∈ GL a O` and all `a × n` matrices `x`. -/
lemma left_mul (h : AreMatched O e χ Φ Ψ) {g : GL a R} {x : Matrix a n R} (hg : g ∈ intGL a O) :
    χ g.val.det * Φ (g.val * x) = Φ x := by
  by_cases hx : ∃ k ∈ intGL n O, x = invLastRows e k
  · -- `g * invLastRows e k = invLastRows e j`, where `j` has the same columns `firstCols` as `k`
    -- and `det j * det g = det k`
    obtain ⟨k, hk, rfl⟩ := hx
    obtain ⟨j, hj, hj_cols, hj_rows, hj_det⟩ := exists_firstCols_eq_mul e k O 1 (one_mem _) g hg hk
    simp only [Units.val_one, Matrix.mul_one, det_one, mul_one] at hj_cols hj_det
    calc χ g.val.det * Φ (g.val * invLastRows e k)
        = χ g.val.det * (χ j.val.det * Ψ (firstCols e j)) := by rw [← hj_rows, h.apply_eq j hj]
      _ = χ k.val.det * Ψ (firstCols e k) := by rw [← hj_det, hj_cols, map_mul]; ring
      _ = Φ (invLastRows e k) := (h.apply_eq k hk).symm
  · -- `g * x` is not of the form `invLastRows e k` either, so both sides vanish
    have h_left : Φ (g.val * x) = 0 := by_contra fun h_ne ↦
      hx ((exists_mul_eq_invLastRows_iff e hg).1 (h.supp_left (g.val * x) h_ne))
    rw [h_left, by_contra fun h_ne ↦ hx (h.supp_left x h_ne), mul_zero]

/-- If `Φ`, `Ψ` are partners for `χ` over `O` (supported on the rows `a` of `k⁻¹` and the columns
`b` of `k` for `k ∈ GL n O`, with values differing by the factor `χ (det k)`), then
`Ψ (y * g) * χ (det g) = Ψ y` for all `g ∈ GL b O` and all `n × b` matrices `y`. -/
lemma right_mul (h : AreMatched O e χ Φ Ψ) (g : GL b R) (hg : g ∈ intGL b O) (y : Matrix n b R) :
    Ψ (y * g.val) * χ g.val.det = Ψ y := by
  by_cases hy : ∃ k ∈ intGL n O, y = firstCols e k
  · -- `y * g = firstCols e j` for some `j` with the rows `invLastRows e k` and determinant
    -- `det k * det g`; compare `h.apply_eq` at `j` and at `k`, and cancel `χ (det k) ≠ 0`
    obtain ⟨k, hk, rfl⟩ := hy
    obtain ⟨j, hj, hj_cols, hj_rows, hj_det⟩ := exists_firstCols_eq_mul e k O g hg 1 (one_mem _) hk
    simp only [Units.val_one, Matrix.one_mul, det_one, mul_one] at hj_rows hj_det
    refine mul_left_cancel₀ (χ.apply_ne_zero_iff.2 (isUnits_det_units k)) ?_
    calc χ k.val.det * (Ψ (firstCols e k * g.val) * χ g.val.det)
        = χ j.val.det * Ψ (firstCols e j) := by rw [hj_det, hj_cols, map_mul]; ring
      _ = Φ (invLastRows e k) := by rw [← h.apply_eq j hj, hj_rows]
      _ = χ k.val.det * Ψ (firstCols e k) := h.apply_eq k hk
  · -- Otherwise `y * g` is not of the form `firstCols e j` either, and both sides vanish.
    have h_left : Ψ (y * g.val) = 0 := by_contra fun h_ne ↦
      hy ((exists_mul_eq_firstCols_iff e hg).1 (h.supp_right (y * g.val) h_ne))
    rw [h_left, by_contra fun h_ne ↦ hy (h.supp_right y h_ne), zero_mul]

end AreMatched

end New

end
