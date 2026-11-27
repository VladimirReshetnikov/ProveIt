import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Lib.Weil.DualPair.Defs
import Lib.Weil.Unramified.HeckeGL

/-!
# Extending columns, block matrices and block embeddings

For an embedding `ι : r ↪ n` of index sets, `New.inclMatrix k ι` has the standard basis vectors
`e (ι j)` as columns. Such a map splits `n` into two blocks, and the file studies the corresponding
block matrices. Over a field, independent columns extend to an invertible matrix. The embedding
`a ↦ diag(a, 1)` of unitary groups of sign matrices is a proper map, and the norm of a block
diagonal matrix is the larger of those of its blocks, for the L² operator norm.

## Main definitions and results

* `New.extendGL`: the embedding g ↦ diag(g, 1); `New.submatrix_extendGL` and
  `New.extendGL_apply_of_notMem_range` give its block g and its rows outside that block.
* `New.rangeParabolic`, `New.mem_rangeParabolic_iff`: the opposite parabolic for the two blocks, and
  its description in entries.
* `New.index_rangeParabolic_mul_card_GL`, `New.index_stabilizer_inclMatrix`: the index of the
  opposite parabolic times |GL_r(R)| is the index of the group that fixes the basis vectors of
  the first block, and over a finite field the latter index is computed.
* `New.residueDatum`: a function of adelic matrices given by their reductions at a family of
  places.
* `New.DiscreteSeries.isProperMap_inl`: the embedding `a ↦ diag(a, 1)` is a proper map.

Notions from other files:
* `New.parabolic`: the subgroup of GL_n(R) of matrices that are block upper triangular for a given
  level function on the indices.
* `New.U`, `New.U.sum`: U(J) is the group of g with gᴴJg = J; for a block diagonal sum J'' of J
  and J', `New.U.sum` is the homomorphism U(J) × U(J') → U(J'') sending (g,h) to diag(g,h).
-/

noncomputable section

/-!
## Extension of independent columns to an invertible matrix
-/

section ExtendColumns

open Matrix LinearEquiv Submodule

namespace New

variable {r n : Type*} [Fintype r] [Fintype n] [DecidableEq n] (ι : r ↪ n)

lemma inclMatrix_mulVecLin_injective (k : Type*) [Field k] :
    Function.Injective (inclMatrix k ι).mulVecLin :=
  mulVec_injective_iff.2 ((linearIndependent_cols_of_isUnit isUnit_one).comp ι ι.injective)

/-- A matrix b over a field with linearly independent columns extends to an invertible matrix u:
column ι(j) of u is column j of b. -/
lemma exists_GL_mul_inclMatrix {k : Type*} [Field k] {b : Matrix n r k}
    (h : Function.Injective b.mulVecLin) :
    ∃ u : GL n k, u.val * inclMatrix k ι = b := by
  -- Both matrices are injective as linear maps, so their ranges are isomorphic. Extend this
  -- isomorphism to an automorphism `g` of `n → k` and take its matrix.
  let e : (r → k) ≃ₗ[k] LinearMap.range (inclMatrix k ι).mulVecLin :=
    ofInjective _ (inclMatrix_mulVecLin_injective ι k)
  obtain ⟨g, hg⟩ := exists_linearEquiv_restrict_eq (e.symm ≪≫ₗ ofInjective b.mulVecLin h)
  have h_apply (v : r → k) : g (inclMatrix k ι *ᵥ v) = b *ᵥ v := by
    simpa [e] using (hg (e v)).symm
  refine ⟨.mk'' g.toMatrix' (by simp [← coe_det]), ?_⟩
  simp [ext_iff_mulVec, ← mulVec_mulVec, h_apply]

end New

end ExtendColumns

/-!
## The embedding diag(g, 1), the opposite parabolic and residue data

Here `u : r → n` is a map of index sets, mostly an embedding.
-/

namespace New

open Matrix Set

variable {r n n' R S ι : Type*} [CommRing R] [CommRing S]

lemma map_inclMatrix (f : R →+* S) (u : r → n) [DecidableEq n] :
    (inclMatrix R u).map f = inclMatrix S u := by
  rw [inclMatrix, ← submatrix_map, Matrix.map_one f f.map_zero f.map_one, inclMatrix]

variable {E : Type*} [Field E] [NumberField E]
  {T : Matrix n n' R} [Fintype n] [DecidableEq n]

/-- For an embedding u of index sets, multiplying T on the left by the transpose of
`inclMatrix R u` selects the rows of T indexed by u. -/
lemma inclMatrix_transpose_mul (u : r ↪ n) :
    (inclMatrix R u)ᵀ * T = T.submatrix u id := by
  ext i j
  simp [inclMatrix, Matrix.mul_apply, Matrix.one_apply]

@[simp]
lemma inclMatrix_transpose_mul_self [DecidableEq r] (u : r ↪ n) :
    (inclMatrix R u)ᵀ * inclMatrix R u = 1 := by
  rw [inclMatrix_transpose_mul, inclMatrix, submatrix_submatrix]
  exact submatrix_one_embedding u

variable [Fintype r]

/-- The transpose of `inclMatrix R u` cancels `inclMatrix R u` on the left of a product. -/
lemma inclMatrix_transpose_mul_cancel_left [DecidableEq r] (u : r ↪ n) (A : Matrix r n' R) :
    (inclMatrix R u)ᵀ * (inclMatrix R u * A) = A := by
  rw [← Matrix.mul_assoc, inclMatrix_transpose_mul_self, Matrix.one_mul]

open scoped Classical in
/-- For a family of places `w i` of E, the function on finite adelic matrices x
(given as vectors on index pairs) equal to f of the family of the reductions of x at the places
`w i` if x is integral at all of them, and 0 otherwise. -/
def residueDatum (w : ι → FinPlace E) (f : ((i : ι) → Matrix n' n (ResField (w i))) → ℂ)
    (x : n' × n → 𝔸f E) : ℂ :=
  if ∀ (i : ι) (p : n' × n), x p (w i) ∈ LocInt (w i) then
    f fun i ↦ (vecToMatrix x : Matrix n' n (𝔸f E)).map (residueOrZero ∘ evalAt (w i))
  else 0

/-- For an embedding u of index sets, the homomorphism GL_r(R) → GL_n(R), g ↦ diag(g, 1), with g
acting on the indices in the image of u. -/
@[local simp]
def extendGL [DecidableEq r] (u : r ↪ n) : GL r R →* GL n R :=
  Units.map
    { toFun g := 1 + inclMatrix R u * (g - 1) * (inclMatrix R u)ᵀ
      map_one' := by simp
      map_mul' g h := by
        -- With `P = inclMatrix R u`, the product is `1 + P * X * Pᵀ` for this `X = g * h - 1`.
        have h_sum : g * h - 1 = (g - 1) + (h - 1) + (g - 1) * (h - 1) := by noncomm_ring
        rw [h_sum]
        simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, add_assoc,
          inclMatrix_transpose_mul_cancel_left] }

/-- For the embedding g ↦ diag(g, 1), the columns indexed by u of the image of g are the columns
of g, extended by zero. -/
@[simp]
lemma extendGL_mul_inclMatrix [DecidableEq r] (u : r ↪ n) (g : GL r R) :
    (extendGL u g).val * inclMatrix R u = inclMatrix R u * g.val := by
  simp [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_sub]

/-- The block of diag(g, 1) with rows and columns in the image of u is g. -/
lemma submatrix_extendGL [DecidableEq r] (u : r ↪ n) (g : GL r R) :
    (extendGL u g).val.submatrix u u = g.val := by
  ext i j
  simp [extendGL, inclMatrix, Matrix.mul_apply, Matrix.one_apply]

/-- Outside the image of u, the rows of diag(g, 1) are those of the identity matrix. -/
lemma extendGL_apply_of_notMem_range [DecidableEq r]
    (u : r ↪ n) (g : GL r R) {i : n} (hi : i ∉ range u) (j : n) :
    extendGL u g i j = (1 : Matrix n n R) i j := by
  have h_ne (k : r) : i ≠ u k := fun h ↦ hi ⟨k, h.symm⟩
  simp [extendGL, inclMatrix, Matrix.mul_apply, Matrix.one_apply, h_ne]

/-- The matrix `extendGL u g` has block g on the image of u and agrees with the identity matrix at
every entry whose row index is outside that image. -/
lemma submatrix_extendGL_and_apply_of_notMem_range [DecidableEq r] (u : r ↪ n) (g : GL r R) :
    (extendGL u g).val.submatrix u u = g.val ∧
    ∀ i ∉ range u, ∀ j : n, extendGL u g i j = (1 : Matrix n n R) i j :=
  ⟨submatrix_extendGL u g, fun _ hi ↦ extendGL_apply_of_notMem_range u g hi⟩

lemma extendGL_injective [DecidableEq r]
    (u : r ↪ n) : Function.Injective (extendGL (R := R) u) := by
  intro g h h_eq
  rw [Units.ext_iff, ← submatrix_extendGL u g, h_eq, submatrix_extendGL]

/-- An invertible matrix x fixes every column of T, seen as the family `T.col`, if and only if
xT = T. -/
lemma mem_stabilizer_col_iff {x : GL n R} :
    x ∈ MulAction.stabilizer (GL n R) T.col ↔ x.val * T = T := by
  -- the columns of `x * T` are the images of those of `T` under `x`
  change (x.val * T)ᵀ = Tᵀ ↔ _
  exact transpose_inj

omit [Fintype n] in
/-- A matrix T is the extension by zero of its rows indexed by u exactly when its other rows
vanish. -/
lemma eq_inclMatrix_mul_iff [DecidableEq r] (u : r ↪ n) :
    T = inclMatrix R u * T.submatrix u id ↔ ∀ i ∉ range u, ∀ j : n', T i j = 0 := by
  -- row `i` of the product is row `i` of `T` if `i` is in the image of `u`, and zero otherwise
  rw [← ext_iff]
  refine forall_congr' fun i ↦ ?_
  by_cases hi : i ∈ range u
  · obtain ⟨k, rfl⟩ := hi
    simp [inclMatrix, Matrix.mul_apply, Matrix.one_apply]
  · have h_ne (k : r) : i ≠ u k := fun h ↦ hi ⟨k, h.symm⟩
    simp [inclMatrix, Matrix.mul_apply, hi, h_ne]

/-- For the order `False < True` on propositions, the level `· ∉ s` of `j` is below that of `i`
exactly when `j` is in `s` and `i` is not. -/
lemma notMem_lt_notMem_iff {α : Type*} {s : Set α} {i j : α} :
    (j ∉ s) < (i ∉ s) ↔ j ∈ s ∧ i ∉ s := by
  grind [lt_iff_le_not_ge, le_Prop_eq]

attribute [local instance] Prop.linearOrder

/-- An invertible matrix is block upper triangular, for the image of `u` as first block, exactly
when it keeps the span of the basis vectors indexed by `u`, the columns of `inclMatrix R u`. -/
lemma mem_parabolic_iff_mul_inclMatrix [DecidableEq r] (u : r ↪ n) {x : GL n R} :
    x ∈ parabolic (· ∉ range u) ↔
      x.val * inclMatrix R u = inclMatrix R u * ((inclMatrix R u)ᵀ * (x.val * inclMatrix R u)) := by
  have h_entry (i : n) (j : r) : (x.val * inclMatrix R u) i j = x.val i (u j) := by
    simp [inclMatrix, Matrix.mul_apply, Matrix.one_apply]
  simp only [inclMatrix_transpose_mul, eq_inclMatrix_mul_iff, h_entry]
  refine ⟨fun hx i hi j ↦ hx (notMem_lt_notMem_iff.2 ⟨mem_range_self j, hi⟩), fun hx i j hij ↦ ?_⟩
  obtain ⟨⟨j, rfl⟩, hi⟩ := notMem_lt_notMem_iff.1 hij
  exact hx i hi j

/-- The opposite parabolic: the image under g ↦ (gᵀ)⁻¹ of the block upper triangular group
`New.parabolic` for the level function that is false on the image of u and true elsewhere. -/
def rangeParabolic (u : r ↪ n) : Subgroup (GL n R) :=
  (parabolic (· ∉ range u)).map invTransposeGL.toMonoidHom

omit [Fintype r] in
/-- The opposite parabolic `rangeParabolic u` consists of the invertible matrices x whose entries
with row in the image of u and column outside it vanish. -/
lemma mem_rangeParabolic_iff (u : r ↪ n) {x : GL n R} :
    x ∈ rangeParabolic u ↔ ∀ i : r, ∀ j ∉ range u, x (u i) j = 0 := by
  rw [rangeParabolic, Subgroup.mem_map_equiv, ← inv_mem_iff, ← map_inv]
  -- the inverse transpose of `x⁻¹` is `xᵀ`, and `xᵀ` is to be block upper triangular
  have h_val : (invTransposeGL.symm x⁻¹).val = x.valᵀ :=
    congrArg (fun y : GL n R ↦ y.valᵀ) (inv_inv x)
  change (invTransposeGL.symm x⁻¹).val.BlockTriangular (· ∉ range u) ↔ _
  rw [h_val]
  refine ⟨fun hx i j hj ↦ hx (notMem_lt_notMem_iff.2 ⟨mem_range_self i, hj⟩), fun hx k j hjk ↦ ?_⟩
  obtain ⟨⟨i, rfl⟩, hk⟩ := notMem_lt_notMem_iff.1 hjk
  exact hx i k hk

/-- For x in the opposite parabolic (entries with row in the image of u and column outside it
vanish), the rows of x T indexed by u are the u-block of x times the rows of T indexed by u; here
f selects columns of T. -/
lemma submatrix_mul_of_mem_rangeParabolic (u : r ↪ n) {x : GL n R} {f : ι → n'}
    (hx : x ∈ rangeParabolic u) :
    (x.val * T).submatrix u f = x.val.submatrix u u * T.submatrix u f := by
  ext i j
  -- in `∑ k, x (u i) k * T k (f j)` the terms with `k` outside the image of `u` vanish
  have h_zero (k : n) (hk : k ∉ range u) : x (u i) k * T k (f j) = 0 := by
    simp [(mem_rangeParabolic_iff u).1 hx i k hk]
  exact (Fintype.sum_of_injective u u.injective _ _ h_zero fun _ ↦ rfl).symm

omit [Fintype r] in
/-- The opposite parabolic `New.rangeParabolic u` has the same index in GL_n(R) as the block upper
triangular group for the two blocks given by the image of u and its complement. -/
lemma index_rangeParabolic (u : r ↪ n) :
    (rangeParabolic (R := R) u).index = (parabolic (R := R) (· ∉ range u)).index := by
  simp [rangeParabolic]

/-- In `GL_n(R)`, the index of `rangeParabolic u` times the order of `GL_r(R)` equals the index of
the stabilizer of the basis vectors `e_{u j}`, i.e. of the matrices fixing each basis vector indexed
by the image of `u`. Here `rangeParabolic u` is the image under `g ↦ (gᵀ)⁻¹` of the block upper
triangular group `parabolic` for the level function that is false on the image of `u` and true
elsewhere. (An infinite index or order counts as `0`.) -/
lemma index_rangeParabolic_mul_card_GL [DecidableEq r] (u : r ↪ n) :
    (rangeParabolic (R := R) u).index * Nat.card (GL r R) =
      (MulAction.stabilizer (GL n R) (inclMatrix R u).col).index := by
  -- Replace the opposite parabolic by the group `P` of the matrices that keep the span of the
  -- columns of `A`; it has the same index. The first diagonal block is a homomorphism of `P` onto
  -- `GL_r(R)`, and its kernel is the stabiliser.
  let A : Matrix n r R := inclMatrix R u
  let P : Subgroup (GL n R) := parabolic (· ∉ range u)
  have h_mem (x : GL n R) : x ∈ P ↔ x.val * A = A * (Aᵀ * (x.val * A)) :=
    mem_parabolic_iff_mul_inclMatrix u
  let block : P →* Matrix r r R :=
    { toFun x := Aᵀ * ((x : GL n R).val * A)
      map_one' := by simp [A]
      map_mul' x y := by
        rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, (h_mem y).1 y.property,
          inclMatrix_transpose_mul_cancel_left]
        simp only [Matrix.mul_assoc] }
  have h_onto : Function.Surjective block.toHomUnits := fun g ↦ by
    have h_block : Aᵀ * ((extendGL u g).val * A) = g := by
      rw [extendGL_mul_inclMatrix, inclMatrix_transpose_mul_cancel_left]
    have hg : extendGL u g ∈ P := by rw [h_mem, h_block, extendGL_mul_inclMatrix]
    exact ⟨⟨extendGL u g, hg⟩, Units.ext h_block⟩
  have h_le : MulAction.stabilizer (GL n R) A.col ≤ P := fun x hx ↦ by
    rw [h_mem, mem_stabilizer_col_iff.1 hx, inclMatrix_transpose_mul_self, Matrix.mul_one]
  have h_ker : (MulAction.stabilizer (GL n R) A.col).subgroupOf P = block.toHomUnits.ker := by
    ext ⟨x, hx⟩
    rw [Subgroup.mem_subgroupOf, mem_stabilizer_col_iff, MonoidHom.mem_ker, Units.ext_iff]
    change x.val * A = A ↔ Aᵀ * (x.val * A) = 1
    exact ⟨fun h ↦ by simp [h, A], fun h ↦ by rw [(h_mem x).1 hx, h, Matrix.mul_one]⟩
  rw [index_rangeParabolic, ← Subgroup.relIndex_mul_index h_le, Subgroup.relIndex, h_ker,
    Subgroup.index_ker, MonoidHom.range_eq_top.2 h_onto, Subgroup.card_top, mul_comm]

/-- Over a field, the orbit under `GL_n` of the family of the basis vectors indexed by `u` is the
set of all linearly independent families indexed by `r`. -/
lemma orbit_col_inclMatrix (k : Type*) [Field k] (u : r ↪ n) :
    MulAction.orbit (GL n k) (inclMatrix k u).col = {s : r → n → k | LinearIndependent k s} := by
  have h_smul (g : GL n k) : g • (inclMatrix k u).col = (g.val * inclMatrix k u).col := rfl
  ext s
  simp only [MulAction.mem_orbit_iff, h_smul, mem_ofPred_eq]
  constructor
  · rintro ⟨g, rfl⟩
    rw [← mulVec_injective_iff, ← coe_mulVecLin, mulVecLin_mul]
    exact (mulVec_injective_iff_isUnit.2 g.isUnit).comp (inclMatrix_mulVecLin_injective u k)
  · intro hs
    obtain ⟨g, hg⟩ := exists_GL_mul_inclMatrix u (b := (of s)ᵀ) (mulVec_injective_iff.2 hs)
    exact ⟨g, congrArg col hg⟩

variable {k : Type*} [Field k] [Finite k]

/-- Over a finite field with `q` elements, the group of the matrices in `GL_n` that fix the `r`
basis vectors indexed by `u` has index `∏_{i < r} (q ^ n - q ^ i)`, the number of independent
families of `r` vectors. -/
lemma index_stabilizer_inclMatrix (u : r ↪ n) :
    (MulAction.stabilizer (GL n k) (inclMatrix k u).col).index =
      ∏ i ∈ Finset.range (Fintype.card r), (Nat.card k ^ Fintype.card n - Nat.card k ^ i) := by
  cases nonempty_fintype k
  -- The index is the number of independent families; reindex them by `Fin (card r)` to count them.
  have h_card : Nat.card {s : r → n → k | LinearIndependent k s} =
      Nat.card {s : Fin (Fintype.card r) → n → k // LinearIndependent k s} :=
    Nat.card_congr (((Fintype.equivFin r).arrowCongr (.refl (n → k))).subtypeEquiv fun s ↦
      (linearIndependent_equiv (Fintype.equivFin r).symm).symm)
  have h_le : Fintype.card r ≤ Module.finrank k (n → k) := by
    simpa using Fintype.card_le_of_embedding u
  rw [MulAction.index_stabilizer, orbit_col_inclMatrix, ← Nat.card_coe_set_eq, h_card,
    card_linearIndependent h_le, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card,
    Fin.prod_univ_eq_prod_range fun i ↦ Fintype.card k ^ Fintype.card n - Fintype.card k ^ i]

/-- Over a finite field with `q` elements, the index of the group of the matrices in `GL_n` that fix
the `r` basis vectors indexed by `u` is the complex number
`q ^ (n r) ∏_{n - r < i ≤ n} (1 - q⁻¹ ^ i)`. -/
lemma cast_index_stabilizer_inclMatrix (u : r ↪ n) :
    ((MulAction.stabilizer (GL n k) (inclMatrix k u).col).index : ℂ) =
      Nat.card k ^ (Fintype.card n * Fintype.card r) *
        ∏ i ∈ Finset.Icc (Fintype.card n - Fintype.card r + 1) (Fintype.card n),
          (1 - (Nat.card k : ℂ)⁻¹ ^ i) := by
  rw [index_stabilizer_inclMatrix]
  have h_le : Fintype.card r ≤ Fintype.card n := Fintype.card_le_of_embedding u
  have hq_pos : 0 < Nat.card k := Nat.card_pos
  set q := Nat.card k
  set N := Fintype.card n
  set M := Fintype.card r
  have h_factor (i : ℕ) (hi : i ∈ Finset.range M) :
      ((q ^ N - q ^ i : ℕ) : ℂ) = q ^ N * (1 - (q : ℂ)⁻¹ ^ (N - i)) := by
    have hi_le : i ≤ N := (Finset.mem_range.1 hi).le.trans h_le
    have hq_ne : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq_pos.ne'
    rw [Nat.cast_sub (Nat.pow_le_pow_right hq_pos hi_le), inv_pow, pow_sub₀ _ hq_ne hi_le]
    push_cast
    field_simp
  have h_reindex : ∏ i ∈ Finset.range M, (1 - (q : ℂ)⁻¹ ^ (N - i)) =
      ∏ i ∈ Finset.Icc (N - M + 1) N, (1 - (q : ℂ)⁻¹ ^ i) :=
    Finset.prod_nbij' (N - ·) (N - ·) (by grind) (by grind) (by grind) (by grind) fun _ _ ↦ rfl
  rw [Nat.cast_prod, Finset.prod_congr rfl h_factor, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_range, pow_mul, h_reindex]

end New

/-!
## The block embedding of unitary groups

`New.U.inl` embeds `New.U (New.signMatrix ε)`, the unitary group of the diagonal matrix of signs
`ε`, into the group `New.U (New.signMatrix (Sum.elim ε η))` of the concatenated signs, by
`a ↦ diag(a, 1)`.
-/

/-- The block embedding a ↦ diag(a, 1) of U(diag ε) into the unitary group of the concatenated
signs (ε, η). -/
@[simps! apply_coe_val]
noncomputable def New.U.inl {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (ε : n → ℤˣ) (η : m → ℤˣ) :
    U (signMatrix ε) →* U (signMatrix (Sum.elim ε η)) :=
  (sum (signMatrix_sum ε η)).comp (MonoidHom.inl (U (signMatrix ε)) (U (signMatrix η)))

/-!
## Norms of block diagonal matrices and properness of block embeddings

Two facts on block diagonal matrices; all norms are `L²` operator norms.
-/

section BlockEmbeddingNorm

open Matrix Norms.L2Operator

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] {ε : n → ℤˣ}
  {ε' : m → ℤˣ}

/-- The L² operator norm of diag(x, b) is the larger of the norms of x and b. -/
@[simp]
theorem New.norm_fromBlocks_zero_zero (x : Matrix n n ℂ) (b : Matrix m m ℂ) :
    ‖fromBlocks x 0 0 b‖ = ‖x‖ ⊔ ‖b‖ := by
  -- `(x, b) ↦ fromBlocks x 0 0 b` is an injective star homomorphism of C⋆-algebras, so an isometry
  let φ : Matrix n n ℂ × Matrix m m ℂ →⋆ₙₐ[ℂ] Matrix (n ⊕ m) (n ⊕ m) ℂ :=
    { toFun p := fromBlocks p.1 0 0 p.2
      map_smul' := by simp [fromBlocks_smul]
      map_zero' := fromBlocks_zero
      map_add' := by simp [fromBlocks_add]
      map_mul' := by simp [fromBlocks_multiply]
      map_star' := by simp [star_eq_conjTranspose, fromBlocks_conjTranspose] }
  exact NonUnitalStarAlgHom.norm_map φ (fun p q h ↦ by simpa [φ, Prod.ext_iff] using h) (x, b)

/-- For families of signs ε and ε', the embedding a ↦ diag(a, 1) of U(diag ε) into
U(diag(ε, ε')) is a proper map. -/
@[fun_prop]
theorem New.DiscreteSeries.isProperMap_inl : IsProperMap (U.inl ε ε') := by
  -- Followed by the continuous map "upper left block", `U.inl` is the closed embedding of the
  -- unitary group in the matrices.
  have h_val (g : U (signMatrix ε)) : (U.inl ε ε' g).val.val = fromBlocks g.val.val 0 0 1 := by
    simp
  have h_cont : Continuous (U.inl ε ε') := by
    simp only [continuous_U_iff_matrix, h_val]
    fun_prop
  exact isProperMap_of_comp_of_t2 h_cont (g := fun g ↦ g.val.val.submatrix .inl .inl)
    (by fun_prop) isClosedEmbedding_U.isProperMap

end BlockEmbeddingNorm

end
