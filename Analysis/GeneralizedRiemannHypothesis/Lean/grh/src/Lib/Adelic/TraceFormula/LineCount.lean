import Lib.General.Groups.BesselGroups

/-!
# Lines and hyperplanes over a field

This file describes the stabilisers in `GL_n` of the line of a basis vector `e_i` and of the
complementary coordinate hyperplane. Over a finite field it counts the linear forms with value `1`
at `e_i`, and those with value `1` both at `e_i` and at a vector off its line. It shows that `0`
is a simple root of the characteristic polynomial of a matrix of block shape `(0 ∗; 0 g')`
with `g'` invertible.

Notions from other files:
* `parabolic lev`: the subgroup of `GL_n` of the matrices `g` with `g a b = 0` whenever
  `lev b < lev a`. The two stabilisers use level functions with values in `Prop`, ordered by
  implication.

## Relation to the literature

Standard linear algebra.
-/

namespace New

open Matrix Finset

/-! ### Stabilisers and counts -/

attribute [local instance] Prop.linearOrder

section Field

variable {F n : Type} [Field F] [Fintype n] [DecidableEq n] {i : n} {g h : GL n F}

/-- In the order of propositions by implication, `p < q` says that `q` holds and `p` does not. -/
lemma prop_lt_iff_not_and {p q : Prop} : p < q ↔ ¬p ∧ q := by
  simp only [lt_iff_le_not_ge, le_Prop_eq]
  tauto

/-- An element lies in `parabolic lev` exactly when its matrix is block triangular for `lev`. -/
lemma mem_parabolic_iff_blockTriangular {α : Type} [LinearOrder α] {lev : n → α} :
    g ∈ parabolic lev ↔ (g : Matrix n n F).BlockTriangular lev :=
  Iff.rfl

/-- An element `g` lies in `parabolic (· ≠ i)`, the block triangular matrices for the levels
`(· ≠ i)`, exactly when `g j i = 0` for all `j ≠ i`: the group is the stabiliser of the line of
`e_i`. -/
lemma mem_parabolic_ne : g ∈ parabolic (· ≠ i) ↔ ∀ j ≠ i, g j i = 0 := by
  rw [mem_parabolic_iff_blockTriangular]
  refine ⟨fun hg j hj ↦ hg (prop_lt_iff_not_and.2 ⟨not_not.2 rfl, hj⟩), fun hg a b h_lt ↦ ?_⟩
  obtain ⟨rfl, ha⟩ : b = i ∧ a ≠ i := by simpa [prop_lt_iff_not_and] using h_lt
  exact hg a ha

/-- An element `g` lies in `parabolic (· = i)`, the block triangular matrices for the levels
`(· = i)`, exactly when `g i j = 0` for all `j ≠ i`: the group is the stabiliser of the hyperplane
spanned by the `e_j`, `j ≠ i`. -/
lemma mem_parabolic_eq : g ∈ parabolic (· = i) ↔ ∀ j ≠ i, g i j = 0 := by
  rw [mem_parabolic_iff_blockTriangular]
  refine ⟨fun hg j hj ↦ hg (prop_lt_iff_not_and.2 ⟨hj, rfl⟩), fun hg a b h_lt ↦ ?_⟩
  obtain ⟨hb, rfl⟩ : b ≠ i ∧ a = i := prop_lt_iff_not_and.1 h_lt
  exact hg b hb

omit [Fintype n] in
/-- A vector is a multiple of `e_i` exactly when its other coordinates vanish. -/
lemma exists_eq_smul_single_iff {z : n → F} :
    (∃ c : F, z = c • Pi.single i 1) ↔ ∀ j ≠ i, z j = 0 := by
  refine ⟨?_, fun hz ↦ ⟨z i, by ext j; by_cases hj : j = i <;> simp [hj, hz]⟩⟩
  rintro ⟨c, rfl⟩ j hj
  simp [hj]

/-- The elements `g` and `h` have the same left coset of `parabolic (· ≠ i)`, the stabiliser of
the line of `e_i`, exactly when `h e_i` lies on the line of `g e_i`. -/
lemma inv_mul_mem_parabolic_ne :
    g⁻¹ * h ∈ parabolic (· ≠ i) ↔
      ∃ c : F, (h : Matrix n n F).col i = c • (g : Matrix n n F).col i := by
  have h_col (j : n) : (g⁻¹ * h) j i = ((g⁻¹ : GL n F) *ᵥ (h : Matrix n n F).col i) j := by
    simp [mul_apply, mulVec, dotProduct]
  simp only [mem_parabolic_ne, h_col, ← exists_eq_smul_single_iff]
  refine exists_congr fun c ↦ ?_
  rw [← mulVec_single_one (g : Matrix n n F), ← mulVec_smul]
  exact ⟨fun h_eq ↦ by simp [← h_eq, mulVec_mulVec],
    fun h_eq ↦ by simp [h_eq, mulVec_mulVec]⟩

/-- The elements `g` and `h` have the same right coset of `parabolic (· = i)`, the stabiliser of
the hyperplane `z i = 0`, exactly when the `i`-th row of `h` is a multiple of that of `g`. -/
lemma mul_inv_mem_parabolic_eq :
    h * g⁻¹ ∈ parabolic (· = i) ↔
      ∃ c : F, (h : Matrix n n F).row i = c • (g : Matrix n n F).row i := by
  have h_row (j : n) : (h * g⁻¹) i j = ((h : Matrix n n F).row i ᵥ* (g⁻¹ : GL n F)) j := by
    simp [mul_apply, vecMul, dotProduct]
  simp only [mem_parabolic_eq, h_row, ← exists_eq_smul_single_iff]
  refine exists_congr fun c ↦ ?_
  rw [← single_one_vecMul i (g : Matrix n n F), ← smul_vecMul]
  exact ⟨fun h_eq ↦ by simp [← h_eq, vecMul_vecMul],
    fun h_eq ↦ by simp [h_eq, vecMul_vecMul]⟩

/-- If the `i`-th column of an invertible `g` vanishes off the diagonal, then `g i i ≠ 0`. -/
lemma diag_ne_zero_of_col (hg : ∀ j ≠ i, g j i = 0) : g i i ≠ 0 :=
  fun h_zero ↦ g.det_ne_zero (det_eq_zero_of_column_eq_zero i fun j ↦ by grind)

/-- If the `i`-th row of an invertible `g` vanishes off the diagonal, then `g i i ≠ 0`. -/
lemma diag_ne_zero_of_row (hg : ∀ j ≠ i, g i j = 0) : g i i ≠ 0 :=
  fun h_zero ↦ g.det_ne_zero (det_eq_zero_of_row_eq_zero i fun j ↦ by grind)

/-- Replacing the `j`-th column of the identity matrix by `z` gives determinant `z j`. -/
lemma det_updateCol_one (j : n) (z : n → F) : (updateCol 1 j z).det = z j := by
  rw [← cramer_apply, cramer_one, Module.End.one_apply]

/-- Replacing the `j`-th row of the identity matrix by `z` gives determinant `z j`. -/
lemma det_updateRow_one (j : n) (z : n → F) : (updateRow 1 j z).det = z j := by
  rw [← det_transpose, ← updateCol_transpose, transpose_one, det_updateCol_one]

/-- Every non-zero vector is the `i`-th column of an invertible matrix. -/
lemma exists_col_eq (i : n) {z : n → F} (hz : z ≠ 0) :
    ∃ g : GL n F, (g : Matrix n n F).col i = z := by
  -- Put `z` into a column `j` with `z j ≠ 0` of the identity, and exchange the columns `i`, `j`.
  obtain ⟨j, hj⟩ : ∃ j : n, z j ≠ 0 := Function.ne_iff.1 hz
  refine ⟨GeneralLinearGroup.mkOfDetNeZero (updateCol 1 j z) (by rwa [det_updateCol_one]) *
    GeneralLinearGroup.swap F j i, by ext; simp⟩

/-- Every fibre of a surjective homomorphism `A → B` of finite groups has `#A / #B` elements. -/
lemma card_fiber_mul_card {A B : Type} [AddGroup A] [Fintype A] [AddGroup B] [Fintype B]
    [DecidableEq B] (φ : A →+ B) (hφ : Function.Surjective φ) (b : B) :
    #{a : A | φ a = b} * Fintype.card B = Fintype.card A := by
  have h_const (b' : B) : #{a : A | φ a = b'} = #{a : A | φ a = b} :=
    AddMonoidHom.card_fiber_eq_of_mem_range φ (hφ b') (hφ b)
  have h_fibers : Fintype.card A = ∑ b' : B, #{a : A | φ a = b'} :=
    card_eq_sum_card_fiberwise fun a _ ↦ mem_univ (φ a)
  simp [h_fibers, h_const, mul_comm]

variable [Fintype F] [DecidableEq F]

/-- Over a field of `q` elements and in dimension `n` there are `q ^ (n - 1)` hyperplanes that do
not contain `e_i`. Each of them is the kernel of one linear form `ξ` with `ξ e_i = 1`, and these
forms are counted. -/
lemma card_forms_missing_line (i : n) :
    #{ξ : n → F | ξ i = 1} * Fintype.card F = Fintype.card F ^ Fintype.card n := by
  rw [← Fintype.card_fun]
  exact card_fiber_mul_card (Pi.evalAddMonoidHom (fun _ : n ↦ F) i) (Function.surjective_eval i) 1

/-- Over a field of `q` elements and in dimension `n`, if `z j ≠ 0` for some `j ≠ i`, so that `z`
is off the line of `e_i`, then there are `q ^ (n - 2)` linear forms with value `1` at `e_i` and at
`z`. -/
lemma card_forms_taking_one_at_two_vectors_mul_sq {z : n → F} {j : n} (hj : j ≠ i) (hz : z j ≠ 0) :
    #{ξ : n → F | ξ i = 1 ∧ ξ ⬝ᵥ z = 1} * Fintype.card F ^ 2 = Fintype.card F ^ Fintype.card n := by
  -- The forms are the fibre over `(1, 1)` of the surjection `φ : ξ ↦ (ξ e_i, ξ z)`.
  let φ : (n → F) →+ F × F :=
    (Pi.evalAddMonoidHom (fun _ : n ↦ F) i).prod
      (AddMonoidHom.mk' (· ⬝ᵥ z) fun ξ η : n → F ↦ add_dotProduct ξ η z)
  have hφ_apply : ∀ ξ : n → F, φ ξ = (ξ i, ξ ⬝ᵥ z) := fun _ ↦ rfl
  have hφ : Function.Surjective φ := by
    rintro ⟨a, b⟩
    refine ⟨Pi.single i a + Pi.single j ((b - a * z i) / z j), ?_⟩
    simp [hφ_apply, hj.symm, hz]
  simpa only [hφ_apply, Prod.mk.injEq, Fintype.card_prod, Fintype.card_fun, ← sq] using
    card_fiber_mul_card φ hφ (1, 1)

/-- Over a field of `q` elements, the line of `e_i` has `q` elements. -/
lemma card_line (i : n) : #{z : n → F | ∀ j ≠ i, z j = 0} = Fintype.card F := by
  have h_line : ({z : n → F | ∀ j ≠ i, z j = 0} : Finset (n → F)) =
      univ.image fun c : F ↦ c • Pi.single i 1 := by
    ext z
    simpa [eq_comm] using (exists_eq_smul_single_iff (i := i) (z := z)).symm
  rw [h_line, card_image_of_injective _
    (smul_left_injective F (Pi.single_ne_zero_iff.2 one_ne_zero)), card_univ]

/-- For a vector `z` let `N z` be the number of forms `ξ` with `ξ e_i = 1` and `ξ z = 1`. The sum
of `f z` over the pairs `(ξ, z)` with `ξ e_i = 1` and `ξ z = 1` is the sum of `N z • f z` over all
vectors `z`. -/
lemma sum_forms_sum_eq_sum_card_smul {W : Type} [AddCommMonoid W] (i : n) (f : (n → F) → W) :
    ∑ ξ : n → F with ξ i = 1, ∑ z : n → F with ξ ⬝ᵥ z = 1, f z =
      ∑ z : n → F, #{ξ : n → F | ξ i = 1 ∧ ξ ⬝ᵥ z = 1} • f z := by
  simp [sum_comm' (t' := univ) (s' := fun z ↦ {ξ : n → F | ξ i = 1 ∧ ξ ⬝ᵥ z = 1})]

/-- A multiple `z ≠ e_i` of `e_i` has value `1` under no form `ξ` with `ξ e_i = 1`. -/
lemma card_forms_eq_zero_of_ne_single {z : n → F} (hz : ∀ j ≠ i, z j = 0)
    (h_ne : z ≠ Pi.single i 1) : #{ξ : n → F | ξ i = 1 ∧ ξ ⬝ᵥ z = 1} = 0 := by
  obtain ⟨c, rfl⟩ := exists_eq_smul_single_iff.2 hz
  refine card_eq_zero.2 (filter_eq_empty_iff.2 fun ξ _ ⟨h_one, h_dot⟩ ↦ ?_)
  exact h_ne (by simp_all)

/-- If `f` has the value `y` at the non-zero multiples of `e_i`, then its sum over the non-zero
vectors is `(q - 1) • y` plus its sum off the line of `e_i`, over a field of `q` elements. -/
lemma sum_ne_zero_eq_smul_add_sum_compl_line {W : Type} [AddCommGroup W] [Module ℂ W]
    {f : (n → F) → W} {y : W} (hf : ∀ z : n → F, z ≠ 0 → (∀ j ≠ i, z j = 0) → f z = y) :
    ∑ z : n → F with z ≠ 0, f z =
      ((Fintype.card F : ℂ) - 1) • y +
        ∑ z ∈ ({z : n → F | ∀ j ≠ i, z j = 0} : Finset (n → F))ᶜ, f z := by
  let L : Finset (n → F) := {z : n → F | ∀ j ≠ i, z j = 0}
  have h_zero : (0 : n → F) ∈ L := by simp [L]
  have h_line : ∑ z ∈ L.erase 0, f z = ((Fintype.card F : ℂ) - 1) • y := by
    rw [sum_eq_card_nsmul fun z hz ↦
        hf z (ne_of_mem_erase hz) (by simpa [L] using mem_of_mem_erase hz),
      card_erase_of_mem h_zero, card_line, ← Nat.cast_smul_eq_nsmul ℂ,
      Nat.cast_pred Fintype.card_pos]
  refine add_right_cancel (b := f 0) ?_
  calc ∑ z : n → F with z ≠ 0, f z + f 0
    _ = ∑ z ∈ L, f z + ∑ z ∈ Lᶜ, f z := by
      rw [filter_ne', sum_erase_add _ _ (mem_univ _), sum_add_sum_compl L]
    _ = ((Fintype.card F : ℂ) - 1) • y + ∑ z ∈ Lᶜ, f z + f 0 := by
      rw [← sum_erase_add L f h_zero, h_line, add_right_comm]

/-- Over a field of `q` elements and in dimension `n`, let `f` have the value `y` at the non-zero
multiples of `e_i`. Then the sum of `f z` over all forms `ξ` with `ξ e_i = 1` and all vectors `z`
with `ξ z = 1` is `q ^ (n - 2)` times the sum of `y` and all `f z` with `z ≠ 0`. Here `ξ` stands
for a hyperplane that does not contain `e_i`, and `z` for a line outside this hyperplane. -/
lemma sum_sum_dotProduct_eq_one_eq_smul {W : Type} [AddCommGroup W] [Module ℂ W] {f : (n → F) → W}
    {y : W} (hf : ∀ z : n → F, z ≠ 0 → (∀ j ≠ i, z j = 0) → f z = y) :
    ∑ ξ : n → F with ξ i = 1, ∑ z : n → F with ξ ⬝ᵥ z = 1, f z =
      (Fintype.card F : ℂ) ^ (Fintype.card n - 2 : ℤ) • (y + ∑ z : n → F with z ≠ 0, f z) := by
  -- Exchange the sums: a vector `z` occurs `N z` times. This is `q ^ (n - 1)` for `z = e_i`,
  -- zero for its other multiples and `q ^ (n - 2)` off the line `L` of `e_i`.
  set q : ℂ := ((Fintype.card F : ℕ) : ℂ) with hq_def
  have hq : q ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  set d : ℂ := q ^ (Fintype.card n - 2 : ℤ)
  have hd : d * q ^ 2 = q ^ Fintype.card n := by simp [d, zpow_sub₀ hq, hq]
  let L : Finset (n → F) := {z : n → F | ∀ j ≠ i, z j = 0}
  let N (z : n → F) : ℕ := #{ξ : n → F | ξ i = 1 ∧ ξ ⬝ᵥ z = 1}
  let e : n → F := Pi.single i 1
  have h_on : ∑ z ∈ L, N z • f z = (d * q) • y := by
    have he : ∀ j ≠ i, e j = 0 := fun j hj ↦ Pi.single_eq_of_ne hj 1
    have h_count : (N e : ℂ) = d * q := by
      refine mul_right_cancel₀ hq ?_
      rw [mul_assoc, ← sq, hd, show N e = #{ξ : n → F | ξ i = 1} by simp [N, e], hq_def]
      exact_mod_cast card_forms_missing_line (F := F) i
    have h_others : ∀ z ∈ L, z ≠ e → N z • f z = 0 := fun z hz h_ne ↦ by
      simp [N, card_forms_eq_zero_of_ne_single (by simpa [L] using hz) h_ne]
    rw [sum_eq_single_of_mem e (by simpa [L] using he) h_others,
      hf e (Pi.single_ne_zero_iff.2 one_ne_zero) he, ← Nat.cast_smul_eq_nsmul ℂ, h_count]
  have h_off : ∑ z ∈ Lᶜ, N z • f z = d • ∑ z ∈ Lᶜ, f z := by
    rw [smul_sum]
    refine sum_congr rfl fun z hz ↦ ?_
    obtain ⟨j, hj, hzj⟩ : ∃ j ≠ i, z j ≠ 0 := by simpa [L] using hz
    have h_count : (N z : ℂ) = d := by
      refine mul_right_cancel₀ (pow_ne_zero 2 hq) ?_
      rw [hd, hq_def]
      exact_mod_cast card_forms_taking_one_at_two_vectors_mul_sq hj hzj
    rw [← Nat.cast_smul_eq_nsmul ℂ, h_count]
  have h_all : ∑ z : n → F with z ≠ 0, f z = (q - 1) • y + ∑ z ∈ Lᶜ, f z :=
    sum_ne_zero_eq_smul_add_sum_compl_line hf
  calc ∑ ξ : n → F with ξ i = 1, ∑ z : n → F with ξ ⬝ᵥ z = 1, f z
    _ = ∑ z : n → F, N z • f z := sum_forms_sum_eq_sum_card_smul i f
    _ = (d * q) • y + d • ∑ z ∈ Lᶜ, f z := by rw [← sum_add_sum_compl L, h_on, h_off]
    _ = d • (y + ∑ z : n → F with z ≠ 0, f z) := by
      rw [h_all]
      module

end Field

/-! ### Matrices that keep a line -/

section Shape

open Polynomial

variable {F n : Type} [Field F] [Fintype n] [DecidableEq n] {i : n} {M N : Matrix n n F}

/-- The matrix `M` has the block shape `(∗ ∗; 0 g')` with `g'` invertible, where the first block is
the index `i`. -/
structure KeepsLine (i : n) (M : Matrix n n F) : Prop where
  /-- The `i`-th column vanishes off the diagonal. -/
  col_eq_zero : ∀ j ≠ i, M j i = 0
  /-- The block on the other indices is invertible. -/
  block_det_ne_zero : (M.toSquareBlockProp (· ≠ i)).det ≠ 0

/-- If `KeepsLine i N`, so that the column `i` of `N` vanishes off the diagonal and its block on
the other indices is invertible, then the diagonal entry at `i` of `M * N` is the product of those
of `M` and `N`. -/
lemma KeepsLine.mul_apply_self (hN : KeepsLine i N) : (M * N) i i = M i i * N i i := by
  rw [mul_apply]
  exact Fintype.sum_eq_single i fun j hj ↦ mul_eq_zero_of_right _ (hN.col_eq_zero j hj)

/-- If `M` and `N` satisfy `KeepsLine i` (their column `i` vanishes off the diagonal and their
block on the other indices is invertible), then so does `M * N`. -/
lemma KeepsLine.mul (hM : KeepsLine i M) (hN : KeepsLine i N) : KeepsLine i (M * N) where
  col_eq_zero j hj := by
    rw [mul_apply, Fintype.sum_eq_single i fun l hl ↦ mul_eq_zero_of_right _ (hN.col_eq_zero l hl),
      hM.col_eq_zero j hj, zero_mul]
  block_det_ne_zero := by
    have h_block : (M * N).toSquareBlockProp (· ≠ i) =
        M.toSquareBlockProp (· ≠ i) * N.toSquareBlockProp (· ≠ i) := by
      ext a b
      have h_corner : M a i * N i b = 0 := mul_eq_zero_of_left (hM.col_eq_zero a a.2) _
      simp only [toSquareBlockProp_def, mul_apply, of_apply]
      rw [← sum_subtype (univ.erase i) (by simp) fun l : n ↦ M a l * N l b,
        sum_erase univ (f := fun l : n ↦ M a l * N l b) h_corner]
    rw [h_block, det_mul]
    exact mul_ne_zero hM.block_det_ne_zero hN.block_det_ne_zero

/-- If the column `i` of `M` vanishes off the diagonal, then `det M` is the product of `M i i` and
the determinant of the block on the other indices. -/
lemma det_eq_mul_det_block {R : Type} [CommRing R] {M : Matrix n n R} (hM : ∀ j ≠ i, M j i = 0) :
    M.det = M i i * (M.toSquareBlockProp (· ≠ i)).det := by
  have h_corner : (M.toSquareBlockProp (· = i)).det = M i i := by
    rw [det_eq_elem_of_subsingleton _ ⟨i, rfl⟩, toSquareBlockProp_def, of_apply]
  rw [← h_corner]
  -- `convert` matches the two `Fintype` instances on the indices equal to `i`.
  convert twoBlockTriangular_det M (· = i) fun a ha b hb ↦ by simpa [hb] using hM a ha

/-- An element of `parabolic (· ≠ i)`, the stabiliser of the line of `e_i`, has the block shape
`KeepsLine i`: its column `i` vanishes off the diagonal and the block on the other indices is
invertible. -/
lemma keepsLine_of_mem_parabolic {g : GL n F} (hg : g ∈ parabolic (· ≠ i)) :
    KeepsLine i (g : Matrix n n F) where
  col_eq_zero := mem_parabolic_ne.1 hg
  block_det_ne_zero := right_ne_zero_of_mul
    ((det_eq_mul_det_block (mem_parabolic_ne.1 hg)).symm.trans_ne g.det_ne_zero)

/-- If the column `i` of `M` is zero, also at the diagonal, and the block on the other indices is
invertible, then `0` is a simple root of the characteristic polynomial of `M`. -/
lemma KeepsLine.rootMultiplicity_charpoly (hM : KeepsLine i M) (h_zero : M i i = 0) :
    M.charpoly.rootMultiplicity 0 = 1 := by
  set M' : Matrix {j : n // j ≠ i} {j : n // j ≠ i} F := M.toSquareBlockProp (· ≠ i)
  have h_factor : M.charpoly = X * M'.charpoly := by
    have h_block : M.charmatrix.toSquareBlockProp (· ≠ i) = M'.charmatrix := by
      ext1 a b
      simp [M', toSquareBlockProp_def, charmatrix_apply, diagonal_apply, Subtype.ext_iff]
    rw [Matrix.charpoly, det_eq_mul_det_block (i := i) fun j hj ↦ by simp [hj, hM.col_eq_zero j hj],
      h_block, charmatrix_apply_eq, h_zero, C_0, sub_zero, Matrix.charpoly]
  have h_root : ¬ M'.charpoly.IsRoot 0 := fun h_root ↦ hM.block_det_ne_zero <| by
    rw [det_eq_sign_charpoly_coeff, coeff_zero_eq_eval_zero, h_root.eq_zero, mul_zero]
  rw [h_factor, rootMultiplicity_mul (mul_ne_zero X_ne_zero M'.charpoly_monic.ne_zero),
    rootMultiplicity_eq_zero h_root, add_zero]
  simpa only [C_0, sub_zero] using rootMultiplicity_X_sub_C_self (x := (0 : F))

end Shape

end New
