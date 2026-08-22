import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Block factorization of tied Leibniz sums

This module isolates the combinatorics of a tropical minimizing fiber.
When the surviving permutations preserve the fibers of a block map, their
signed Leibniz sum is the determinant of the corresponding block-diagonal
mask, hence the product of the determinants of the individual blocks.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Finset Matrix

/-- Permutations preserving every fiber of a block map. -/
noncomputable def blockPreservingPermutations
    {n o : Type*} [Fintype n] [DecidableEq n] [DecidableEq o]
    (b : n → o) : Finset (Equiv.Perm n) :=
  Finset.univ.filter fun σ ↦ ∀ i, b (σ i) = b i

@[simp]
theorem mem_blockPreservingPermutations
    {n o : Type*} [Fintype n] [DecidableEq n] [DecidableEq o]
    {b : n → o} {sigma : Equiv.Perm n} :
    sigma ∈ blockPreservingPermutations b ↔ ∀ i, b (sigma i) = b i := by
  classical
  simp [blockPreservingPermutations]

/-- Delete all entries joining distinct fibers of `b`. -/
def blockDiagonalMask
    {n o R : Type*} [DecidableEq o] [Zero R]
    (b : n → o) (A : Matrix n n R) : Matrix n n R :=
  fun i j ↦ if b i = b j then A i j else 0

@[simp]
theorem blockDiagonalMask_apply_of_eq
    {n o R : Type*} [DecidableEq o] [Zero R]
    (b : n → o) (A : Matrix n n R) {i j : n} (h : b i = b j) :
    blockDiagonalMask b A i j = A i j := by
  simp [blockDiagonalMask, h]

@[simp]
theorem blockDiagonalMask_apply_of_ne
    {n o R : Type*} [DecidableEq o] [Zero R]
    (b : n → o) (A : Matrix n n R) {i j : n} (h : b i ≠ b j) :
    blockDiagonalMask b A i j = 0 := by
  simp [blockDiagonalMask, h]

/-- **Abstract tied-fiber factorization.**  The signed Leibniz sum over all
permutations preserving the prescribed blocks is the product of the
determinants of the corresponding square blocks.

The block sizes may vary and empty blocks contribute determinant `1`. -/
theorem sum_blockPreserving_eq_prod_blockDet
    {n o R : Type*} [Fintype n] [DecidableEq n]
    [Fintype o] [DecidableEq o] [LinearOrder o] [CommRing R]
    (b : n → o) (A : Matrix n n R) :
    (∑ sigma ∈ blockPreservingPermutations b,
        (Equiv.Perm.sign sigma : R) * ∏ i, A (sigma i) i) =
      ∏ k : o, (A.toSquareBlock b k).det := by
  classical
  let B : Matrix n n R := blockDiagonalMask b A
  have hpreserve :
      (∑ sigma ∈ blockPreservingPermutations b,
          (Equiv.Perm.sign sigma : R) * ∏ i, A (sigma i) i) =
        ∑ sigma ∈ blockPreservingPermutations b,
          (Equiv.Perm.sign sigma : R) * ∏ i, B (sigma i) i := by
    apply Finset.sum_congr rfl
    intro sigma hsigma
    have hsigma' : ∀ i, b (sigma i) = b i :=
      mem_blockPreservingPermutations.mp hsigma
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    exact (blockDiagonalMask_apply_of_eq b A (hsigma' i)).symm
  have hnonpreserve :
      (∑ sigma ∈ blockPreservingPermutations b,
          (Equiv.Perm.sign sigma : R) * ∏ i, B (sigma i) i) =
        ∑ sigma : Equiv.Perm n,
          (Equiv.Perm.sign sigma : R) * ∏ i, B (sigma i) i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro sigma _ hsigma
    have hsigma' : ¬ ∀ i, b (sigma i) = b i := by
      simpa only [mem_blockPreservingPermutations] using hsigma
    obtain ⟨i, hi⟩ := not_forall.mp hsigma'
    rw [Finset.prod_eq_zero (Finset.mem_univ i), mul_zero]
    exact blockDiagonalMask_apply_of_ne b A hi
  have hsum :
      (∑ sigma ∈ blockPreservingPermutations b,
          (Equiv.Perm.sign sigma : R) * ∏ i, A (sigma i) i) = B.det := by
    rw [hpreserve, hnonpreserve, Matrix.det_apply']
  have htri : B.BlockTriangular b := by
    intro i j hij
    exact blockDiagonalMask_apply_of_ne b A (ne_of_gt hij)
  rw [hsum, htri.det_fintype]
  apply Finset.prod_congr rfl
  intro k _
  congr 1
  ext i j
  exact blockDiagonalMask_apply_of_eq b A (i.property.trans j.property.symm)

/-- A fixed row alignment `rho` permits different prescribed row and column
blocks.  After pulling the row blocks back along `rho`, the tied permutations
preserve the column block map `b`; their sum acquires only the single overall
sign of `rho` and still factors into block determinants. -/
theorem sum_basePerm_mul_blockPreserving_eq_sign_mul_prod_blockDet
    {n o R : Type*} [Fintype n] [DecidableEq n]
    [Fintype o] [DecidableEq o] [LinearOrder o] [CommRing R]
    (b : n → o) (A : Matrix n n R) (rho : Equiv.Perm n) :
    (∑ sigma ∈ blockPreservingPermutations b,
        (Equiv.Perm.sign (rho * sigma) : R) * ∏ i, A (rho (sigma i)) i) =
      (Equiv.Perm.sign rho : R) *
        ∏ k : o, ((A.submatrix rho id).toSquareBlock b k).det := by
  classical
  calc
    (∑ sigma ∈ blockPreservingPermutations b,
        (Equiv.Perm.sign (rho * sigma) : R) * ∏ i, A (rho (sigma i)) i) =
      (Equiv.Perm.sign rho : R) *
        ∑ sigma ∈ blockPreservingPermutations b,
          (Equiv.Perm.sign sigma : R) *
            ∏ i, (A.submatrix rho id) (sigma i) i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro sigma _
      simp only [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul,
        Matrix.submatrix_apply, id_eq]
      ring
    _ = (Equiv.Perm.sign rho : R) *
        ∏ k : o, ((A.submatrix rho id).toSquareBlock b k).det := by
      rw [sum_blockPreserving_eq_prod_blockDet]

/-- **Variable-size consecutive-power blocks.**  Suppose every fiber block,
after reindexing by `e k`, is the ordinary Vandermonde matrix on `x k`.
Then the tied signed sum is the product of all within-block Vandermonde
products.  Unlike the concrete product-indexed corollary below, the block
sizes `s k` may vary with `k`. -/
theorem sum_blockPreserving_eq_prod_vandermonde_of_reindex
    {n o R : Type*} [Fintype n] [DecidableEq n]
    [Fintype o] [DecidableEq o] [LinearOrder o] [CommRing R]
    (b : n → o) (A : Matrix n n R) (s : o → ℕ)
    (x : ∀ k : o, Fin (s k) → R)
    (e : ∀ k : o, {i : n // b i = k} ≃ Fin (s k))
    (hpower : ∀ k : o,
      Matrix.reindex (e k) (e k) (A.toSquareBlock b k) =
        Matrix.vandermonde (x k)) :
    (∑ sigma ∈ blockPreservingPermutations b,
        (Equiv.Perm.sign sigma : R) * ∏ i, A (sigma i) i) =
      ∏ k : o, ∏ i : Fin (s k),
        ∏ j ∈ Finset.Ioi i, (x k j - x k i) := by
  classical
  rw [sum_blockPreserving_eq_prod_blockDet b A]
  apply Finset.prod_congr rfl
  intro k _
  calc
    (A.toSquareBlock b k).det =
        (Matrix.reindex (e k) (e k) (A.toSquareBlock b k)).det :=
      (Matrix.det_reindex_self (e k) (A.toSquareBlock b k)).symm
    _ = (Matrix.vandermonde (x k)).det := by rw [hpower k]
    _ = ∏ i : Fin (s k), ∏ j ∈ Finset.Ioi i, (x k j - x k i) :=
      Matrix.det_vandermonde (x k)

/-! ## Consecutive-power blocks -/

/-- The fiber of `Prod.snd` over `k` is canonically equivalent to the common
within-block index type. -/
def prodSndFiberEquiv {m o : Type*} (k : o) :
    {a : m × o // a.2 = k} ≃ m where
  toFun a := a.1.1
  invFun i := ⟨(i, k), rfl⟩
  left_inv a := by
    rcases a with ⟨⟨i, l⟩, hl⟩
    simp only at hl
    subst l
    rfl
  right_inv _ := rfl

@[simp]
theorem prodSndFiberEquiv_apply {m o : Type*} (k : o)
    (a : {a : m × o // a.2 = k}) :
    prodSndFiberEquiv k a = a.1.1 :=
  rfl

@[simp]
theorem prodSndFiberEquiv_symm_apply {m o : Type*} (k : o) (i : m) :
    (prodSndFiberEquiv k).symm i = ⟨(i, k), rfl⟩ :=
  rfl

/-- A global matrix whose restriction to the block `k` is the Vandermonde
matrix on the nodes `x k`.  Its values between distinct blocks are immaterial
for the block-preserving Leibniz sum. -/
def consecutivePowerBlockMatrix
    {r : ℕ} {o R : Type*} [CommRing R]
    (x : o → Fin r → R) : Matrix (Fin r × o) (Fin r × o) R :=
  fun row col ↦ (x col.2 row.1) ^ (col.1 : ℕ)

@[simp]
theorem consecutivePowerBlockMatrix_apply
    {r : ℕ} {o R : Type*} [CommRing R]
    (x : o → Fin r → R) (row col : Fin r × o) :
    consecutivePowerBlockMatrix x row col =
      (x col.2 row.1) ^ (col.1 : ℕ) :=
  rfl

/-- Reindexing one consecutive-power block by its within-block coordinate
produces Mathlib's ordinary Vandermonde matrix. -/
theorem reindex_toSquareBlock_consecutivePowerBlockMatrix
    {r : ℕ} {o R : Type*} [CommRing R]
    (x : o → Fin r → R) (k : o) :
    Matrix.reindex (prodSndFiberEquiv k) (prodSndFiberEquiv k)
        ((consecutivePowerBlockMatrix x).toSquareBlock Prod.snd k) =
      Matrix.vandermonde (x k) := by
  ext i j
  rfl

/-- **Consecutive-power tied-fiber factorization.**  If each block uses the
consecutive powers `0, ..., r - 1`, the signed sum over block-preserving
permutations is the product of the ordinary Vandermonde products of the block
nodes.  This is the abstract algebraic content of the report's
`initial-two`/`initial-three` formulas, before inserting their odd unit row
factors. -/
theorem sum_blockPreserving_consecutivePowers_eq_prod_vandermonde
    {r : ℕ} {o R : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    [CommRing R] (x : o → Fin r → R) :
    (∑ sigma ∈ blockPreservingPermutations (Prod.snd : Fin r × o → o),
        (Equiv.Perm.sign sigma : R) *
          ∏ i : Fin r × o, (x i.2 (sigma i).1) ^ (i.1 : ℕ)) =
      ∏ k : o, ∏ i : Fin r, ∏ j ∈ Finset.Ioi i, (x k j - x k i) := by
  classical
  change
    (∑ sigma ∈ blockPreservingPermutations (Prod.snd : Fin r × o → o),
        (Equiv.Perm.sign sigma : R) *
          ∏ i : Fin r × o, consecutivePowerBlockMatrix x (sigma i) i) = _
  rw [sum_blockPreserving_eq_prod_blockDet
    (Prod.snd : Fin r × o → o) (consecutivePowerBlockMatrix x)]
  apply Finset.prod_congr rfl
  intro k _
  calc
    ((consecutivePowerBlockMatrix x).toSquareBlock Prod.snd k).det =
        (Matrix.reindex (prodSndFiberEquiv k) (prodSndFiberEquiv k)
          ((consecutivePowerBlockMatrix x).toSquareBlock Prod.snd k)).det :=
      (Matrix.det_reindex_self (prodSndFiberEquiv k)
        ((consecutivePowerBlockMatrix x).toSquareBlock Prod.snd k)).symm
    _ = (Matrix.vandermonde (x k)).det := by
      rw [reindex_toSquareBlock_consecutivePowerBlockMatrix]
    _ = ∏ i : Fin r, ∏ j ∈ Finset.Ioi i, (x k j - x k i) :=
      Matrix.det_vandermonde (x k)

end LeanProofs.TwoBaseIntegerExponent
