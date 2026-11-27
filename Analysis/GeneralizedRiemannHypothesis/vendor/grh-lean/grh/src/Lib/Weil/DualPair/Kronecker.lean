import Lib.General.Groups.CongruenceSubgroups

/-!
# The action x ↦ hxg⁻¹ on matrices as a map of unitary groups

`New.U.kroneckerHom` sends `(g, h)` in `U S × U T` to the Kronecker product `h ⊗ₖ g⁻¹ᵀ`, the matrix
of `x ↦ h x g⁻¹` on matrices indexed by pairs (row, column). Here `New.U J` is the group of
invertible `g` with `gᴴ J g = J`.

* `New.kroneckerGL`: the Kronecker product of two invertible matrices, as an invertible matrix.
* `New.U.kroneckerHom`: the homomorphism of unitary groups.
* `New.map_kronecker`: applying a ring homomorphism entrywise commutes with the Kronecker product.

## Relation to the literature

Known; see `Lib.Weil.DualPair.ThetaLiftConvergence` for sources.
-/

open Matrix Kronecker

variable {m n R : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The Kronecker product x ⊗ y of invertible matrices x and y over a commutative semiring, as
an invertible matrix with inverse x⁻¹ ⊗ y⁻¹. -/
@[local simp]
noncomputable def New.kroneckerGL [CommSemiring R] (x : GL m R) (y : GL n R) : GL (m × n) R where
  val := x ⊗ₖ y
  inv := x⁻¹.val ⊗ₖ y⁻¹.val
  val_inv := by simp [← mul_kronecker_mul]
  inv_val := by simp [← mul_kronecker_mul]

/-- For SK = 1 and J = T ⊗ Kᵀ, the homomorphism (g, h) ↦ h ⊗ (g⁻¹)ᵀ from U(S) × U(T) to U(J). -/
@[simps! apply_coe_val]
noncomputable def New.U.kroneckerHom [CommRing R] [StarRing R] {S K : Matrix n n R}
    {T : Matrix m m R} {J : Matrix (m × n) (m × n) R} (hS : S * K = 1) (h : J = T ⊗ₖ Kᵀ) :
    U S × U T →* U J :=
  MonoidHom.mk'
    (fun p ↦
      ⟨kroneckerGL p.2 (transposeGL p.1⁻¹), by
        -- For `p = (x, y)`: the Kronecker product of `yᴴ T y = T` and the inverse transpose of
        -- `xᴴ S x = S`.
        simpa [U, inv_eq_right_inv hS, h, conjTranspose_nonsing_inv, conjTranspose_kronecker,
          conjTranspose_transpose_eq_transpose_conjTranspose, ← mul_kronecker_mul,
          Matrix.mul_inv_rev] using!
          congr($(p.2.2) ⊗ₖ $(p.1.2)⁻¹ᵀ)⟩)
    (fun _ _ ↦ Subtype.ext <| Units.ext <| by simp [← mul_kronecker_mul])

/-- Applying a ring homomorphism `f` entrywise commutes with the Kronecker product:
(A ⊗ B).map f = A.map f ⊗ B.map f. -/
lemma New.map_kronecker {a b c d R S : Type*} [Ring R] [Ring S] (f : R →+* S) (A : Matrix a b R)
    (B : Matrix c d R) :
    (A ⊗ₖ B).map f = A.map f ⊗ₖ B.map f := by
  aesop
