import Mathlib.LinearAlgebra.Matrix.Block
import IPRADerivations.Foundations.NullVectorDeterminant
import IPRADerivations.Geometry.TetrahedralGram

/-!
# The Hankel determinant by a triangular congruence (`bell_numbers_ipra`, `thm:hankel`, `cor:strict-logconvex`)

Packet: `combinatorics/bell_numbers_ipra`, theorem `thm:hankel`:
`det(B_{i+j})_{0 ≤ i,j ≤ N} = ∏_{j=0}^{N} j!`. Proof: "The coefficient matrix `U` expressing
`P_0, …, P_N` in the monomial basis is lower triangular with diagonal entries one. Thus, by
multiplication of finite matrices, `U (B_{i+j}) Uᵀ = diag(0!, 1!, …, N!)`. Taking determinants,
defined by their finite permutation sums, proves (the formula), since `det U = 1`." And
corollary `cor:strict-logconvex`: "the entirely finite identity
`L(f²) L(g²) − L(fg)² = Σ_{i<j} i! j! (c_i d_j − c_j d_i)²` follows by expansion."

Derived for integer terms and every size (a parameter of the Lean statements):

* `congruence_ring`, `diag`, `toZ_diag`, `congruence_det`: if `U H Uᵀ = diag(d_0, …, d_N)` with
  `U` lower triangular with unit diagonal, then `det H = ∏_j d_j`. With `d_j = j!` and the
  Charlier coefficient matrix this is the determinant step of `thm:hankel`;
* `lagrange_ring`, `gram_lagrange`: for weights `w` and coefficient vectors `c`, `d`,
  `2 ((Σ w_i c_i²)(Σ w_i d_i²) − (Σ w_i c_i d_i)²) = Σ_i Σ_j w_i w_j (c_i d_j − c_j d_i)²`:
  the displayed identity of `cor:strict-logconvex`, with the sum over `i < j` written as half
  of the sum over all pairs.

Not derived: the Charlier orthogonality `L(P_r P_s) = r! δ_{rs}` (hence the congruence itself
for the Bell numbers), and the positivity step that gives `B_n² < B_{n−1} B_{n+1}`.
-/

namespace LeanProofs.IPRA.Combinatorics.HankelCongruence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.NullVectorDeterminant
open LeanProofs.IPRA.Geometry.TetrahedralGram (prodFin toZ_prodFin)
open Syn Matrix
open scoped Fm

section Ring

variable {R : Type*} [CommRing R] {k : ℕ}

/-- A congruence by a unit lower triangular matrix to a diagonal matrix computes the
determinant. -/
theorem congruence_ring (U H : Matrix (Fin k) (Fin k) R) (d : Fin k → R)
    (hlow : ∀ i j, i < j → U i j = 0) (hdiag : ∀ i, U i i = 1)
    (h : U * H * Uᵀ = Matrix.diagonal d) : H.det = ∏ i, d i := by
  have hU : U.det = 1 := by
    rw [Matrix.det_of_lowerTriangular U (fun i j h => hlow i j (by simpa using h))]
    simp [hdiag]
  have e := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hU, Matrix.det_diagonal] at e
  linear_combination e

/-- Lagrange's identity with weights. -/
theorem lagrange_ring (w c d : Fin k → R) :
    2 * ((∑ i, w i * c i ^ 2) * (∑ i, w i * d i ^ 2) - (∑ i, w i * c i * d i) ^ 2) =
      ∑ i, ∑ j, w i * w j * (c i * d j - c j * d i) ^ 2 := by
  have e : ∀ i j, w i * w j * (c i * d j - c j * d i) ^ 2 =
      w i * c i ^ 2 * (w j * d j ^ 2) - 2 * (w i * c i * d i * (w j * c j * d j)) +
        w i * d i ^ 2 * (w j * c j ^ 2) := fun i j => by ring
  have e' : (∑ i, ∑ j, w i * w j * (c i * d j - c j * d i) ^ 2) =
      (∑ i, ∑ j, w i * c i ^ 2 * (w j * d j ^ 2)) -
        2 * (∑ i, ∑ j, w i * c i * d i * (w j * c j * d j)) +
        ∑ i, ∑ j, w i * d i ^ 2 * (w j * c j ^ 2) := by
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [e', ← Finset.sum_mul_sum, ← Finset.sum_mul_sum, ← Finset.sum_mul_sum]
  ring

end Ring

variable {n : ℕ} {Γ : List (Fm PTm n)} {k : ℕ}

/-- The diagonal matrix of a family of integer terms. -/
def diag (d : Vec k n) : Mat k n := fun i j => if i = j then d i else ZT.natLit 0

theorem toZ_diag (d : Vec k n) : Mat.toZ Γ (diag d) = Matrix.diagonal (Vec.toZ Γ d) := by
  ext i j
  by_cases h : i = j <;> simp [diag, Mat.toZ, Vec.toZ, h]

/-- `thm:hankel`, the determinant step: `U H Uᵀ = diag(d)` with `U` unit lower triangular
gives `det H = ∏ d_j`. -/
theorem congruence_det {U H : Mat k n} {d : Vec k n}
    (hlow : ∀ i j, i < j → (Γ ⊢[PRAAx] ZT.eq (U i j) (ZT.natLit 0)))
    (hdiag : ∀ i, Γ ⊢[PRAAx] ZT.eq (U i i) (ZT.natLit 1))
    (h : Γ ⊢[PRAAx] Mat.eqFm (Mat.mul (Mat.mul U H) (Mat.transpose U)) (diag d)) :
    Γ ⊢[PRAAx] ZT.eq (Mat.det H) (prodFin d) := by
  have e := Mat.toZ_eq h
  rw [Mat.toZ_mul, Mat.toZ_mul, Mat.toZ_transpose, toZ_diag] at e
  refine ZT.derive ?_
  rw [Mat.toZ_det, toZ_prodFin]
  refine congruence_ring _ _ _ (fun i j hij => ?_) (fun i => ?_) e
  · simpa using ZT.toZ_eq (hlow i j hij)
  · simpa using ZT.toZ_eq (hdiag i)

/-- `cor:strict-logconvex`, the finite identity: the Gram determinant of two coefficient
vectors as a sum of squares of `2 × 2` minors. -/
theorem gram_lagrange (w c d : Vec k n) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.natLit 2 * ((ZT.sumFin fun i => w i * ZT.sq (c i)) *
          (ZT.sumFin fun i => w i * ZT.sq (d i)) -
        ZT.sq (ZT.sumFin fun i => w i * c i * d i)))
      (ZT.sumFin fun i => ZT.sumFin fun j => w i * w j * ZT.sq (c i * d j - c j * d i)) :=
  ZT.derive (by
    simp only [ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_sq, ZT.toZ_sumFin, ZT.toZ_natLit, Nat.cast_ofNat]
    exact lagrange_ring _ _ _)

end LeanProofs.IPRA.Combinatorics.HankelCongruence
