import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

/-!
# Candidate alternants from rational approximations

Report 10 observes that the arithmetic progression of candidate exponents

`(d - 1) p + i (q t - p)`, for `0 ≤ i < d`,

turns the corresponding exponential determinant into an ordinary Vandermonde determinant.
This file formalizes that exact identity.  The proof is entirely finite algebra: factor the
common scale from each column, transpose the remaining Vandermonde matrix, and use Mathlib's
Vandermonde determinant formula.

No irrationality estimate is asserted.  The subsequent mean-value upper bound and its
Diophantine interpretation remain analytic steps in the paper layer.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open scoped BigOperators

noncomputable section

/-! ## An affine-exponent Vandermonde factorization over a ring -/

/-- A column-scaled, transposed Vandermonde matrix: row `i`, column `j` is
`scale j * node j ^ i`. -/
def affineExponentVandermonde {R : Type*} [CommRing R]
    (N : ℕ) (scale node : Fin N → R) : Matrix (Fin N) (Fin N) R :=
  Matrix.of fun i j ↦ scale j * node j ^ (i : ℕ)

@[simp] theorem affineExponentVandermonde_apply {R : Type*} [CommRing R]
    (N : ℕ) (scale node : Fin N → R) (i j : Fin N) :
    affineExponentVandermonde N scale node i j = scale j * node j ^ (i : ℕ) := rfl

/-- **Exact affine-exponent determinant.**  Factoring `scale j` from column `j` leaves the
transpose of the ordinary Vandermonde matrix on `node`. -/
theorem det_affineExponentVandermonde {R : Type*} [CommRing R]
    (N : ℕ) (scale node : Fin N → R) :
    (affineExponentVandermonde N scale node).det =
      (∏ j, scale j) *
        ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (node j - node i) := by
  change (Matrix.of fun i j ↦ scale j * (Matrix.vandermonde node).transpose i j).det = _
  rw [Matrix.det_mul_row, Matrix.det_transpose, Matrix.det_vandermonde]

/-! ## Real-power progressions -/

/-- Matrix of real powers whose row exponents form the affine progression `a + iε`. -/
def rpowAffineExponentMatrix
    (N : ℕ) (s : Fin N → ℝ) (a ε : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j ↦ s j ^ (a + (i : ℝ) * ε)

@[simp] theorem rpowAffineExponentMatrix_apply
    (N : ℕ) (s : Fin N → ℝ) (a ε : ℝ) (i j : Fin N) :
    rpowAffineExponentMatrix N s a ε i j = s j ^ (a + (i : ℝ) * ε) := rfl

private theorem rpow_nat_mul (s ε : ℝ) (i : ℕ) (hs : 0 < s) :
    s ^ ((i : ℝ) * ε) = (s ^ ε) ^ i := by
  rw [mul_comm, Real.rpow_mul hs.le, Real.rpow_natCast]

/-- A positive-base real-power progression is literally an affine-exponent Vandermonde
matrix with column scale `s^a` and node `s^ε`. -/
theorem rpowAffineExponentMatrix_eq_affineExponentVandermonde
    (N : ℕ) (s : Fin N → ℝ) (a ε : ℝ) (hs : ∀ j, 0 < s j) :
    rpowAffineExponentMatrix N s a ε =
      affineExponentVandermonde N (fun j ↦ s j ^ a) (fun j ↦ s j ^ ε) := by
  ext i j
  rw [rpowAffineExponentMatrix_apply, affineExponentVandermonde_apply,
    Real.rpow_add (hs j), rpow_nat_mul (s j) ε (i : ℕ) (hs j)]

/-- **Exact Vandermonde identity for an affine progression of real exponents.** -/
theorem det_rpowAffineExponentMatrix
    (N : ℕ) (s : Fin N → ℝ) (a ε : ℝ) (hs : ∀ j, 0 < s j) :
    (rpowAffineExponentMatrix N s a ε).det =
      (∏ j, s j ^ a) *
        ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (s j ^ ε - s i ^ ε) := by
  rw [rpowAffineExponentMatrix_eq_affineExponentVandermonde N s a ε hs,
    det_affineExponentVandermonde]

/-! ## The report's rational-approximation specialization -/

/-- The approximation error `ε = q t - p`. -/
def candidateApproximationError (p q : ℕ) (t : ℝ) : ℝ :=
  (q : ℝ) * t - (p : ℝ)

/-- The common exponent `(d-1)p` in the report's clustered-candidate construction. -/
def candidateClusterBaseExponent (d p : ℕ) : ℝ :=
  ((d - 1) * p : ℕ)

/-- The determinant matrix attached to the exponent progression
`(d-1)p + i(qt-p)`. -/
def candidateApproximationAlternant
    (d p q : ℕ) (t : ℝ) (s : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  rpowAffineExponentMatrix d s (candidateClusterBaseExponent d p)
    (candidateApproximationError p q t)

@[simp] theorem candidateApproximationAlternant_apply
    (d p q : ℕ) (t : ℝ) (s : Fin d → ℝ) (i j : Fin d) :
    candidateApproximationAlternant d p q t s i j =
      s j ^ (candidateClusterBaseExponent d p +
        (i : ℝ) * candidateApproximationError p q t) := rfl

/-- The affine exponent is the nonnegative candidate combination
`(d-1-i)p + iqt` used in the report. -/
theorem candidateClusterExponent_eq_semigroupCombination
    {d : ℕ} (p q : ℕ) (t : ℝ) (i : Fin d) :
    candidateClusterBaseExponent d p +
        (i : ℝ) * candidateApproximationError p q t =
      (((d - 1 - (i : ℕ)) * p : ℕ) : ℝ) + (((i : ℕ) * q : ℕ) : ℝ) * t := by
  have hi : (i : ℕ) ≤ d - 1 := by omega
  simp only [candidateClusterBaseExponent, candidateApproximationError, Nat.cast_mul,
    Nat.cast_sub hi]
  ring

/-- **Report 10's exact approximation determinant.**  For positive nodes,

`det(sⱼ ^ ((d-1)p + i(qt-p)))`

is the common column scale times the Vandermonde product of the nodes
`sⱼ ^ (qt-p)`. -/
theorem det_candidateApproximationAlternant
    (d p q : ℕ) (t : ℝ) (s : Fin d → ℝ) (hs : ∀ j, 0 < s j) :
    (candidateApproximationAlternant d p q t s).det =
      (∏ j, s j ^ candidateClusterBaseExponent d p) *
        ∏ i : Fin d, ∏ j ∈ Finset.Ioi i,
          (s j ^ candidateApproximationError p q t -
            s i ^ candidateApproximationError p q t) := by
  exact det_rpowAffineExponentMatrix d s (candidateClusterBaseExponent d p)
    (candidateApproximationError p q t) hs

/-- The approximation alternant is nonzero whenever the smooth bases are distinct and the
approximation error is nonzero.  This is the exact nonvanishing half of the report's
integer-versus-small determinant argument. -/
theorem det_candidateApproximationAlternant_ne_zero
    (d p q : ℕ) (t : ℝ) (s : Fin d → ℝ) (hs : ∀ j, 0 < s j)
    (hinj : Function.Injective s) (herror : candidateApproximationError p q t ≠ 0) :
    (candidateApproximationAlternant d p q t s).det ≠ 0 := by
  have hnode : Function.Injective (fun j ↦ s j ^ candidateApproximationError p q t) := by
    intro i j hij
    apply hinj
    exact (Real.rpow_left_inj (hs i).le (hs j).le herror).mp hij
  have hscale : (∏ j, s j ^ candidateClusterBaseExponent d p) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun j _ ↦
      (Real.rpow_pos_of_pos (hs j) (candidateClusterBaseExponent d p)).ne'
  have hvandermonde :
      (∏ i : Fin d, ∏ j ∈ Finset.Ioi i,
        (s j ^ candidateApproximationError p q t -
          s i ^ candidateApproximationError p q t)) ≠ 0 := by
    rw [← Matrix.det_vandermonde]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hnode
  rw [det_candidateApproximationAlternant d p q t s hs]
  exact mul_ne_zero hscale hvandermonde

end

end LeanProofs.TwoBaseIntegerExponent
