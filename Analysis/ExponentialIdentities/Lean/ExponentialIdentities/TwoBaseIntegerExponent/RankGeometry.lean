import Mathlib.Tactic

/-!
# Rank geometry from rank-geometry analysis

This module kernel-checks the finite algebra behind the genuinely new part of report 22.
It deliberately does not formalize Baker's theorem or the remaining transcendence statement.

The four-variable form `z₁z₂ - z₃z₄` has hyperbolic Gram matrix

`[[0,1,0,0], [1,0,0,0], [0,0,0,-1], [0,0,-1,0]]`.

Its normal square on a relation vector is twice the tangency invariant
`c₁c₂ - c₃c₄`.  We also verify the determinant certificate for the ternary conic in the
multiplicative-rank-three branch.

The strongest packaged result is the rational symmetrization construction.  If

`gamma*l₁₁ + alpha*l₁₂ + delta*l₂₁ + beta*l₂₂ = 0`,

then right multiplication by

`Q = [[-delta, gamma], [-beta, alpha]]`

makes `L` symmetric.  Moreover `det Q = gamma*beta - delta*alpha`, so the non-tangency
condition is exactly what makes this rational column operation invertible.
-/

namespace LeanProofs.TwoBaseIntegerExponent
namespace RankGeometry

open scoped Matrix

/-! ## The hyperbolic tangency invariant -/

/-- Twice the symmetric matrix of `z₁z₂ - z₃z₄`. -/
def hyperbolicGram (R : Type*) [CommRing R] : Matrix (Fin 4) (Fin 4) R :=
  !![0, 1, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, -1;
     0, 0, -1, 0]

/-- The tangency invariant attached to a relation vector. -/
def tangentInvariant {R : Type*} [CommRing R] (c : Fin 4 → R) : R :=
  c 0 * c 1 - c 2 * c 3

/-- The hyperbolic normal square is twice the tangency invariant. -/
theorem dotProduct_hyperbolicGram_mulVec
    {R : Type*} [CommRing R] (c : Fin 4 → R) :
    dotProduct c (hyperbolicGram R *ᵥ c) = 2 * tangentInvariant c := by
  simp [hyperbolicGram, tangentInvariant, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-! ## The rank-three conic determinant -/

/-- Twice the symmetric matrix of
`C X² + (D-A)XY - B Y² + v XZ - u YZ`. -/
def rankThreeConicMatrix {R : Type*} [CommRing R]
    (A B C D u v : R) : Matrix (Fin 3) (Fin 3) R :=
  !![2 * C, D - A, v;
     D - A, -2 * B, -u;
     v, -u, 0]

/-- Exact determinant certificate for the rank-three ternary conic. -/
theorem rankThreeConicMatrix_det
    {R : Type*} [CommRing R] (A B C D u v : R) :
    (rankThreeConicMatrix A B C D u v).det =
      2 * ((A - D) * u * v + B * v ^ 2 - C * u ^ 2) := by
  rw [Matrix.det_fin_three]
  simp [rankThreeConicMatrix]
  ring

/-! ## Rational symmetrization -/

/-- The relation coefficient matrix
`[[gamma, alpha], [delta, beta]]`. -/
def relationMatrix {R : Type*} [CommRing R]
    (gamma alpha delta beta : R) : Matrix (Fin 2) (Fin 2) R :=
  !![gamma, alpha; delta, beta]

/-- The integral right-column operation that symmetrizes the logarithm matrix. -/
def symmetrizingMatrix {R : Type*} [CommRing R]
    (gamma alpha delta beta : R) : Matrix (Fin 2) (Fin 2) R :=
  !![-delta, gamma; -beta, alpha]

/-- The determinant of the symmetrizing column operation is exactly the non-tangency
invariant. -/
theorem symmetrizingMatrix_det
    {R : Type*} [CommRing R] (gamma alpha delta beta : R) :
    (symmetrizingMatrix gamma alpha delta beta).det = gamma * beta - delta * alpha := by
  rw [Matrix.det_fin_two]
  simp [symmetrizingMatrix]
  ring

/-- The same invariant is the determinant of the unique-relation coefficient matrix. -/
theorem relationMatrix_det
    {R : Type*} [CommRing R] (gamma alpha delta beta : R) :
    (relationMatrix gamma alpha delta beta).det = gamma * beta - delta * alpha := by
  rw [Matrix.det_fin_two]
  simp [relationMatrix]
  ring

/-- A relation with coefficient matrix `[[gamma,alpha],[delta,beta]]` is precisely the
off-diagonal equality needed after the explicit right-column operation. -/
theorem right_mul_symmetrizingMatrix_offDiagonal
    {R : Type*} [CommRing R]
    (L : Matrix (Fin 2) (Fin 2) R) (gamma alpha delta beta : R)
    (hrel : gamma * L 0 0 + alpha * L 0 1 + delta * L 1 0 + beta * L 1 1 = 0) :
    (L * symmetrizingMatrix gamma alpha delta beta) 0 1 =
      (L * symmetrizingMatrix gamma alpha delta beta) 1 0 := by
  simp [Matrix.mul_apply, symmetrizingMatrix, Fin.sum_univ_two]
  linear_combination hrel

/-- **Rational symmetrization.**  The explicit column operation attached to a rational
relation makes the matrix symmetric. -/
theorem right_mul_symmetrizingMatrix_isSymm
    {R : Type*} [CommRing R]
    (L : Matrix (Fin 2) (Fin 2) R) (gamma alpha delta beta : R)
    (hrel : gamma * L 0 0 + alpha * L 0 1 + delta * L 1 0 + beta * L 1 1 = 0) :
    (L * symmetrizingMatrix gamma alpha delta beta).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact (right_mul_symmetrizingMatrix_offDiagonal L gamma alpha delta beta hrel).symm
  · exact right_mul_symmetrizingMatrix_offDiagonal L gamma alpha delta beta hrel
  · rfl

/-- Under non-tangency, the symmetrizing column operation is invertible over a field. -/
theorem symmetrizingMatrix_isUnit_det
    {K : Type*} [Field K] (gamma alpha delta beta : K)
    (hdet : gamma * beta - delta * alpha ≠ 0) :
    IsUnit (symmetrizingMatrix gamma alpha delta beta).det := by
  rw [symmetrizingMatrix_det]
  exact isUnit_iff_ne_zero.mpr hdet

/-- Under non-tangency, the symmetrizing column operation itself is a unit. -/
theorem symmetrizingMatrix_isUnit
    {K : Type*} [Field K] (gamma alpha delta beta : K)
    (hdet : gamma * beta - delta * alpha ≠ 0) :
    IsUnit (symmetrizingMatrix gamma alpha delta beta) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact symmetrizingMatrix_isUnit_det gamma alpha delta beta hdet

/-- Packaged form of rational symmetrization: a non-tangent rational relation supplies an
invertible right multiplier that makes the matrix symmetric. -/
theorem exists_isUnit_rightMultiplier_isSymm
    {K : Type*} [Field K]
    (L : Matrix (Fin 2) (Fin 2) K) (gamma alpha delta beta : K)
    (hrel : gamma * L 0 0 + alpha * L 0 1 + delta * L 1 0 + beta * L 1 1 = 0)
    (hdet : gamma * beta - delta * alpha ≠ 0) :
    ∃ Q : Matrix (Fin 2) (Fin 2) K, IsUnit Q ∧ (L * Q).IsSymm := by
  refine ⟨symmetrizingMatrix gamma alpha delta beta,
    symmetrizingMatrix_isUnit gamma alpha delta beta hdet, ?_⟩
  exact right_mul_symmetrizingMatrix_isSymm L gamma alpha delta beta hrel

/-! ## The symmetric rank-one normal form -/

/-- Two nonzero proportional directions in a field have a common scalar.  This is the
two-coordinate algebra used after symmetrizing an outer product. -/
theorem exists_scalar_of_cross_eq
    {K : Type*} [Field K] {r₁ r₂ d₁ d₂ : K}
    (hr : r₁ ≠ 0 ∨ r₂ ≠ 0) (hcross : r₁ * d₂ = r₂ * d₁) :
    ∃ k : K, d₁ = k * r₁ ∧ d₂ = k * r₂ := by
  rcases hr with hr₁ | hr₂
  · refine ⟨d₁ / r₁, ?_, ?_⟩
    · exact (div_mul_cancel₀ d₁ hr₁).symm
    · rw [div_mul_eq_mul_div, eq_div_iff hr₁]
      simpa [mul_comm] using hcross
  · refine ⟨d₂ / r₂, ?_, ?_⟩
    · rw [div_mul_eq_mul_div, eq_div_iff hr₂]
      simpa [mul_comm] using hcross.symm
    · exact (div_mul_cancel₀ d₂ hr₂).symm

/-- A symmetric nonzero outer product is a scalar multiple of `r rᵀ`. -/
theorem symmetric_outerProduct_normalForm
    {K : Type*} [Field K] {r d : Fin 2 → K}
    (hr : r ≠ 0)
    (hsymm : (Matrix.vecMulVec r d).IsSymm) :
    ∃ k : K, Matrix.vecMulVec r d =
      (fun i j => k * (r i * r j)) := by
  have hr' : r 0 ≠ 0 ∨ r 1 ≠ 0 := by
    by_cases hzero : r 0 = 0
    · right
      intro hone
      apply hr
      funext i
      fin_cases i
      · exact hzero
      · exact hone
    · exact Or.inl hzero
  have hcross : r 0 * d 1 = r 1 * d 0 := by
    simpa only [Matrix.vecMulVec_apply] using Matrix.IsSymm.apply hsymm 1 0
  obtain ⟨k, hd₁, hd₂⟩ := exists_scalar_of_cross_eq hr' hcross
  have hd : d = fun j => k * r j := by
    funext j
    fin_cases j
    · exact hd₁
    · exact hd₂
  refine ⟨k, ?_⟩
  rw [hd]
  ext i j
  simp only [Matrix.vecMulVec_apply]
  ring

end RankGeometry
end LeanProofs.TwoBaseIntegerExponent
