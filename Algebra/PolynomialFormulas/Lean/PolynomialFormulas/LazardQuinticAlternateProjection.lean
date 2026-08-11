import PolynomialFormulas.LazardQuintic

/-!
# Lazard's alternate projection

This file isolates the linear algebra in Section 5 of Daniel Lazard,
*Solving Quintics by Radicals*.  If

`source = ![S, φ(S), φ²(S), φ³(S)]`,

then `standardProjectionMatrix` produces Lazard's `I₁, I₂, I₃, I₄`, while
`alternateProjectionMatrix` replaces the last row by `I₄'`.  We compute both
determinants and give the corresponding formulas that recover `S`.

The explicit quintic formulas in `LazardQuintic` use the Section 7 scaling
`ε² = 5D`, `T² = (5/2)(E + F/ε)`, and `TUε = 5G`.  Consequently the unscaled
relations from Section 5 acquire factors of five here.  The final lemmas make
that normalization explicit.
-/

open Matrix

namespace LeanProofs.PolynomialFormulas.LazardQuintic

set_option autoImplicit false

section ProjectionAlgebra

variable {K : Type*} [Field K] [CharZero K]

/-- The coefficient matrix of Lazard's four standard projections
`I₁, I₂, I₃, I₄`, acting on `![S, φ(S), φ²(S), φ³(S)]`. -/
def standardProjectionMatrix (epsilon t u : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 1, 1, 1;
     epsilon, -epsilon, epsilon, -epsilon;
     t, -u, -t, u;
     u, t, -u, -t]

/-- The coefficient matrix of Lazard's projections `I₁, I₂, I₃, I₄'`.
Its last row is the alternate projection used when `T² + U² = 0`. -/
def alternateProjectionMatrix (epsilon t u : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 1, 1, 1;
     epsilon, -epsilon, epsilon, -epsilon;
     t, -u, -t, u;
     epsilon * (t + 2 * u), epsilon * (u - 2 * t),
       -epsilon * (t + 2 * u), -epsilon * (u - 2 * t)]

/-- The convention-safe alternate matrix for the formula-sign coordinate
`U = rootFormulaU`.  Its fourth row is the coherent-family row with
parameters `(a,b)=(-1,2)`:

`epsilon * ![-T+2U, -2T-U, T-2U, 2T+U]`.

This is the sign/order correction of the printed Section-5 row compatible
with `branchTriple .rotate` and `sourceForBranch .rotate`. -/
def coherentAlternateProjectionMatrix
    (epsilon t u : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 1, 1, 1;
     epsilon, -epsilon, epsilon, -epsilon;
     t, -u, -t, u;
     epsilon * (-t + 2 * u), epsilon * (-2 * t - u),
       epsilon * (t - 2 * u), epsilon * (2 * t + u)]

/-- The extra denominator in Lazard's alternate `I₄'` projection. -/
def alternateDenominator (t u : K) : K :=
  t * u - t ^ 2 + u ^ 2

/-- Denominator of the convention-safe alternate system. -/
def coherentAlternateDenominator (t u : K) : K :=
  t ^ 2 + t * u - u ^ 2

/-- Apply Lazard's standard four projection functionals to an orbit of four
source values. -/
def standardProjections (epsilon t u : K) (source : Fin 4 → K) : Fin 4 → K :=
  (standardProjectionMatrix epsilon t u).mulVec source

/-- Apply Lazard's alternate four projection functionals to an orbit of four
source values. -/
def alternateProjections (epsilon t u : K) (source : Fin 4 → K) : Fin 4 → K :=
  (alternateProjectionMatrix epsilon t u).mulVec source

/-- Apply the convention-safe alternate projection functionals. -/
def coherentAlternateProjections
    (epsilon t u : K) (source : Fin 4 → K) : Fin 4 → K :=
  (coherentAlternateProjectionMatrix epsilon t u).mulVec source

/-- Recover `S`, the zeroth source coordinate, from `I₁, I₂, I₃, I₄`.
The denominator hypotheses are stated by the correctness theorem below. -/
def standardRecover (epsilon t u : K) (projections : Fin 4 → K) : K :=
  projections 0 / 4 + projections 1 / (4 * epsilon) +
    (t * projections 2 + u * projections 3) / (2 * (t ^ 2 + u ^ 2))

/-- Recover `S`, the zeroth source coordinate, from `I₁, I₂, I₃, I₄'`.
This is Cramer's-rule recovery with denominator
`4 ε (TU - T² + U²)`. -/
def alternateRecover (epsilon t u : K) (projections : Fin 4 → K) : K :=
  projections 0 / 4 + projections 1 / (4 * epsilon) +
    (epsilon * (u - 2 * t) * projections 2 + u * projections 3) /
      (4 * epsilon * alternateDenominator t u)

/-- Recover the zeroth source coordinate from the convention-safe alternate
system. -/
def coherentAlternateRecover
    (epsilon t u : K) (projections : Fin 4 → K) : K :=
  projections 0 / 4 + projections 1 / (4 * epsilon) +
    (epsilon * (2 * t + u) * projections 2 - u * projections 3) /
      (4 * epsilon * coherentAlternateDenominator t u)

omit [CharZero K] in
/-- Lazard's standard projection matrix has determinant
`-8 ε (T² + U²)`. -/
theorem standardProjectionMatrix_det (epsilon t u : K) :
    (standardProjectionMatrix epsilon t u).det =
      -8 * epsilon * (t ^ 2 + u ^ 2) := by
  simp [standardProjectionMatrix, Matrix.det_succ_row_zero,
    Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Fin.succAbove]
  ring

omit [CharZero K] in
/-- Lazard's alternate projection matrix has determinant
`-16 ε² (TU - T² + U²)`. -/
theorem alternateProjectionMatrix_det (epsilon t u : K) :
    (alternateProjectionMatrix epsilon t u).det =
      -16 * epsilon ^ 2 * alternateDenominator t u := by
  simp [alternateProjectionMatrix, Matrix.det_succ_row_zero,
    Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Fin.succAbove,
    alternateDenominator]
  ring

omit [CharZero K] in
/-- The corrected denominator is the negative of the printed denominator
after translating from formula-sign `U` back to the Section-5 sign. -/
theorem coherentAlternateDenominator_eq_neg_alternateDenominator
    (t u : K) :
    coherentAlternateDenominator t u =
      -alternateDenominator t (-u) := by
  simp [coherentAlternateDenominator, alternateDenominator]
  ring

omit [CharZero K] in
/-- The convention-safe alternate matrix has determinant
`16 epsilon^2 (T^2 + TU - U^2)`. -/
theorem coherentAlternateProjectionMatrix_det (epsilon t u : K) :
    (coherentAlternateProjectionMatrix epsilon t u).det =
      16 * epsilon ^ 2 * coherentAlternateDenominator t u := by
  simp [coherentAlternateProjectionMatrix, Matrix.det_succ_row_zero,
    Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Fin.succAbove,
    coherentAlternateDenominator]
  ring

/-- The standard projection matrix is nonsingular under exactly the two
denominator hypotheses used by `standardRecover`. -/
theorem standardProjectionMatrix_det_ne_zero (epsilon t u : K)
    (hepsilon : epsilon ≠ 0) (hdenominator : t ^ 2 + u ^ 2 ≠ 0) :
    (standardProjectionMatrix epsilon t u).det ≠ 0 := by
  rw [standardProjectionMatrix_det]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hepsilon) hdenominator

/-- The alternate projection matrix is nonsingular under exactly the two
denominator hypotheses used by `alternateRecover`. -/
theorem alternateProjectionMatrix_det_ne_zero (epsilon t u : K)
    (hepsilon : epsilon ≠ 0)
    (hdenominator : alternateDenominator t u ≠ 0) :
    (alternateProjectionMatrix epsilon t u).det ≠ 0 := by
  rw [alternateProjectionMatrix_det]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hepsilon)) hdenominator

/-- The corrected alternate matrix is nonsingular under its two explicit
denominator hypotheses. -/
theorem coherentAlternateProjectionMatrix_det_ne_zero (epsilon t u : K)
    (hepsilon : epsilon ≠ 0)
    (hdenominator : coherentAlternateDenominator t u ≠ 0) :
    (coherentAlternateProjectionMatrix epsilon t u).det ≠ 0 := by
  rw [coherentAlternateProjectionMatrix_det]
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hepsilon)) hdenominator

/-- Lazard's standard inverse formula really recovers the original `S` from
the four standard projections. -/
theorem standardRecover_standardProjections (epsilon t u : K)
    (source : Fin 4 → K) (hepsilon : epsilon ≠ 0)
    (hdenominator : t ^ 2 + u ^ 2 ≠ 0) :
    standardRecover epsilon t u (standardProjections epsilon t u source) =
      source 0 := by
  simp [standardRecover, standardProjections, standardProjectionMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  field_simp [hepsilon, hdenominator]
  ring

/-- Lazard's alternate inverse formula really recovers the original `S` from
the four projections using `I₄'`. -/
theorem alternateRecover_alternateProjections (epsilon t u : K)
    (source : Fin 4 → K) (hepsilon : epsilon ≠ 0)
    (hdenominator : alternateDenominator t u ≠ 0) :
    alternateRecover epsilon t u (alternateProjections epsilon t u source) =
      source 0 := by
  simp [alternateRecover, alternateProjections, alternateProjectionMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  field_simp [hepsilon, hdenominator]
  rw [alternateDenominator]
  ring

/-- The convention-safe inverse formula recovers the zeroth source
coordinate. -/
theorem coherentAlternateRecover_coherentAlternateProjections
    (epsilon t u : K) (source : Fin 4 → K)
    (hepsilon : epsilon ≠ 0)
    (hdenominator : coherentAlternateDenominator t u ≠ 0) :
    coherentAlternateRecover epsilon t u
        (coherentAlternateProjections epsilon t u source) =
      source 0 := by
  simp [coherentAlternateRecover, coherentAlternateProjections,
    coherentAlternateProjectionMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]
  field_simp [hepsilon, hdenominator]
  rw [coherentAlternateDenominator]
  ring

/-! ## The Section 7 scaling -/

/-- The two square equations in `QuadraticRelations` add to
`T² + U² = 5E`.  No nonzero hypothesis on `ε` is needed for this sum. -/
theorem QuadraticRelations.t_sq_add_u_sq
    {c : DepressedQuintic K} {i : Invariants K} {v : QuadraticTriple K}
    (h : QuadraticRelations c i v) :
    v.t ^ 2 + v.u ^ 2 = 5 * invariantE c i := by
  rw [h.t_square, h.u_square]
  ring

/-- The two square equations in `QuadraticRelations` subtract to
`ε(T² - U²) = 5F`.  Cancellation of the division by `ε` requires the explicit
hypothesis `ε ≠ 0`. -/
theorem QuadraticRelations.epsilon_mul_t_sq_sub_u_sq
    {c : DepressedQuintic K} {i : Invariants K} {v : QuadraticTriple K}
    (h : QuadraticRelations c i v) (hepsilon : v.epsilon ≠ 0) :
    v.epsilon * (v.t ^ 2 - v.u ^ 2) = 5 * invariantF c i := by
  rw [h.t_square, h.u_square]
  field_simp [hepsilon]
  ring

/-- In the Section 7 normalization, Lazard's alternate denominator satisfies
`ε(TU - T² + U²) = 5(G - F)`. -/
theorem QuadraticRelations.epsilon_mul_alternateDenominator
    {c : DepressedQuintic K} {i : Invariants K} {v : QuadraticTriple K}
    (h : QuadraticRelations c i v) (hepsilon : v.epsilon ≠ 0) :
    v.epsilon * alternateDenominator v.t v.u =
      5 * (invariantG c i - invariantF c i) := by
  rw [alternateDenominator]
  calc
    v.epsilon * (v.t * v.u - v.t ^ 2 + v.u ^ 2) =
        v.t * v.u * v.epsilon -
          v.epsilon * (v.t ^ 2 - v.u ^ 2) := by ring
    _ = 5 * invariantG c i - 5 * invariantF c i := by
      rw [h.product, h.epsilon_mul_t_sq_sub_u_sq hepsilon]
    _ = 5 * (invariantG c i - invariantF c i) := by ring

/-- After substituting `T² + U² = 5E`, the standard determinant is
`-40 ε E`. -/
theorem QuadraticRelations.standardProjectionMatrix_det
    {c : DepressedQuintic K} {i : Invariants K} {v : QuadraticTriple K}
    (h : QuadraticRelations c i v) :
    (standardProjectionMatrix v.epsilon v.t v.u).det =
      -40 * v.epsilon * invariantE c i := by
  rw [_root_.LeanProofs.PolynomialFormulas.LazardQuintic.standardProjectionMatrix_det,
    h.t_sq_add_u_sq]
  ring

/-- After substituting the quadratic relations, the alternate determinant is
`-80 ε (G - F)` in the Section 7 normalization. -/
theorem QuadraticRelations.alternateProjectionMatrix_det
    {c : DepressedQuintic K} {i : Invariants K} {v : QuadraticTriple K}
    (h : QuadraticRelations c i v) (hepsilon : v.epsilon ≠ 0) :
    (alternateProjectionMatrix v.epsilon v.t v.u).det =
      -80 * v.epsilon * (invariantG c i - invariantF c i) := by
  rw [_root_.LeanProofs.PolynomialFormulas.LazardQuintic.alternateProjectionMatrix_det]
  calc
    -16 * v.epsilon ^ 2 * alternateDenominator v.t v.u =
        -16 * v.epsilon *
          (v.epsilon * alternateDenominator v.t v.u) := by ring
    _ = -16 * v.epsilon *
          (5 * (invariantG c i - invariantF c i)) := by
      rw [h.epsilon_mul_alternateDenominator hepsilon]
    _ = -80 * v.epsilon * (invariantG c i - invariantF c i) := by ring

/-- If `G - F` is nonzero, the alternate denominator is nonzero.  The
`ε ≠ 0` hypothesis is precisely what is needed to derive its invariant
identity from `QuadraticRelations`. -/
theorem QuadraticRelations.alternateDenominator_ne_zero
    {c : DepressedQuintic K} {i : Invariants K} {v : QuadraticTriple K}
    (h : QuadraticRelations c i v) (hepsilon : v.epsilon ≠ 0)
    (hGF : invariantG c i - invariantF c i ≠ 0) :
    alternateDenominator v.t v.u ≠ 0 := by
  intro hzero
  have hrelation := h.epsilon_mul_alternateDenominator hepsilon
  rw [hzero, mul_zero] at hrelation
  exact hGF (by
    apply (mul_eq_zero.mp hrelation.symm).resolve_left
    norm_num)

/-- Under the invariant nonvanishing hypotheses, Lazard's alternate
projection matrix is nonsingular. -/
theorem QuadraticRelations.alternateProjectionMatrix_det_ne_zero
    {c : DepressedQuintic K} {i : Invariants K} {v : QuadraticTriple K}
    (h : QuadraticRelations c i v) (hepsilon : v.epsilon ≠ 0)
    (hGF : invariantG c i - invariantF c i ≠ 0) :
    (alternateProjectionMatrix v.epsilon v.t v.u).det ≠ 0 := by
  rw [h.alternateProjectionMatrix_det hepsilon]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hepsilon) hGF

end ProjectionAlgebra

end LeanProofs.PolynomialFormulas.LazardQuintic
