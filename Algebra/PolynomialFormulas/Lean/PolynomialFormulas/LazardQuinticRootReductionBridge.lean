import PolynomialFormulas.LazardQuinticRootInvariants
import PolynomialFormulas.LazardQuinticRootRadicals
import PolynomialFormulas.LazardQuinticRootReductionsSparse
import PolynomialFormulas.LazardQuinticRootReductionGSparse

/-!
# Root-level bridge for Lazard's invariant reductions

The large `D` and `E` certificates are checked after eliminating the fifth
root.  This module proves that the elimination is the identity on a depressed
ordered root tuple, transports the sparse coefficient and invariant tuples to
their root-defined counterparts, and exposes the resulting root-level
identities.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuintic

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients
open LeanProofs.PolynomialFormulas.FrobeniusDummitResolvent

set_option autoImplicit false

private theorem depressedQuintic_eq_of_fields_eq
    {K : Type*} {a b : DepressedQuintic K}
    (hp : a.p = b.p) (hq : a.q = b.q) (hr : a.r = b.r) (hs : a.s = b.s) :
    a = b := by
  cases a
  cases b
  simp_all

private theorem invariants_eq_of_fields_eq
    {K : Type*} {a b : Invariants K}
    (h4 : a.i4 = b.i4) (h5 : a.i5 = b.i5) (h6 : a.i6 = b.i6)
    (h7 : a.i7 = b.i7) (h8 : a.i8 = b.i8) : a = b := by
  cases a
  cases b
  simp_all

/-- Eliminating `x₄` by the depressed relation does not change an already
depressed ordered root tuple. -/
theorem eliminatedTuple_eq_self_of_elementaryTuple_zero
    {K : Type*} [CommRing K] (x : Fin 5 → K)
    (hsum : elementaryTuple x 0 = 0) :
    RootInvariantSparse.eliminatedTuple x = x := by
  have hx4 : x 4 = -(x 0 + x 1 + x 2 + x 3) := by
    simp [elementaryTuple] at hsum
    linear_combination hsum
  funext j
  fin_cases j <;> simp [hx4]

/-- The sparse coefficient tuple is the usual depressed coefficient tuple
when the supplied roots have sum zero. -/
theorem sparseDepressedOfRoots_eq_depressedOfRoots
    {K : Type*} [CommRing K] (x : Fin 5 → K)
    (hsum : elementaryTuple x 0 = 0) :
    sparseDepressedOfRoots x = depressedOfRoots x := by
  have helim := eliminatedTuple_eq_self_of_elementaryTuple_zero x hsum
  apply depressedQuintic_eq_of_fields_eq
  · change SparsePolynomial.eval RootInvariantSparse.p x =
      (depressedOfRoots x).p
    rw [RootInvariantSparse.eval_p, helim]
    rfl
  · change SparsePolynomial.eval RootInvariantSparse.q x =
      (depressedOfRoots x).q
    rw [RootInvariantSparse.eval_q, helim]
    rfl
  · change SparsePolynomial.eval RootInvariantSparse.r x =
      (depressedOfRoots x).r
    rw [RootInvariantSparse.eval_r, helim]
    rfl
  · change SparsePolynomial.eval RootInvariantSparse.s x =
      (depressedOfRoots x).s
    rw [RootInvariantSparse.eval_s, helim]
    rfl

/-- The five checked sparse orbit sums agree with the five invariants defined
directly from the ordered roots. -/
theorem sparseRootInvariants_eq_rootInvariants
    {K : Type*} [CommRing K] (x : Fin 5 → K)
    (hsum : elementaryTuple x 0 = 0) :
    sparseRootInvariants x = rootInvariants x := by
  have helim := eliminatedTuple_eq_self_of_elementaryTuple_zero x hsum
  apply invariants_eq_of_fields_eq
  · change SparsePolynomial.eval RootInvariantSparse.i4 x =
      (rootInvariants x).i4
    rw [RootInvariantSparse.eval_i4, helim,
      rootInvariants_i4_eq_thetaFormula]
    simp [RootInvariantSparse.orbitValue, thetaFormula]
  · change SparsePolynomial.eval RootInvariantSparse.i5 x =
      (rootInvariants x).i5
    rw [RootInvariantSparse.eval_i5, helim,
      rootInvariants_i5_eq_lazardOrbitFormula]
    rfl
  · change SparsePolynomial.eval RootInvariantSparse.i6 x =
      (rootInvariants x).i6
    rw [RootInvariantSparse.eval_i6, helim,
      rootInvariants_i6_eq_lazardOrbitFormula]
    rfl
  · change SparsePolynomial.eval RootInvariantSparse.i7 x =
      (rootInvariants x).i7
    rw [RootInvariantSparse.eval_i7, helim,
      rootInvariants_i7_eq_lazardOrbitFormula]
    rfl
  · change SparsePolynomial.eval RootInvariantSparse.i8 x =
      (rootInvariants x).i8
    rw [RootInvariantSparse.eval_i8, helim,
      rootInvariants_i8_eq_lazardOrbitFormula]
    rfl

/-- Lazard's displayed `D`, evaluated on the root-defined coefficients and
invariants, is the square of the cyclic epsilon product. -/
theorem root_invariantD_eq_rootEpsilonProduct_sq
    {K : Type*} [Field K] [CharZero K] (x : Fin 5 → K)
    (hsum : elementaryTuple x 0 = 0) :
    invariantD (depressedOfRoots x) (rootInvariants x) =
      rootEpsilonProduct x ^ 2 := by
  rw [← sparseDepressedOfRoots_eq_depressedOfRoots x hsum,
    ← sparseRootInvariants_eq_rootInvariants x hsum,
    sparse_invariantD_eq_rootEpsilonProduct_sq,
    eliminatedTuple_eq_self_of_elementaryTuple_zero x hsum]

/-- Lazard's displayed `E`, evaluated on the root-defined coefficients and
invariants, is the negative sum of the two cyclic product squares. -/
theorem root_invariantE_eq_neg_rootTPrime_sq_add_rootUPrime_sq
    {K : Type*} [Field K] [CharZero K] (x : Fin 5 → K)
    (hsum : elementaryTuple x 0 = 0) :
    invariantE (depressedOfRoots x) (rootInvariants x) =
      -(rootTPrime x ^ 2 + rootUPrime x ^ 2) := by
  rw [← sparseDepressedOfRoots_eq_depressedOfRoots x hsum,
    ← sparseRootInvariants_eq_rootInvariants x hsum,
    sparse_invariantE_eq_neg_rootTPrime_sq_add_rootUPrime_sq,
    eliminatedTuple_eq_self_of_elementaryTuple_zero x hsum]

/-- Lazard's displayed `F`, evaluated on the root-defined coefficients and
invariants, has the cyclic root-product expression used in the quadratic
stage. -/
theorem root_invariantF_eq_root_expression
    {K : Type*} [Field K] [CharZero K] (x : Fin 5 → K)
    (hsum : elementaryTuple x 0 = 0) :
    invariantF (depressedOfRoots x) (rootInvariants x) =
      -rootEpsilonProduct x *
        (rootTPrime x ^ 2 + 4 * rootTPrime x * rootUPrime x -
          rootUPrime x ^ 2) := by
  rw [← sparseDepressedOfRoots_eq_depressedOfRoots x hsum,
    ← sparseRootInvariants_eq_rootInvariants x hsum,
    sparse_invariantF_eq_root_expression,
    eliminatedTuple_eq_self_of_elementaryTuple_zero x hsum]

/-- Lazard's displayed `G`, evaluated on the root-defined coefficients and
invariants, has the cyclic root-product expression used in the quadratic
stage. -/
theorem root_invariantG_eq_root_expression
    {K : Type*} [Field K] [CharZero K] (x : Fin 5 → K)
    (hsum : elementaryTuple x 0 = 0) :
    invariantG (depressedOfRoots x) (rootInvariants x) =
      rootEpsilonProduct x *
        (rootTPrime x ^ 2 - rootTPrime x * rootUPrime x -
          rootUPrime x ^ 2) := by
  rw [← sparseDepressedOfRoots_eq_depressedOfRoots x hsum,
    ← sparseRootInvariants_eq_rootInvariants x hsum,
    sparse_invariantG_eq_root_expression,
    eliminatedTuple_eq_self_of_elementaryTuple_zero x hsum]

/-- Recover the two individual square equations from their sum and their
epsilon-weighted difference.  Only this conversion to division by `epsilon`
requires `epsilon ≠ 0`. -/
theorem quadratic_squares_of_sum_and_epsilon_difference
    {K : Type*} [Field K] [CharZero K] {epsilon t u e f : K}
    (hepsilon : epsilon ≠ 0)
    (hsum : t ^ 2 + u ^ 2 = 5 * e)
    (hdifference : epsilon * (t ^ 2 - u ^ 2) = 5 * f) :
    t ^ 2 = (5 / 2) * (e + f / epsilon) ∧
      u ^ 2 = (5 / 2) * (e - f / epsilon) := by
  constructor
  · field_simp [hepsilon]
    linear_combination epsilon * hsum + hdifference
  · field_simp [hepsilon]
    linear_combination epsilon * hsum - hdifference

/-- The root-defined epsilon is a square root of `5D`. -/
theorem rootEpsilon_sq_eq_five_invariantD
    {K : Type*} [Field K] [CharZero K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hsum : elementaryTuple x 0 = 0) :
    rootEpsilon omega x ^ 2 =
      5 * invariantD (depressedOfRoots x) (rootInvariants x) := by
  rw [root_invariantD_eq_rootEpsilonProduct_sq x hsum]
  unfold rootEpsilon
  rw [mul_pow, fifthRootDiscriminantFactor_sq]

/-- The root-defined `T` and formula-sign `U` satisfy the sum relation
`T² + U² = 5E`. -/
theorem rootT_sq_add_rootFormulaU_sq_eq_five_invariantE
    {K : Type*} [Field K] [CharZero K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hsum : elementaryTuple x 0 = 0) :
    rootT omega x ^ 2 + rootFormulaU omega x ^ 2 =
      5 * invariantE (depressedOfRoots x) (rootInvariants x) := by
  rw [rootT_sq_add_rootFormulaU_sq,
    root_invariantE_eq_neg_rootTPrime_sq_add_rootUPrime_sq x hsum]
  ring

/-- The root-defined epsilon, `T`, and formula-sign `U` satisfy the
epsilon-weighted difference relation `epsilon (T² - U²) = 5F`. -/
theorem rootEpsilon_mul_rootT_sq_sub_rootFormulaU_sq_eq_five_invariantF
    {K : Type*} [Field K] [CharZero K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hsum : elementaryTuple x 0 = 0) :
    rootEpsilon omega x *
        (rootT omega x ^ 2 - rootFormulaU omega x ^ 2) =
      5 * invariantF (depressedOfRoots x) (rootInvariants x) := by
  rw [rootEpsilon_mul_rootT_sq_sub_rootFormulaU_sq,
    root_invariantF_eq_root_expression x hsum]
  ring

/-- The root-defined `T` is a square root of Lazard's first quadratic
radicand. -/
theorem rootT_sq_eq_quadratic_radicand
    {K : Type*} [Field K] [CharZero K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hsum : elementaryTuple x 0 = 0)
    (hepsilon : rootEpsilon omega x ≠ 0) :
    rootT omega x ^ 2 =
      (5 / 2) * (invariantE (depressedOfRoots x) (rootInvariants x) +
        invariantF (depressedOfRoots x) (rootInvariants x) /
          rootEpsilon omega x) :=
  (quadratic_squares_of_sum_and_epsilon_difference hepsilon
    (rootT_sq_add_rootFormulaU_sq_eq_five_invariantE omega x hsum)
    (rootEpsilon_mul_rootT_sq_sub_rootFormulaU_sq_eq_five_invariantF
      omega x hsum)).1

/-- The root-defined formula-sign `U` is a square root of Lazard's second
quadratic radicand. -/
theorem rootFormulaU_sq_eq_quadratic_radicand
    {K : Type*} [Field K] [CharZero K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hsum : elementaryTuple x 0 = 0)
    (hepsilon : rootEpsilon omega x ≠ 0) :
    rootFormulaU omega x ^ 2 =
      (5 / 2) * (invariantE (depressedOfRoots x) (rootInvariants x) -
        invariantF (depressedOfRoots x) (rootInvariants x) /
          rootEpsilon omega x) :=
  (quadratic_squares_of_sum_and_epsilon_difference hepsilon
    (rootT_sq_add_rootFormulaU_sq_eq_five_invariantE omega x hsum)
    (rootEpsilon_mul_rootT_sq_sub_rootFormulaU_sq_eq_five_invariantF
      omega x hsum)).2

/-- Once the remaining `G` product identity is supplied, the three root
expressions form a complete `QuadraticRelations` certificate.  The explicit
nonzero epsilon hypothesis is used only by the two division formulas. -/
theorem rootQuadraticRelations_of_product
    {K : Type*} [Field K] [CharZero K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hsum : elementaryTuple x 0 = 0)
    (hepsilon : rootEpsilon omega x ≠ 0)
    (hproduct :
      rootT omega x * rootFormulaU omega x * rootEpsilon omega x =
        5 * invariantG (depressedOfRoots x) (rootInvariants x)) :
    QuadraticRelations (depressedOfRoots x) (rootInvariants x)
      (rootQuadraticTriple omega x) := by
  constructor
  · simpa [rootQuadraticTriple] using
      rootEpsilon_sq_eq_five_invariantD omega x hsum
  · simpa [rootQuadraticTriple] using
      rootT_sq_eq_quadratic_radicand omega x hsum hepsilon
  · simpa [rootQuadraticTriple] using
      rootFormulaU_sq_eq_quadratic_radicand omega x hsum hepsilon
  · simpa [rootQuadraticTriple] using hproduct

/-- The root-defined quadratic radicals satisfy Lazard's `G` product
relation.  Unlike the two quotient presentations of their squares, this
identity needs no nonzero denominator. -/
theorem rootT_mul_rootFormulaU_mul_rootEpsilon_eq_five_invariantG
    {K : Type*} [Field K] [CharZero K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hsum : elementaryTuple x 0 = 0) :
    rootT omega x * rootFormulaU omega x * rootEpsilon omega x =
      5 * invariantG (depressedOfRoots x) (rootInvariants x) := by
  calc
    rootT omega x * rootFormulaU omega x * rootEpsilon omega x =
        rootEpsilon omega x * rootT omega x * rootFormulaU omega x := by
      ring
    _ = 5 * rootEpsilonProduct x *
          (rootTPrime x ^ 2 - rootTPrime x * rootUPrime x -
            rootUPrime x ^ 2) :=
      rootEpsilon_mul_rootT_mul_rootFormulaU omega x
    _ = 5 * invariantG (depressedOfRoots x) (rootInvariants x) := by
      rw [root_invariantG_eq_root_expression x hsum]
      ring

/-- The roots themselves provide a complete certificate for Lazard's
quadratic stage whenever the displayed divisions by epsilon are defined. -/
theorem rootQuadraticRelations
    {K : Type*} [Field K] [CharZero K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hsum : elementaryTuple x 0 = 0)
    (hepsilon : rootEpsilon omega x ≠ 0) :
    QuadraticRelations (depressedOfRoots x) (rootInvariants x)
      (rootQuadraticTriple omega x) :=
  rootQuadraticRelations_of_product omega x hsum hepsilon
    (rootT_mul_rootFormulaU_mul_rootEpsilon_eq_five_invariantG omega x hsum)

end LeanProofs.PolynomialFormulas.LazardQuintic
