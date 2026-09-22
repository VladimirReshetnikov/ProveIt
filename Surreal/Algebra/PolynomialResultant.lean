import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Resultant products and common roots

This file proves `polynomial:eq:resultantproduct` and the Sylvester
determinant, interchange sign, and common-root assertions in its surrounding
paragraphs in `docs/surcomplex/polynomial-algebra/article.tex`.

We use Mathlib's `Polynomial.resultant`. Its two size parameters default to
the actual natural degrees. Fixed-size determinants commute with arbitrary
coefficient maps; after a map drops a degree, that is not automatically a
statement about the new actual-degree resultant. Both conventions are kept
explicit below. In particular the zero-size determinant gives
`resultant 0 0 = 1`, so the common-root criterion assumes the first polynomial
is nonzero. Nonzero constants and empty root multisets are allowed.

Splitting is assumed where required. No algebraic closedness of a Hahn or
surcomplex field, multiplication determinant on a quotient, discriminant,
or valuation formula is asserted here.
-/

namespace Surreal.FinitePolynomial

open Polynomial

section CommRing

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The Sylvester determinant assertion following
`polynomial:eq:resultantproduct`, at the actual polynomial degrees. -/
theorem resultant_eq_sylvester_det (P Q : R[X]) :
    P.resultant Q = (P.sylvester Q P.natDegree Q.natDegree).det := rfl

/-- The Sylvester matrix represents the finite Bézout map
`(p, q) ↦ P * q + Q * p`, in the ordered coefficient bases. This is the
finite linear map in the common-root paragraph following
`polynomial:eq:discval`. -/
theorem sylvester_eq_matrix_bezout (P Q : R[X]) :
    P.sylvester Q P.natDegree Q.natDegree =
      (Polynomial.sylvesterMap P Q le_rfl le_rfl).toMatrix
        (((degreeLT.basis R P.natDegree).prod (degreeLT.basis R Q.natDegree)).reindex
          finSumFinEquiv)
        (degreeLT.basis R (P.natDegree + Q.natDegree)) :=
  (Polynomial.toMatrix_sylvesterMap' P Q le_rfl le_rfl).symm

/-- Coefficient specialization of the fixed-size Sylvester determinant.
The sizes remain unchanged even when polynomial degrees drop. This is the
coefficient-polynomial interpretation stated after
`polynomial:eq:resultantproduct`. -/
theorem resultant_map_fixed_degrees (P Q : R[X]) (m n : ℕ) (f : R →+* S) :
    (P.map f).resultant (Q.map f) m n = f (P.resultant Q m n) :=
  Polynomial.resultant_map_map P Q m n f

/-- An injective coefficient map preserves the degrees, so it also
commutes with the actual-degree resultant. -/
theorem resultant_map_of_injective (P Q : R[X]) (f : R →+* S)
    (hf : Function.Injective f) :
    (P.map f).resultant (Q.map f) = f (P.resultant Q) := by
  simpa only [natDegree_map_eq_of_injective hf] using
    (resultant_map_fixed_degrees P Q P.natDegree Q.natDegree f)

/-- The sign under interchanging the two polynomials, as stated after
`polynomial:eq:resultantproduct`. -/
theorem resultant_swap (P Q : R[X]) :
    P.resultant Q = (-1) ^ (P.natDegree * Q.natDegree) * Q.resultant P :=
  Polynomial.resultant_comm P Q P.natDegree Q.natDegree

end CommRing

section Field

variable {K : Type*} [Field K]

/-- The first product in `polynomial:eq:resultantproduct`. The first
polynomial splits; the second polynomial need not split. -/
theorem resultant_eq_leadingCoeff_mul_prod_eval (P Q : K[X]) (hP : P.Splits) :
    P.resultant Q = P.leadingCoeff ^ Q.natDegree * (P.roots.map Q.eval).prod :=
  Polynomial.resultant_eq_prod_eval P Q Q.natDegree le_rfl hP

/-- The double product of root differences in
`polynomial:eq:resultantproduct`, with both leading-coefficient powers.
The Cartesian product is a multiset, so repeated roots are counted. -/
theorem resultant_eq_leadingCoeffs_mul_prod_sub (P Q : K[X])
    (hP : P.Splits) (hQ : Q.Splits) :
    P.resultant Q = P.leadingCoeff ^ Q.natDegree * Q.leadingCoeff ^ P.natDegree *
      ((P.roots ×ˢ Q.roots).map fun ab => ab.1 - ab.2).prod := by
  rw [resultant_eq_leadingCoeff_mul_prod_eval P Q hP,
    Multiset.prod_map_product_eq_prod_prod]
  simp_rw [hQ.eval_eq_prod_roots]
  rw [Multiset.prod_map_mul]
  simp only [Multiset.map_const', Multiset.prod_replicate, ← hP.natDegree_eq_card_roots,
    mul_assoc]

/-- The monic specialization of the double-root product. -/
theorem resultant_eq_prod_sub_of_monic (P Q : K[X]) (hPm : P.Monic) (hQm : Q.Monic)
    (hP : P.Splits) (hQ : Q.Splits) :
    P.resultant Q = ((P.roots ×ˢ Q.roots).map fun ab => ab.1 - ab.2).prod :=
  Polynomial.resultant_eq_prod_roots_sub P Q hPm hQm hP hQ

/-- The common-root criterion following `polynomial:eq:discval`.
Splitting only the nonzero first polynomial suffices. This permits a zero
second polynomial, and still handles nonzero constants correctly. -/
theorem resultant_eq_zero_iff_common_root (P Q : K[X]) (hP0 : P ≠ 0) (hP : P.Splits) :
    P.resultant Q = 0 ↔ ∃ a : K, P.IsRoot a ∧ Q.IsRoot a := by
  rw [resultant_eq_leadingCoeff_mul_prod_eval P Q hP]
  have hlead : P.leadingCoeff ^ Q.natDegree ≠ 0 :=
    pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hP0)
  rw [mul_eq_zero, or_iff_right hlead, Multiset.prod_eq_zero_iff, Multiset.mem_map]
  constructor
  · rintro ⟨a, ha, hQa⟩
    exact ⟨a, (mem_roots hP0).mp ha, hQa⟩
  · rintro ⟨a, hPa, hQa⟩
    exact ⟨a, (mem_roots hP0).mpr hPa, hQa⟩

/-- The Sylvester matrix is singular, in the determinant-zero sense,
exactly when the split polynomials have a common root. -/
theorem sylvester_det_eq_zero_iff_common_root (P Q : K[X])
    (hP0 : P ≠ 0) (hP : P.Splits) :
    (P.sylvester Q P.natDegree Q.natDegree).det = 0 ↔
      ∃ a : K, P.IsRoot a ∧ Q.IsRoot a :=
  resultant_eq_zero_iff_common_root P Q hP0 hP

/-- The finite Bézout map has a nonzero vector in its coefficient kernel
exactly when the polynomials share a root. The preceding matrix identity
identifies these coordinates with the bounded-degree polynomial map. -/
theorem sylvester_has_kernel_iff_common_root (P Q : K[X])
    (hP0 : P ≠ 0) (hP : P.Splits) :
    (∃ v : Fin (P.natDegree + Q.natDegree) → K,
      v ≠ 0 ∧ (P.sylvester Q P.natDegree Q.natDegree).mulVec v = 0) ↔
      ∃ a : K, P.IsRoot a ∧ Q.IsRoot a :=
  Matrix.exists_mulVec_eq_zero_iff.trans
    (sylvester_det_eq_zero_iff_common_root P Q hP0 hP)

/-- Over a field, the nonzero-polynomial resultant criterion is also the
coprimality criterion, without any splitting assumption. -/
theorem resultant_ne_zero_iff_isCoprime (P Q : K[X]) (hP0 : P ≠ 0) :
    P.resultant Q ≠ 0 ↔ IsCoprime P Q := by
  constructor
  · intro h
    by_contra hcop
    exact h (Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl hP0, hcop⟩)
  · intro hcop hzero
    exact (Polynomial.resultant_eq_zero_iff.mp hzero).2 hcop

end Field

end Surreal.FinitePolynomial
