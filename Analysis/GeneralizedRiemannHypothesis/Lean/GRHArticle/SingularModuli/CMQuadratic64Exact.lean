import GRHArticle.SingularModuli.CMQuadratic64Forms
import GRHArticle.SingularModuli.Prime17DiagonalChecks
import GRHArticle.SingularModuli.Prime17DiagonalCertificate
import GRHArticle.SingularModuli.HeckeComputedDiagonalCertificate
import GRHArticle.SingularModuli.HeckeCofactorEnclosure
import GRHArticle.SingularModuli.ReducedCuspSeparation
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Exact singular moduli at discriminant −64

Both roots of the quadratic class polynomial have minimum support three.
This establishes the first member of the first dyadic family directly from
the analytic modular invariant.
-/

namespace GRHArticle.SingularModuli

open Polynomial

noncomputable def quadratic64Int : ℤ[X] :=
  C (-7367066619912) + C (-82226316240)*X + X^2

private theorem monic64 : quadratic64Int.Monic := by unfold quadratic64Int; monicity!
private theorem degree64 : quadratic64Int.natDegree = 2 := by unfold quadratic64Int; compute_degree!

private def coefficients64 : List ℤ := [-7367066619912,-82226316240,1]

/-- Synthetic division in descending order by the displayed monic quadratic.
The finite multiplication check below verifies the quotient. -/
private def quotient64 (l : List ℤ) : List ℤ :=
  (l.drop 2).reverse.foldl (fun acc c ↦
    (c + 82226316240 * acc.getD 0 0 + 7367066619912 * acc.getD 1 0) :: acc) []

private def cofactor64 := quotient64 (quotient64 Prime17Data.diagonal)

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
private theorem diagonal_factor64 : coefficientListPolynomial Prime17Data.diagonal =
    quadratic64Int^2 * coefficientListPolynomial cofactor64 := by
  let sq := multiplyPackedIntegerPolynomial 5 coefficients64 coefficients64
  have h : Prime17Data.diagonal = multiplyPackedIntegerPolynomial 35 sq cofactor64 := by decide +kernel
  have he : coefficientListPolynomial coefficients64 = quadratic64Int := by
    simp [coefficients64,coefficientListPolynomial,quadratic64Int]
    ring
  have hd : (coefficientListPolynomial coefficients64 * coefficientListPolynomial coefficients64).natDegree < 5 :=
    Polynomial.natDegree_mul_le.trans_lt (by rw [he,degree64]; decide)
  have hs : coefficientListPolynomial sq = quadratic64Int^2 := by
    dsimp only [sq]
    rw [coefficientListPolynomial_multiplyPackedIntegerPolynomial _ _ _ hd,he,pow_two]
  have h₁ : (coefficientListPolynomial sq).natDegree ≤ 4 := natDegree_coefficientListPolynomial_le (by decide)
  have h₂ : (coefficientListPolynomial cofactor64).natDegree ≤ 30 := natDegree_coefficientListPolynomial_le (by decide +kernel)
  rw [h,coefficientListPolynomial_multiplyPackedIntegerPolynomial _ _ _
    (Polynomial.natDegree_mul_le.trans_lt (by omega)),hs]

set_option maxRecDepth 150000 in
set_option maxHeartbeats 0 in
private theorem cofactor64_nonzero (i : Fin 2) :
    aeval (quadratic64Value i) (coefficientListPolynomial cofactor64) ≠ 0 := by
  apply RationalComplexBox.ne_zero_of_contains_of_excludesZero
    (RationalComplexBox.contains_evaluateIntegerCoefficients (quadratic64Box_contains i) _)
  fin_cases i <;> decide +kernel

theorem quadratic64Value_isRoot (i : Fin 2) : aeval (quadratic64Value i) quadratic64Int = 0 := by
  let f := quadratic64Form i
  let z := quadraticPoint 64 f.a f.b
  have hdiag := Prime17Data.diagonalEval_eq_of_packed_checks Prime17Data.discriminant_check
    Prime17Data.invariant_check Prime17Data.invariant_nonnegative Prime17Data.trace_checks
    Prime17Data.elementary_zero_check Prime17Data.elementary_checks Prime17Data.diagonal_check z
  exact aeval_factor_eq_zero_of_primeHeckeDiagonal_zero 17 _ _ _ 2 hdiag diagonal_factor64
    (quadratic64_heckeDiagonal_zero i) (cofactor64_nonzero i)

/-- The integer quadratic remains irreducible over the rationals, as seen
by its reduction X²−2 modulo five. -/
theorem quadratic64_irreducible : Irreducible (quadratic64Int.map (algebraMap ℤ ℚ)) := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let φ := Int.castRingHom (ZMod 5)
  have hmod : Irreducible (quadratic64Int.map φ) := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · rw [monic64.natDegree_map φ,degree64]; decide
    · intro x
      simp only [quadratic64Int,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,
        Polynomial.map_C,Polynomial.map_X,Polynomial.IsRoot,eval_add,eval_mul,eval_X,eval_C,eval_pow]
      revert x
      decide +kernel
  exact monic64.isPrimitive.irreducible_iff_irreducible_map_fraction_map.mp
    (Monic.irreducible_of_irreducible_map φ quadratic64Int monic64 hmod)

/-- The analytic class polynomial of the order of conductor four in the
Gaussian field has the stated integer coefficients. -/
theorem analyticClassPolynomial_sixtyFour_eq : analyticClassPolynomial 64 =
    quadratic64Int.map (Int.castRingHom ℂ) := by
  let H := quadratic64Int.map (Int.castRingHom ℂ)
  have hroot (i : Fin 2) : X-C (quadratic64Value i) ∣ H := by
    apply dvd_iff_isRoot.mpr
    rw [Polynomial.IsRoot]
    change (quadratic64Int.map (Int.castRingHom ℂ)).eval (quadratic64Value i) = 0
    rw [← Polynomial.eval₂_eq_eval_map]
    exact quadratic64Value_isRoot i
  have hne : quadratic64Value 0 ≠ quadratic64Value 1 :=
    RationalComplexBox.ne_of_contains_of_separated (quadratic64Box_contains 0)
      (quadratic64Box_contains 1) (by decide +kernel)
  have hcop := isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
  have hdiv : analyticClassPolynomial 64 ∣ H := by
    rw [analyticClassPolynomial,reducedForms_sixtyFour,Finset.prod_insert (by decide),Finset.prod_singleton]
    exact hcop.mul_dvd (hroot 0) (hroot 1)
  symm
  apply eq_of_monic_of_dvd_of_natDegree_le (analyticClassPolynomial_monic 64) (monic64.map _) hdiv
  rw [monic64.natDegree_map,degree64,analyticClassPolynomial_natDegree,reducedForms_sixtyFour]
  decide

/-- Every actual singular modulus of discriminant −64 has minimum support
three among all rational annihilating polynomials. -/
theorem quadratic64_singularModulus_minimumSupport {f : FormCoefficients}
    (hf : f ∈ reducedForms 64) : ∃ hx : IsIntegral ℚ (reducedFormInvariant 64 f),
      minimumSupport hx = 3 := by
  let x := reducedFormInvariant 64 f
  let H := quadratic64Int.map (algebraMap ℤ ℚ)
  have hroot : aeval x H = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    rw [reducedForms_sixtyFour,Finset.mem_insert,Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · exact quadratic64Value_isRoot 0
    · exact quadratic64Value_isRoot 1
  have hmonic : H.Monic := monic64.map _
  have hx : IsIntegral ℚ x := ⟨H,hmonic,hroot⟩
  refine ⟨hx, minimumSupport_eq_three_of_analyticClassPolynomial (D := 64) ?_ hx ?_⟩
  · rw [reducedForms_sixtyFour]; decide
  · rw [← minpoly.eq_of_irreducible_of_monic quadratic64_irreducible hroot hmonic,
      analyticClassPolynomial_sixtyFour_eq,Polynomial.map_map]
    rfl

end GRHArticle.SingularModuli
