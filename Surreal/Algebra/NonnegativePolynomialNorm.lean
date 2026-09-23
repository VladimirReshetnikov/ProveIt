import Surreal.Algebra.ConjugatePolynomialFactor
import Surreal.Algebra.OrderedSquareRoots
import Surreal.Algebra.Polynomial

/-!
# Norm-square factorization of nonnegative polynomials

The finite factor construction for `trigonometry:lem:twosquares`.
The coefficient field is ordered, has nonnegative square roots, and its
quadratic complexification is algebraically closed. All these properties
are already proved for the actual surreal and surcomplex fields.
-/

namespace Surreal.Complexify

open Polynomial

noncomputable section
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [HasNonnegSquareRoots F] [IsAlgClosed (Complexify F)]

/-- A nonnegative real polynomial is the product of one complex factor and its conjugate. -/
theorem exists_polynomial_norm_factor (p : F[X]) (hn : ∀ x : F, 0 ≤ p.eval x) :
    ∃ Q : (Complexify F)[X], p.map (algebraMap F (Complexify F)) =
      Q * Q.map (starRingEnd (Complexify F)) := by
  induction hdeg : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases hd : p.natDegree = 0
    · have he : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hd
      have hc : 0 ≤ p.coeff 0 := by simpa only [← coeff_zero_eq_eval_zero] using hn 0
      obtain ⟨s, _, hs⟩ := HasNonnegSquareRoots.exists_nonneg_sq hc
      refine ⟨C (algebraMap F (Complexify F) s), ?_⟩
      conv_lhs => rw [he]
      simp only [map_C]
      have hstar : star (algebraMap F (Complexify F) s) = algebraMap F (Complexify F) s := by
        apply QuadraticAlgebra.ext <;> simp
      simp only [starRingEnd_apply, hstar, ← map_mul]
      rw [← pow_two, hs]
    · have hp : p ≠ 0 := by intro hz; simp [hz] at hd
      have hm : 0 < (p.map (algebraMap F (Complexify F))).natDegree := by
        rw [natDegree_map_eq_of_injective (algebraMap F (Complexify F)).injective]
        exact Nat.pos_of_ne_zero hd
      obtain ⟨z, hz⟩ := FinitePolynomial.exists_root _ hm
      by_cases hi : z.im = 0
      · have hzreal : z = algebraMap F (Complexify F) z.re := by
          apply QuadraticAlgebra.ext <;> simp [hi]
        have hr : p.IsRoot z.re := by
          have hv := hz
          rw [IsRoot, hzreal, eval_map_apply] at hv
          exact (algebraMap F (Complexify F)).injective (by simpa using hv)
        obtain ⟨m, q, hmult, he, hqn, hqa⟩ :=
          FinitePolynomial.nonnegative_root_factorization p hp hn z.re
        have hmp : 0 < m := by
          have ht := (rootMultiplicity_pos hp).mpr hr
          omega
        have hq : q ≠ 0 := by intro h; simp [h] at he; exact hp he
        have hqd : q.natDegree < n := by
          have ht : p.natDegree = 2 * m + q.natDegree := by
            conv_lhs => rw [he]
            rw [natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero _)) hq]
            simp only [natDegree_pow, natDegree_X_sub_C, mul_one]
          omega
        obtain ⟨Q, hQ⟩ := ih q.natDegree hqd q hqn rfl
        let R := ((X - C z.re) ^ m).map (algebraMap F (Complexify F))
        refine ⟨R * Q, ?_⟩
        have hR : R.map (starRingEnd (Complexify F)) = R := conjugate_map_real _
        rw [he, Polynomial.map_mul, hQ, Polynomial.map_mul, hR]
        have hpow : ((X - C z.re) ^ (2 * m)).map (algebraMap F (Complexify F)) = R * R := by
          rw [show 2 * m = m + m by omega, pow_add, Polynomial.map_mul]
        rw [hpow]
        ring
      · obtain ⟨q, he⟩ := rootQuadratic_dvd p z hi hz
        have hq : q ≠ 0 := by intro h; simp [h] at he; exact hp he
        have hquadratic : rootQuadratic z ≠ 0 := by
          intro h
          have hdq := natDegree_rootQuadratic z
          simp [h] at hdq
        have hqd : q.natDegree < n := by
          have ht : p.natDegree = 2 + q.natDegree := by
            conv_lhs => rw [he]
            rw [natDegree_mul hquadratic hq, natDegree_rootQuadratic]
          omega
        have hqn := nonnegative_of_rootQuadratic_factor q z hi (fun x => by rw [← he]; exact hn x)
        obtain ⟨Q, hQ⟩ := ih q.natDegree hqd q hqn rfl
        refine ⟨(X - C z) * Q, ?_⟩
        rw [he, Polynomial.map_mul, map_rootQuadratic, hQ]
        simp only [Polynomial.map_mul, Polynomial.map_sub, map_X, map_C, starRingEnd_apply]
        ring


omit [HasNonnegSquareRoots F] [IsAlgClosed (Complexify F)] in
/-- A polynomial norm identity evaluates to the literal sum of two coordinate squares. -/
theorem eval_of_polynomial_norm_factor (p : F[X]) (Q : (Complexify F)[X])
    (he : p.map (algebraMap F (Complexify F)) = Q * Q.map (starRingEnd (Complexify F)))
    (x : F) : p.eval x = normSq (Q.eval (algebraMap F (Complexify F) x)) := by
  have hx : star (algebraMap F (Complexify F) x) = algebraMap F (Complexify F) x := by
    apply QuadraticAlgebra.ext <;> simp
  have hc := eval_map_apply (p := Q) (starRingEnd (Complexify F))
    (algebraMap F (Complexify F) x)
  simp only [starRingEnd_apply, hx] at hc
  apply (algebraMap F (Complexify F)).injective
  have hv := congrArg (fun P : (Complexify F)[X] => P.eval (algebraMap F (Complexify F) x)) he
  rw [eval_map_apply, eval_mul, hc, mul_conj] at hv
  exact hv

omit [HasNonnegSquareRoots F] [IsAlgClosed (Complexify F)] in
/-- The norm identity forces exactly half the original degree for a nonzero polynomial. -/
theorem natDegree_of_polynomial_norm_factor (p : F[X]) (hp : p ≠ 0) (Q : (Complexify F)[X])
    (he : p.map (algebraMap F (Complexify F)) = Q * Q.map (starRingEnd (Complexify F))) :
    2 * Q.natDegree = p.natDegree := by
  have hQ : Q ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at he
    exact hp ((Polynomial.map_eq_zero _).mp he)
  have hQc : Q.map (starRingEnd (Complexify F)) ≠ 0 := by
    exact fun h => hQ ((Polynomial.map_eq_zero _).mp h)
  have hd := congrArg Polynomial.natDegree he
  rw [natDegree_map_eq_of_injective (algebraMap F (Complexify F)).injective,
    natDegree_mul hQ hQc, natDegree_map_eq_of_injective (starRingEnd (Complexify F)).injective] at hd
  omega

/-- Norm-square factorization with its exact degree, valid also for the zero polynomial. -/
theorem nonnegative_polynomial_norm_factorization (p : F[X]) (hn : ∀ x : F, 0 ≤ p.eval x) :
    ∃ Q : (Complexify F)[X],
      p.map (algebraMap F (Complexify F)) = Q * Q.map (starRingEnd (Complexify F)) ∧
      (∀ x : F, p.eval x = normSq (Q.eval (algebraMap F (Complexify F) x))) ∧
      Q.natDegree = p.natDegree / 2 := by
  by_cases hp : p = 0
  · subst p
    exact ⟨0, by simp, by simp, by simp⟩
  obtain ⟨Q, hQ⟩ := exists_polynomial_norm_factor p hn
  refine ⟨Q, hQ, eval_of_polynomial_norm_factor p Q hQ, ?_⟩
  have hd := natDegree_of_polynomial_norm_factor p hp Q hQ
  omega

/-- Everywhere nonnegative is equivalent to admitting a polynomial norm factor. -/
theorem nonnegative_iff_polynomial_norm_factor (p : F[X]) :
    (∀ x : F, 0 ≤ p.eval x) ↔ ∃ Q : (Complexify F)[X],
      p.map (algebraMap F (Complexify F)) = Q * Q.map (starRingEnd (Complexify F)) := by
  refine ⟨exists_polynomial_norm_factor p, ?_⟩
  rintro ⟨Q, hQ⟩ x
  rw [eval_of_polynomial_norm_factor p Q hQ]
  exact normSq_nonneg _

end
end Surreal.Complexify
