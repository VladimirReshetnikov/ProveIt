import Surreal.Surcomplex.CirclePolynomialNorm
import Surreal.Surcomplex.PolynomialPositiveNormalization

/-!
# Uniqueness of outer polynomial factors

A polynomial with no zeros in the open actual unit disk is determined by
its boundary modulus up to a constant of modulus one. Positive real value
at zero removes that scalar ambiguity. These are the uniqueness steps of
`trigonometry:thm:fejer`, using only finite polynomial root multiplicities.
-/

universe u
namespace Surreal.Surcomplex

open Foundations Polynomial

noncomputable section

/-- The norm encoding adds the multiplicities at a point and its conjugate reciprocal. -/
theorem rootMultiplicity_circleNormPolynomial (p : Polynomial Surcomplex.{u}) (hp : p ≠ 0)
    (N : ℕ) (hN : p.natDegree ≤ N) (a : Surcomplex.{u}) (ha : a ≠ 0) :
    (circleNormPolynomial p N).rootMultiplicity a =
      p.rootMultiplicity a + p.rootMultiplicity (conj a)⁻¹ := by
  rw [circleNormPolynomial, rootMultiplicity_mul (mul_ne_zero hp (conjugateReflect_ne_zero p N hp)),
    rootMultiplicity_conjugateReflect p N hN a ha]

/-- Boundary points are fixed by conjugate reciprocation. -/
theorem conj_inv_eq_self_of_modulus_one (a : Surcomplex.{u}) (ha : modulus a = 1) :
    (conj a)⁻¹ = a := by
  have hu : a * conj a = 1 := by rw [mul_conj, ← modulus_sq, ha, one_pow, map_one]
  exact (eq_inv_of_mul_eq_one_left hu).symm

/-- Equal boundary moduli determine all root multiplicities for polynomials without interior zeros. -/
theorem rootMultiplicity_eq_of_outer_modulus_eq (p q : Polynomial Surcomplex.{u})
    (hp : ∀ z : Surcomplex.{u}, modulus z < 1 → p.eval z ≠ 0)
    (hq : ∀ z : Surcomplex.{u}, modulus z < 1 → q.eval z ≠ 0)
    (he : ∀ z : Surcomplex.{u}, modulus z = 1 → modulus (p.eval z) = modulus (q.eval z))
    (a : Surcomplex.{u}) : p.rootMultiplicity a = q.rootMultiplicity a := by
  have hp0 : p ≠ 0 := by intro h; have := hp 0 (by simp); simp [h] at this
  have hq0 : q ≠ 0 := by intro h; have := hq 0 (by simp); simp [h] at this
  by_cases ha : modulus a < 1
  · rw [rootMultiplicity_eq_zero (hp a ha), rootMultiplicity_eq_zero (hq a ha)]
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  let N := max p.natDegree q.natDegree
  have hpn : p.natDegree ≤ N := le_max_left _ _
  have hqn : q.natDegree ≤ N := le_max_right _ _
  have hm := congrArg (fun P : Polynomial Surcomplex.{u} => P.rootMultiplicity a)
    (circleNormPolynomial_eq_of_modulus_eq p q N hpn hqn he)
  rw [rootMultiplicity_circleNormPolynomial p hp0 N hpn a ha0,
    rootMultiplicity_circleNormPolynomial q hq0 N hqn a ha0] at hm
  by_cases hb : modulus a = 1
  · rw [conj_inv_eq_self_of_modulus_one a hb] at hm
    omega
  · have hlt : modulus ((conj a)⁻¹) < 1 := by
      rw [modulus_inv, modulus_conj]
      exact inv_lt_one_of_one_lt₀ (lt_of_le_of_ne (le_of_not_gt ha) (Ne.symm hb))
    rw [rootMultiplicity_eq_zero (hp _ hlt), rootMultiplicity_eq_zero (hq _ hlt),
      add_zero, add_zero] at hm
    exact hm

/-- Two outer polynomials with equal boundary modulus differ by a scalar of modulus one. -/
theorem exists_unit_scalar_of_outer_modulus_eq (p q : Polynomial Surcomplex.{u})
    (hp : ∀ z : Surcomplex.{u}, modulus z < 1 → p.eval z ≠ 0)
    (hq : ∀ z : Surcomplex.{u}, modulus z < 1 → q.eval z ≠ 0)
    (he : ∀ z : Surcomplex.{u}, modulus z = 1 → modulus (p.eval z) = modulus (q.eval z)) :
    ∃ c : Surcomplex.{u}, modulus c = 1 ∧ p = C c * q := by
  classical
  have hp0 : p ≠ 0 := by intro h; have := hp 0 (by simp); simp [h] at this
  have hq0 : q ≠ 0 := by intro h; have := hq 0 (by simp); simp [h] at this
  have hr : p.roots = q.roots := by
    apply Multiset.ext.mpr
    intro a
    simpa only [Polynomial.count_roots] using rootMultiplicity_eq_of_outer_modulus_eq p q hp hq he a
  let c := p.leadingCoeff / q.leadingCoeff
  have hc : p = C c * q := by
    conv_lhs => rw [FinitePolynomial.factorization p]
    conv_rhs => rw [FinitePolynomial.factorization q]
    rw [hr, ← mul_assoc, ← C_mul]
    dsimp only [c]
    rw [div_mul_cancel₀ _ (Polynomial.leadingCoeff_ne_zero.mpr hq0)]
  have hex : ∃ z : Surcomplex.{u}, modulus z = 1 ∧ q.eval z ≠ 0 := by
    by_contra! h
    apply hq0
    apply polynomial_eq_of_unit_circle
    intro z hz
    simpa only [eval_zero] using h z hz
  obtain ⟨z, hz, hqz⟩ := hex
  have hv := he z hz
  rw [hc, eval_mul, eval_C, modulus_mul] at hv
  have hm : modulus c = 1 := by
    apply mul_right_cancel₀ (ne_of_gt (modulus_pos hqz))
    simpa only [one_mul] using hv
  exact ⟨c, hm, hc⟩

/-- Positive real normalization at zero makes an outer polynomial unique from its boundary modulus. -/
theorem eq_of_normalized_outer_modulus_eq (p q : Polynomial Surcomplex.{u})
    (hp : ∀ z : Surcomplex.{u}, modulus z < 1 → p.eval z ≠ 0)
    (hq : ∀ z : Surcomplex.{u}, modulus z < 1 → q.eval z ≠ 0)
    (he : ∀ z : Surcomplex.{u}, modulus z = 1 → modulus (p.eval z) = modulus (q.eval z))
    (hpPos : ∃ r : SignSequence.{u}, 0 < r ∧ p.eval 0 = ofReal r)
    (hqPos : ∃ r : SignSequence.{u}, 0 < r ∧ q.eval 0 = ofReal r) : p = q := by
  obtain ⟨c, hc, h⟩ := exists_unit_scalar_of_outer_modulus_eq p q hp hq he
  exact eq_of_unit_scalar_and_positive_at_zero p q c hc h hpPos hqPos

end
end Surreal.Surcomplex
