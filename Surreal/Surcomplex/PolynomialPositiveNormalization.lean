import Surreal.Surcomplex.PolynomialRootReflection

/-!
# Positive normalization of a polynomial at zero

Multiplication by a constant of modulus one makes a nonzero value at zero
positive real, preserving all pointwise moduli and roots. Combined with
root reflection, this supplies the normalized factor in
`trigonometry:thm:fejer`.
-/

universe u
namespace Surreal.Surcomplex

open Foundations Polynomial

noncomputable section

/-- The phase-cancelling scalar that makes a nonzero value positive real. -/
def positiveNormalizationScalar (a : Surcomplex.{u}) : Surcomplex.{u} := ofReal (modulus a) / a

/-- The normalizing scalar has modulus one when the value being normalized is nonzero. -/
theorem modulus_positiveNormalizationScalar (a : Surcomplex.{u}) (ha : a ≠ 0) :
    modulus (positiveNormalizationScalar a) = 1 := by
  rw [positiveNormalizationScalar, modulus_div, modulus_ofReal, abs_of_nonneg (modulus_nonneg a),
    div_self (ne_of_gt (modulus_pos ha))]

/-- Positive normalization keeps the polynomial in its coefficient field. -/
def positiveNormalize (p : Polynomial Surcomplex.{u}) : Polynomial Surcomplex.{u} :=
  C (positiveNormalizationScalar (p.eval 0)) * p

/-- Normalization does not increase polynomial degree. -/
theorem natDegree_positiveNormalize_le (p : Polynomial Surcomplex.{u}) :
    (positiveNormalize p).natDegree ≤ p.natDegree := natDegree_C_mul_le _ _

/-- The new value at zero is exactly the embedded positive modulus. -/
theorem positiveNormalize_eval_zero (p : Polynomial Surcomplex.{u}) (hp : p.eval 0 ≠ 0) :
    (positiveNormalize p).eval 0 = ofReal (modulus (p.eval 0)) := by
  rw [positiveNormalize, eval_mul, eval_C, positiveNormalizationScalar, div_mul_cancel₀ _ hp]

/-- Normalization preserves the modulus at every point, not just boundary points. -/
theorem modulus_positiveNormalize (p : Polynomial Surcomplex.{u}) (hp : p.eval 0 ≠ 0)
    (z : Surcomplex.{u}) : modulus ((positiveNormalize p).eval z) = modulus (p.eval z) := by
  rw [positiveNormalize, eval_mul, eval_C, modulus_mul,
    modulus_positiveNormalizationScalar _ hp, one_mul]

/-- A normalized polynomial is nonvanishing wherever the original polynomial is. -/
theorem positiveNormalize_eval_ne_zero (p : Polynomial Surcomplex.{u}) (hp : p.eval 0 ≠ 0)
    (z : Surcomplex.{u}) (hz : p.eval z ≠ 0) : (positiveNormalize p).eval z ≠ 0 := by
  intro he
  have hm := modulus_positiveNormalize p hp z
  rw [he, modulus_zero] at hm
  exact hz ((modulus_eq_zero_iff _).mp hm.symm)

/-- Every nonzero polynomial has a normalized representative with no zeros in the open disk. -/
theorem exists_normalized_outer_polynomial (p : Polynomial Surcomplex.{u}) (hp : p ≠ 0) :
    ∃ Q : Polynomial Surcomplex.{u}, Q.natDegree ≤ p.natDegree ∧
      (∀ z : Surcomplex.{u}, modulus z = 1 → modulus (Q.eval z) = modulus (p.eval z)) ∧
      (∀ z : Surcomplex.{u}, modulus z < 1 → Q.eval z ≠ 0) ∧
      ∃ r : SignSequence.{u}, 0 < r ∧ Q.eval 0 = ofReal r := by
  have hzero : (outerPolynomial p).eval 0 ≠ 0 :=
    outerPolynomial_ne_zero_on_disk p hp 0 (by simp)
  refine ⟨positiveNormalize (outerPolynomial p),
    (natDegree_positiveNormalize_le _).trans (natDegree_outerPolynomial_le p), ?_, ?_, ?_⟩
  · intro z hz
    rw [modulus_positiveNormalize _ hzero, modulus_outerPolynomial p z hz]
  · intro z hz
    exact positiveNormalize_eval_ne_zero _ hzero z (outerPolynomial_ne_zero_on_disk p hp z hz)
  · exact ⟨modulus ((outerPolynomial p).eval 0), modulus_pos hzero,
      positiveNormalize_eval_zero _ hzero⟩


/-- Positive values at zero remove the remaining ambiguity of a scalar of modulus one. -/
theorem eq_of_unit_scalar_and_positive_at_zero (p q : Polynomial Surcomplex.{u})
    (c : Surcomplex.{u}) (hc : modulus c = 1) (he : p = C c * q)
    (hp : ∃ r : SignSequence.{u}, 0 < r ∧ p.eval 0 = ofReal r)
    (hq : ∃ s : SignSequence.{u}, 0 < s ∧ q.eval 0 = ofReal s) : p = q := by
  obtain ⟨r, hr, hpr⟩ := hp
  obtain ⟨s, hs, hqs⟩ := hq
  have hv := congrArg (fun P : Polynomial Surcomplex.{u} => P.eval 0) he
  rw [hpr, eval_mul, eval_C, hqs] at hv
  have hm := congrArg modulus hv
  rw [modulus_ofReal, modulus_mul, hc, modulus_ofReal, one_mul,
    abs_of_pos hr, abs_of_pos hs] at hm
  have hn : ofReal s ≠ 0 := by
    intro hz
    have hh := ofReal_injective (by simpa only [map_zero] using hz : ofReal s = ofReal 0)
    exact (ne_of_gt hs) hh
  have hc1 : c = 1 := by
    apply mul_right_cancel₀ hn
    rw [← hv, one_mul, hm]
  rw [he, hc1, C_1, one_mul]

end
end Surreal.Surcomplex
