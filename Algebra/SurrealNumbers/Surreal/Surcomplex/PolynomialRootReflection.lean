import Surreal.Surcomplex.Modulus
import Surreal.Surcomplex.AlgebraicallyClosed

/-!
# Reflecting polynomial roots out of the open unit disk

The root-selection step of the normalized clause of `trigonometry:thm:fejer`.
A root in the open disk is replaced by its conjugate reciprocal factor;
the zero root is removed. This preserves the modulus at every actual unit
point and does not increase the degree.
-/

universe u
namespace Surreal.Surcomplex

open Foundations Polynomial

noncomputable section

/-- Reflection of a linear factor preserves its modulus on the actual unit circle. -/
theorem modulus_sub_eq_reflected (a z : Surcomplex.{u}) (hz : modulus z = 1) :
    modulus (z - a) = modulus (1 - conj a * z) := by
  have hu : z * conj z = 1 := by
    rw [mul_conj, ← modulus_sq, hz, one_pow, map_one]
  calc
    _ = modulus (z * (1 - conj z * a)) := by
      rw [mul_sub, mul_one, ← mul_assoc, hu, one_mul]
    _ = modulus (1 - conj z * a) := by rw [modulus_mul, hz, one_mul]
    _ = modulus (conj (1 - conj z * a)) := (modulus_conj _).symm
    _ = _ := by
      rw [map_sub, map_one, map_mul, conj_conj]
      congr 1
      ring

/-- Reflect an interior root; leave roots on and outside the circle in place. -/
def reflectedLinear (a : Surcomplex.{u}) : Polynomial Surcomplex.{u} :=
  if modulus a < 1 then 1 - C (conj a) * X else X - C a

/-- The reflected factor remains of degree at most one, also for a zero root. -/
theorem natDegree_reflectedLinear_le (a : Surcomplex.{u}) : (reflectedLinear a).natDegree ≤ 1 := by
  unfold reflectedLinear
  split
  · exact (natDegree_sub_le _ _).trans
      (max_le (by simp) ((natDegree_C_mul_le _ _).trans natDegree_X_le))
  · exact (natDegree_sub_le _ _).trans (max_le natDegree_X_le (by simp))

/-- Each chosen linear factor preserves the original boundary modulus. -/
theorem modulus_eval_reflectedLinear (a z : Surcomplex.{u}) (hz : modulus z = 1) :
    modulus ((reflectedLinear a).eval z) = modulus (z - a) := by
  unfold reflectedLinear
  split
  · simpa only [eval_sub, eval_one, eval_mul, eval_C, eval_X] using
      (modulus_sub_eq_reflected a z hz).symm
  · simp

/-- None of the reflected factors vanishes in the open unit disk. -/
theorem eval_reflectedLinear_ne_zero (a z : Surcomplex.{u}) (hz : modulus z < 1) :
    (reflectedLinear a).eval z ≠ 0 := by
  unfold reflectedLinear
  split_ifs with ha
  · simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X]
    intro he
    have hm := congrArg modulus (sub_eq_zero.mp he)
    rw [modulus_one, modulus_mul, modulus_conj] at hm
    have hprod : modulus a * modulus z < 1 := by
      nlinarith [modulus_nonneg a, modulus_nonneg z,
        mul_nonneg (sub_nonneg.mpr ha.le) (sub_nonneg.mpr hz.le)]
    exact (ne_of_lt hprod) hm.symm
  · simp only [eval_sub, eval_X, eval_C]
    intro he
    exact ha (sub_eq_zero.mp he ▸ hz)

/-- Replace all interior roots in Mathlib's finite root factorization. -/
def outerPolynomial (p : Polynomial Surcomplex.{u}) : Polynomial Surcomplex.{u} :=
  C p.leadingCoeff * (p.roots.map reflectedLinear).prod

private theorem natDegree_reflected_prod_le (s : Multiset Surcomplex.{u}) :
    (s.map reflectedLinear).prod.natDegree ≤ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    exact natDegree_mul_le.trans (by have := natDegree_reflectedLinear_le a; omega)

/-- Reflection cannot increase polynomial degree. -/
theorem natDegree_outerPolynomial_le (p : Polynomial Surcomplex.{u}) :
    (outerPolynomial p).natDegree ≤ p.natDegree := by
  exact (natDegree_C_mul_le _ _).trans
    ((natDegree_reflected_prod_le p.roots).trans_eq (FinitePolynomial.roots_card p))

private theorem modulus_reflected_prod (s : Multiset Surcomplex.{u}) (z : Surcomplex.{u})
    (hz : modulus z = 1) :
    modulus ((s.map reflectedLinear).prod.eval z) =
      modulus ((s.map (fun a => X - C a)).prod.eval z) := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, eval_mul, modulus_mul]
    rw [modulus_eval_reflectedLinear a z hz, ih]
    simp

/-- The reflected polynomial has exactly the original modulus at every unit-circle point. -/
theorem modulus_outerPolynomial (p : Polynomial Surcomplex.{u}) (z : Surcomplex.{u})
    (hz : modulus z = 1) : modulus ((outerPolynomial p).eval z) = modulus (p.eval z) := by
  rw [outerPolynomial, eval_mul, modulus_mul, modulus_reflected_prod p.roots z hz]
  conv_rhs => rw [FinitePolynomial.factorization p]
  rw [eval_mul, modulus_mul]

private theorem reflected_prod_ne_zero (s : Multiset Surcomplex.{u}) (z : Surcomplex.{u})
    (hz : modulus z < 1) : (s.map reflectedLinear).prod.eval z ≠ 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, eval_mul]
    exact mul_ne_zero (eval_reflectedLinear_ne_zero a z hz) ih

/-- Every nonzero polynomial has a boundary-modulus representative without open-disk zeros. -/
theorem outerPolynomial_ne_zero_on_disk (p : Polynomial Surcomplex.{u}) (hp : p ≠ 0)
    (z : Surcomplex.{u}) (hz : modulus z < 1) : (outerPolynomial p).eval z ≠ 0 := by
  rw [outerPolynomial, eval_mul, eval_C]
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hp) (reflected_prod_ne_zero p.roots z hz)

end
end Surreal.Surcomplex
