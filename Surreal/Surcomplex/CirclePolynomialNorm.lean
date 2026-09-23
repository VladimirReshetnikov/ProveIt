import Surreal.Algebra.PolynomialReflectionMultiplicity
import Surreal.Surcomplex.Cayley
import Surreal.Surcomplex.AlgebraicallyClosed

/-!
# Polynomial encoding of a squared modulus on the unit circle

Conjugate coefficient reflection turns a boundary norm into an ordinary
polynomial. Its reciprocal-root multiplicity formula and the injective
Cayley chart support normalized uniqueness in `trigonometry:thm:fejer`.
-/

universe u
namespace Surreal.Surcomplex

open Foundations Polynomial

noncomputable section

/-- Coefficient conjugation followed by reflection at a prescribed degree bound. -/
def conjugateReflect (p : Polynomial Surcomplex.{u}) (N : ℕ) : Polynomial Surcomplex.{u} :=
  (p.map conj.toRingHom).reflect N

/-- Conjugate reflection preserves nonzeroness. -/
theorem conjugateReflect_ne_zero (p : Polynomial Surcomplex.{u}) (N : ℕ) (hp : p ≠ 0) :
    conjugateReflect p N ≠ 0 := by
  simpa only [conjugateReflect, ne_eq, reflect_eq_zero_iff, Polynomial.map_eq_zero] using hp

/-- Conjugate reflection exchanges the multiplicities of conjugate reciprocal points. -/
theorem rootMultiplicity_conjugateReflect (p : Polynomial Surcomplex.{u}) (N : ℕ)
    (hp : p.natDegree ≤ N) (a : Surcomplex.{u}) (ha : a ≠ 0) :
    (conjugateReflect p N).rootMultiplicity a = p.rootMultiplicity (conj a)⁻¹ := by
  rw [conjugateReflect, FinitePolynomial.rootMultiplicity_reflect _ N (by
    rwa [natDegree_map_eq_of_injective conj.injective]) a ha]
  have he := Polynomial.eq_rootMultiplicity_map (p := p) (f := conj.toRingHom)
    conj.injective ((conj a)⁻¹)
  change p.rootMultiplicity ((conj a)⁻¹) =
    (p.map conj.toRingHom).rootMultiplicity (conj ((conj a)⁻¹)) at he
  simpa only [map_inv₀, conj_conj] using he.symm

/-- On the circle, conjugate reflection is conjugate evaluation times the degree power. -/
theorem eval_conjugateReflect_on_circle (p : Polynomial Surcomplex.{u}) (N : ℕ)
    (hp : p.natDegree ≤ N) (z : Surcomplex.{u}) (hz : modulus z = 1) :
    (conjugateReflect p N).eval z = z ^ N * conj (p.eval z) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hu : z * conj z = 1 := by
    rw [mul_conj, ← modulus_sq, hz, one_pow, map_one]
  have hconj : conj z = z⁻¹ := (mul_eq_one_iff_eq_inv₀ hz0).mp (by rw [mul_comm]; exact hu)
  letI : Invertible (conj z) := invertibleOfNonzero (by rw [hconj]; exact inv_ne_zero hz0)
  have he := eval₂_reflect_mul_pow (RingHom.id Surcomplex.{u}) (conj z) N
    (p.map conj.toRingHom) (by rwa [natDegree_map_eq_of_injective conj.injective])
  have hinv : (conj z)⁻¹ = z := by rw [hconj, inv_inv]
  simp only [invOf_eq_inv, hinv, eval₂_id] at he
  have hc := eval_map_apply (p := p) conj.toRingHom z
  change (p.map conj.toRingHom).eval (conj z) = conj (p.eval z) at hc
  rw [hc] at he
  change (conjugateReflect p N).eval z * (conj z) ^ N = conj (p.eval z) at he
  have hunit : (conj z) ^ N * z ^ N = 1 := by rw [← mul_pow, mul_comm, hu, one_pow]
  calc
    _ = (conjugateReflect p N).eval z * ((conj z) ^ N * z ^ N) := by rw [hunit, mul_one]
    _ = conj (p.eval z) * z ^ N := by rw [← mul_assoc, he]
    _ = _ := mul_comm _ _

/-- The ordinary polynomial representing `z^N` times the boundary squared modulus. -/
def circleNormPolynomial (p : Polynomial Surcomplex.{u}) (N : ℕ) : Polynomial Surcomplex.{u} :=
  p * conjugateReflect p N

/-- The norm polynomial evaluates to the actual squared modulus on every unit point. -/
theorem eval_circleNormPolynomial (p : Polynomial Surcomplex.{u}) (N : ℕ)
    (hp : p.natDegree ≤ N) (z : Surcomplex.{u}) (hz : modulus z = 1) :
    (circleNormPolynomial p N).eval z = z ^ N * ofReal (modulus (p.eval z) ^ 2) := by
  rw [circleNormPolynomial, eval_mul, eval_conjugateReflect_on_circle p N hp z hz, modulus_sq,
    ← mul_conj]
  ring

/-- Agreement on the actual unit circle determines an ordinary surcomplex polynomial. -/
theorem polynomial_eq_of_unit_circle (p q : Polynomial Surcomplex.{u})
    (h : ∀ z : Surcomplex.{u}, modulus z = 1 → p.eval z = q.eval z) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hinj : Function.Injective (cayley : SignSequence.{u} → Surcomplex.{u}) := by
    intro x y he
    simpa only [cayleyCoord_cayley] using congrArg cayleyCoord he
  exact (Set.infinite_range_of_injective hinj).mono (by
    rintro z ⟨t, rfl⟩
    exact h _ (modulus_cayley t))

/-- Equal boundary moduli give equal polynomial norm encodings at any common degree bound. -/
theorem circleNormPolynomial_eq_of_modulus_eq (p q : Polynomial Surcomplex.{u}) (N : ℕ)
    (hp : p.natDegree ≤ N) (hq : q.natDegree ≤ N)
    (h : ∀ z : Surcomplex.{u}, modulus z = 1 → modulus (p.eval z) = modulus (q.eval z)) :
    circleNormPolynomial p N = circleNormPolynomial q N := by
  apply polynomial_eq_of_unit_circle
  intro z hz
  rw [eval_circleNormPolynomial p N hp z hz, eval_circleNormPolynomial q N hq z hz, h z hz]

end
end Surreal.Surcomplex
