import Surreal.Algebra.NonnegativePolynomialRoots
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Degree and leading coefficient of nonnegative polynomials

The leading-coefficient and degree steps toward `trigonometry:lem:twosquares`.
These statements hold over arbitrary ordered fields, with no Archimedean
or completeness assumption. Polynomial reversal turns the behavior at
infinity into continuity at zero in the field's order topology.
-/

namespace Surreal.FinitePolynomial

open Polynomial Filter Topology

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- The reciprocal-coordinate identity uses the polynomial's actual degree. -/
theorem eval_reverse_reciprocal (p : F[X]) (x : F) (hx : x ≠ 0) :
    p.reverse.eval x * (x⁻¹) ^ p.natDegree = p.eval (x⁻¹) := by
  letI : Invertible (x⁻¹) := invertibleOfNonzero (inv_ne_zero hx)
  simpa only [invOf_eq_inv, inv_inv, eval₂_id] using
    eval₂_reverse_mul_pow (RingHom.id F) (x⁻¹) p

/-- A polynomial nonnegative everywhere has nonnegative leading coefficient. -/
theorem leadingCoeff_nonneg_of_nonnegative (p : F[X])
    (hp : ∀ x : F, 0 ≤ p.eval x) : 0 ≤ p.leadingCoeff := by
  letI : TopologicalSpace F := Preorder.topology F
  letI : OrderTopology F := ⟨rfl⟩
  by_contra hn
  have hc : p.reverse.eval 0 < 0 := by
    simpa only [← coeff_zero_eq_eval_zero, coeff_zero_reverse] using (lt_of_not_ge hn)
  have he : ∀ᶠ x in 𝓝 (0 : F), p.reverse.eval x < 0 :=
    p.reverse.continuousAt.eventually (gt_mem_nhds hc)
  obtain ⟨x, hx, he⟩ := ((frequently_gt_nhds (0 : F)).and_eventually he).exists
  have hv := eval_reverse_reciprocal p x (ne_of_gt hx)
  have hneg : p.eval x⁻¹ < 0 := by
    rw [← hv]
    exact mul_neg_of_neg_of_pos he (pow_pos (inv_pos.mpr hx) _)
  exact (not_lt_of_ge (hp _)) hneg

/-- Every nonzero everywhere-nonnegative polynomial has strictly positive leading coefficient. -/
theorem leadingCoeff_pos_of_nonnegative (p : F[X]) (hp : p ≠ 0)
    (hn : ∀ x : F, 0 ≤ p.eval x) : 0 < p.leadingCoeff :=
  lt_of_le_of_ne (leadingCoeff_nonneg_of_nonnegative p hn)
    (Ne.symm (leadingCoeff_ne_zero.mpr hp))

/-- The degree of an everywhere-nonnegative polynomial is even, including the zero polynomial. -/
theorem even_natDegree_of_nonnegative (p : F[X])
    (hp : ∀ x : F, 0 ≤ p.eval x) : Even p.natDegree := by
  letI : TopologicalSpace F := Preorder.topology F
  letI : OrderTopology F := ⟨rfl⟩
  by_cases hz : p = 0
  · simp [hz]
  by_contra hn
  have hodd := Nat.not_even_iff_odd.mp hn
  have hc : 0 < p.reverse.eval 0 := by
    simpa only [← coeff_zero_eq_eval_zero, coeff_zero_reverse] using leadingCoeff_pos_of_nonnegative p hz hp
  have he : ∀ᶠ x in 𝓝 (0 : F), 0 < p.reverse.eval x :=
    p.reverse.continuousAt.eventually (lt_mem_nhds hc)
  obtain ⟨x, hx, he⟩ := ((frequently_lt_nhds (0 : F)).and_eventually he).exists
  have hv := eval_reverse_reciprocal p x (ne_of_lt hx)
  have hneg : p.eval x⁻¹ < 0 := by
    rw [← hv]
    exact mul_neg_of_pos_of_neg he (hodd.pow_neg (inv_lt_zero.mpr hx))
  exact (not_lt_of_ge (hp _)) hneg

end Surreal.FinitePolynomial
