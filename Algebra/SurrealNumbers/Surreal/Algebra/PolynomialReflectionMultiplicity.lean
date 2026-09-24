import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# Multiplicity under polynomial reflection

Mathlib's bounded reflection represents `X^N p(1/X)`. At a nonzero
point, its root multiplicity equals the original multiplicity at the
reciprocal point. This is the finite algebra needed to recover root data
from a boundary norm in the uniqueness clause of `trigonometry:thm:fejer`.
-/

namespace Surreal.FinitePolynomial

open Polynomial

variable {K : Type*} [Field K]

/-- Reflection of a power of a monic linear factor, with its precise degree bound. -/
theorem reflect_linear_pow (b : K) (m : ℕ) :
    ((X - C b) ^ m).reflect m = (1 - C b * X) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, reflect_mul _ _ (by simp) (by simp), ih, pow_succ]
    simp

/-- Bounded coefficient reflection preserves multiplicities at reciprocal nonzero points. -/
theorem rootMultiplicity_reflect (p : K[X]) (N : ℕ) (hN : p.natDegree ≤ N)
    (a : K) (ha : a ≠ 0) :
    (p.reflect N).rootMultiplicity a = p.rootMultiplicity a⁻¹ := by
  by_cases hp : p = 0
  · simp [hp]
  let m := p.rootMultiplicity a⁻¹
  obtain ⟨q, he, hq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp a⁻¹
  have hqn : q ≠ 0 := by intro h; rw [h, mul_zero] at he; exact hp he
  have hd : p.natDegree = m + q.natDegree := by
    conv_lhs => rw [he]
    rw [natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero _)) hqn]
    simp only [natDegree_pow, natDegree_X_sub_C, mul_one, m]
  have hm : m ≤ N := by omega
  have hqd : q.natDegree ≤ N - m := by omega
  have hqa : q.eval a⁻¹ ≠ 0 := by simpa only [dvd_iff_isRoot, IsRoot] using hq
  have hr : (q.reflect (N - m)).eval a ≠ 0 := by
    letI : Invertible (a⁻¹) := invertibleOfNonzero (inv_ne_zero ha)
    have hz := eval₂_reflect_eq_zero_iff (RingHom.id K) a⁻¹ (N - m) q hqd
    simp only [invOf_eq_inv, inv_inv, eval₂_id] at hz
    exact fun h => hqa (hz.mp h)
  have hlin : (1 - C a⁻¹ * X : K[X]) = C (-a⁻¹) * (X - C a) := by
    rw [mul_sub, ← C_mul, neg_mul, inv_mul_cancel₀ ha]
    simp only [map_neg, map_one]
    ring
  have hscalar : (-a⁻¹) ^ m ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr (inv_ne_zero ha))
  let r := C ((-a⁻¹) ^ m) * q.reflect (N - m)
  have hre : r.eval a ≠ 0 := by
    simpa only [r, eval_mul, eval_C] using mul_ne_zero hscalar hr
  have hrefl : p.reflect N = r * (X - C a) ^ m := by
    conv_lhs => rw [he]
    change (((X - C a⁻¹) ^ m) * q).reflect N = _
    rw [show N = m + (N - m) by omega,
      reflect_mul _ _ (by simp) hqd, reflect_linear_pow, hlin, mul_pow, ← map_pow]
    change C ((-a⁻¹) ^ m) * (X - C a) ^ m * q.reflect (N - m) = _
    dsimp only [r]
    ring
  rw [hrefl, rootMultiplicity_mul_X_sub_C_pow (by
    intro h
    exact hre (by rw [h, eval_zero])), rootMultiplicity_eq_zero hre, zero_add]

/-- Reversing at the actual degree is the special case used by reciprocal root pairing. -/
theorem rootMultiplicity_reverse (p : K[X]) (a : K) (ha : a ≠ 0) :
    p.reverse.rootMultiplicity a = p.rootMultiplicity a⁻¹ :=
  rootMultiplicity_reflect p p.natDegree le_rfl a ha

end Surreal.FinitePolynomial
