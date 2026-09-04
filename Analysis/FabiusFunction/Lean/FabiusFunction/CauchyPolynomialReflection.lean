import FabiusFunction.CauchyPolynomials
import FabiusFunction.TransseriesBlockAntiderivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Polynomial

/-!
# Reflection of the Cauchy polynomials

The Cauchy polynomials of the first kind satisfy
`b_n(n - 2 - x) = (-1)^n b_n(x)`.  The centre is `(n - 2)/2`;
the shift by two comes from reflecting both the falling factorial and
the integration interval.  This is `eq:merged-cauchy-reflection` in
Combinatorial Coefficient Calculus.

We first identify `b_n(a)` with the formal integral of `(a + u)_n`.
Reflection of the interval then proves an identity in `ℚ[X]`, so it
can be evaluated in every commutative `ℚ`-algebra.  The argument uses
only polynomial integration and includes `n = 0`.  The final theorem
also identifies this formal integral with the real interval integral,
using the difference equation and the fundamental theorem of calculus.
-/

set_option autoImplicit false

open Polynomial Finset

namespace Fabius

/-- The formal integral over `[0,1]` is invariant under `u ↦ 1-u`. -/
theorem intPoly_comp_one_sub_X (p : ℚ[X]) :
    intPoly (p.comp (1 - X)) = intPoly p := by
  obtain ⟨q, rfl⟩ := derivative_surjective (K := ℚ) p
  have h := intPoly_derivative (q.comp (1 - X))
  rw [derivative_comp_one_sub_X, map_neg] at h
  simp only [eval_comp, eval_sub, eval_one, eval_X, sub_self, sub_zero] at h
  rw [intPoly_derivative]
  linarith

/-- The integral of a falling factorial is the corresponding Cauchy number. -/
theorem intPoly_descPochhammer (n : ℕ) :
    intPoly (descPochhammer ℚ n) = (cauchyPoly n).eval 0 := by
  rw [descPochhammer_eq_sum_monomial_signedStirlingFirst, map_sum,
    cauchyPoly_eval_zero]
  exact Finset.sum_congr rfl fun k _ => intPoly_monomial k _

/-- The defining integral of a Cauchy polynomial, interpreted as exact
polynomial integration: `b_n(a) = ∫₀¹ (a+u)_n du`. -/
theorem cauchyPoly_eval_eq_intPoly (n : ℕ) (a : ℚ) :
    (cauchyPoly n).eval a =
      intPoly ((descPochhammer ℚ n).comp (X + C a)) := by
  have hadd : (descPochhammer ℚ n).comp (X + C a) =
      ∑ k ∈ range (n + 1),
        ((n.choose k : ℚ) * (descPochhammer ℚ (n - k)).eval a) •
          descPochhammer ℚ k := by
    apply Polynomial.funext
    intro u
    simp only [eval_comp, eval_add, eval_X, eval_C, eval_finsetSum, eval_smul]
    rw [descPochhammer_eval_add ℚ]
    exact Finset.sum_congr rfl fun k _ => by simp only [smul_eq_mul]; ring
  rw [hadd, map_sum]
  simp only [map_smul, smul_eq_mul, intPoly_descPochhammer]
  have h := cauchyPoly_eval_add n 0 a
  rw [zero_add] at h
  rw [h]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Reflecting a falling factorial about `(n-1)/2` contributes the sign
`(-1)^n`.  This identity holds over any commutative ring. -/
theorem descPochhammer_eval_reflect {R : Type*} [CommRing R]
    (n : ℕ) (x : R) :
    (descPochhammer R n).eval ((n : R) - 1 - x) =
      (-1 : R) ^ n * (descPochhammer R n).eval x := by
  rw [descPochhammer_eval_eq_prod_range, descPochhammer_eval_eq_prod_range,
    ← Finset.prod_range_reflect (fun j => (n : R) - 1 - x - j) n]
  calc
    ∏ j ∈ range n, ((n : R) - 1 - x - (n - 1 - j : ℕ)) =
        ∏ j ∈ range n, (-(x - j)) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hjn := Finset.mem_range.mp hj
      rw [Nat.cast_sub (by omega : j ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n)]
      push_cast
      ring
    _ = (-1 : R) ^ n * ∏ j ∈ range n, (x - j) := by
      rw [Finset.prod_neg, Finset.card_range]

/-- **Cauchy reflection as a polynomial identity.** The first-kind Cauchy
polynomial `b_n` is even or odd about `(n-2)/2`, according to the parity of `n`. -/
theorem cauchyPoly_reflect (n : ℕ) :
    (cauchyPoly n).comp (C ((n : ℚ) - 2) - X) =
      (-1 : ℚ) ^ n • cauchyPoly n := by
  apply Polynomial.funext
  intro a
  simp only [eval_comp, eval_sub, eval_C, eval_X, eval_smul, smul_eq_mul]
  rw [cauchyPoly_eval_eq_intPoly, cauchyPoly_eval_eq_intPoly]
  have h := intPoly_comp_one_sub_X
    ((descPochhammer ℚ n).comp (X + C ((n : ℚ) - 2 - a)))
  rw [← h]
  have hreflect :
      ((descPochhammer ℚ n).comp (X + C ((n : ℚ) - 2 - a))).comp (1 - X) =
        (-1 : ℚ) ^ n • (descPochhammer ℚ n).comp (X + C a) := by
    apply Polynomial.funext
    intro u
    simp only [eval_comp, eval_add, eval_sub, eval_one, eval_X, eval_C,
      eval_smul, smul_eq_mul]
    convert descPochhammer_eval_reflect n (u + a) using 1
    congr 1
    ring
  rw [hreflect, map_smul, smul_eq_mul]

/-- Cauchy reflection evaluated in an arbitrary commutative `ℚ`-algebra. -/
theorem cauchyPoly_aeval_reflect {A : Type*} [CommRing A] [Algebra ℚ A]
    (n : ℕ) (a : A) :
    aeval ((n : A) - 2 - a) (cauchyPoly n) =
      (-1 : A) ^ n * aeval a (cauchyPoly n) := by
  have h := congrArg (aeval a) (cauchyPoly_reflect n)
  simpa [aeval_comp, Algebra.smul_def, map_ofNat] using h

/-- The Cauchy difference equation evaluated in any commutative `ℚ`-algebra. -/
theorem cauchyPoly_succ_aeval_add_one_sub {A : Type*} [CommRing A] [Algebra ℚ A]
    (n : ℕ) (a : A) :
    aeval (a + 1) (cauchyPoly (n + 1)) - aeval a (cauchyPoly (n + 1)) =
      (n + 1) * aeval a (cauchyPoly n) := by
  have hp : (cauchyPoly (n + 1)).comp (X + 1) - cauchyPoly (n + 1) =
      C (n + 1 : ℚ) * cauchyPoly n := by
    apply Polynomial.funext
    intro x
    simpa using cauchyPoly_succ_eval_add_one_sub n x
  have h := congrArg (aeval a) hp
  simpa [aeval_comp] using h

/-- **The real integral representation of the Cauchy polynomials.**
The primitive is `b_{n+1}(a+u)/(n+1)`, and its endpoint difference is
`b_n(a)` by the Cauchy difference equation. -/
theorem cauchyPoly_aeval_eq_integral (n : ℕ) (a : ℝ) :
    aeval a (cauchyPoly n) =
      ∫ u in (0 : ℝ)..1, aeval (a + u) (descPochhammer ℚ n) := by
  have hder (u : ℝ) :
      HasDerivAt (fun v : ℝ => aeval (a + v) (cauchyPoly (n + 1)))
        ((n + 1) * aeval (a + u) (descPochhammer ℚ n)) u := by
    simpa [Function.comp_def, derivative_cauchyPoly_succ] using!
      ((cauchyPoly (n + 1)).hasDerivAt_aeval (a + u)).comp u
        ((hasDerivAt_id u).const_add a)
  have hint : IntervalIntegrable
      (fun u : ℝ => (n + 1) * aeval (a + u) (descPochhammer ℚ n))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hder u) hint
  rw [intervalIntegral.integral_const_mul] at h
  simp only [add_zero, cauchyPoly_succ_aeval_add_one_sub] at h
  exact (mul_left_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0) h).symm

end Fabius
