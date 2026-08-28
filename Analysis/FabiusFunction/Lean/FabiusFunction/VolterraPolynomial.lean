import FabiusFunction.VolterraTaylor
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Polynomial commutators for Volterra integrals

Multiplication by a polynomial can be moved through every normalized Volterra
integral by one finite Taylor expansion.  Hasse derivatives are the natural
coefficients: they keep the identity division-free on the polynomial side,
while the rising factorial records the change in the Cauchy kernel.

The result is formulated for arbitrary real normed-space-valued integrands, arbitrary
base points, and either orientation of the interval.  It is the reusable
algebraic layer behind the polynomial-weighted Fabius primitive formulas.

## Main result

* `volterraIntegral_polynomial_smul_of_kernel_intervalIntegrable` is the
  kernel-integrable form of the polynomial commutator.
* `volterraIntegral_polynomial_smul` is its convenient integrable-function
  specialization.
* `volterraIntegral_pow_smul` is the monomial specialization.
-/

set_option autoImplicit false

open Set
open scoped Interval
open MeasureTheory

namespace Fabius

private theorem polynomial_eval_eq_sum_hasse
    (p : Polynomial ℝ) (x t : ℝ) :
    p.eval t =
      ∑ k ∈ Finset.range (p.natDegree + 1),
        (Polynomial.hasseDeriv k p).eval x * (t - x) ^ k := by
  calc
    p.eval t = (Polynomial.taylor x p).eval (t - x) :=
      (Polynomial.taylor_eval_sub x p t).symm
    _ = ∑ k ∈ Finset.range ((Polynomial.taylor x p).natDegree + 1),
          (Polynomial.taylor x p).coeff k * (t - x) ^ k :=
      Polynomial.eval_eq_sum_range (t - x)
    _ = ∑ k ∈ Finset.range (p.natDegree + 1),
          (Polynomial.hasseDeriv k p).eval x * (t - x) ^ k := by
      simp only [Polynomial.natDegree_taylor, Polynomial.taylor_coeff]

private theorem volterraKernel_mul_sub_pow
    (n k : ℕ) (x t : ℝ) :
    ((x - t) ^ n / (n.factorial : ℝ)) * (t - x) ^ k =
      ((-1 : ℝ) ^ k * ((n + 1).ascFactorial k : ℝ)) *
        ((x - t) ^ (n + k) / ((n + k).factorial : ℝ)) := by
  have hfactorial :
      (n.factorial : ℝ) * ((n + 1).ascFactorial k : ℝ) =
        ((n + k).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_mul_ascFactorial n k
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hnk : ((n + k).factorial : ℝ) ≠ 0 := by positivity
  rw [show t - x = -(x - t) by ring, neg_pow, pow_add]
  calc
    ((x - t) ^ n / (n.factorial : ℝ)) *
        ((-1 : ℝ) ^ k * (x - t) ^ k) =
      ((-1 : ℝ) ^ k * (x - t) ^ n * (x - t) ^ k) /
        (n.factorial : ℝ) := by ring
    _ = ((-1 : ℝ) ^ k * ((n + 1).ascFactorial k : ℝ) *
          ((x - t) ^ n * (x - t) ^ k)) /
          ((n + k).factorial : ℝ) := by
      apply (div_eq_div_iff hn hnk).2
      rw [← hfactorial]
      ring
    _ = ((-1 : ℝ) ^ k * ((n + 1).ascFactorial k : ℝ)) *
        (((x - t) ^ n * (x - t) ^ k) /
          ((n + k).factorial : ℝ)) := by ring

private theorem volterraKernel_mul_polynomial_eq_sum
    (p : Polynomial ℝ) (n : ℕ) (x t : ℝ) :
    (x - t) ^ n / (n.factorial : ℝ) * p.eval t =
      ∑ k ∈ Finset.range (p.natDegree + 1),
        ((-1 : ℝ) ^ k * ((n + 1).ascFactorial k : ℝ) *
            (Polynomial.hasseDeriv k p).eval x) *
          ((x - t) ^ (n + k) / ((n + k).factorial : ℝ)) := by
  rw [polynomial_eval_eq_sum_hasse p x t, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    (x - t) ^ n / (n.factorial : ℝ) *
        ((Polynomial.hasseDeriv k p).eval x * (t - x) ^ k) =
      (Polynomial.hasseDeriv k p).eval x *
        ((x - t) ^ n / (n.factorial : ℝ) * (t - x) ^ k) := by ring
    _ = (Polynomial.hasseDeriv k p).eval x *
        (((-1 : ℝ) ^ k * ((n + 1).ascFactorial k : ℝ)) *
          ((x - t) ^ (n + k) / ((n + k).factorial : ℝ))) := by
      rw [volterraKernel_mul_sub_pow]
    _ = ((-1 : ℝ) ^ k * ((n + 1).ascFactorial k : ℝ) *
          (Polynomial.hasseDeriv k p).eval x) *
        ((x - t) ^ (n + k) / ((n + k).factorial : ℝ)) := by ring

/-- Moving multiplication by a polynomial through a normalized Volterra
integral produces a finite Hasse-derivative expansion:

`Vₙ(p · f; a, x) = ∑ₖ (-1)^k (n+1)^(overline k)
  (D^[k]p)(x) · V_(n+k)(f; a, x)`.

The weakest kernel naturally visible in the left side is the only one assumed
interval integrable.  This permits singular `f` whose order-`n` Volterra kernel
is nevertheless integrable.  The theorem is valid for every real polynomial,
every base point and endpoint, either interval orientation, and any real normed
space as codomain. -/
theorem volterraIntegral_polynomial_smul_of_kernel_intervalIntegrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Polynomial ℝ) (n : ℕ) (f : ℝ → E) (a x : ℝ)
    (hf : IntervalIntegrable
      (fun t => ((x - t) ^ n / (n.factorial : ℝ)) • f t) volume a x) :
    volterraIntegral n (fun t => p.eval t • f t) a x =
      ∑ k ∈ Finset.range (p.natDegree + 1),
        (((-1 : ℝ) ^ k * ((n + 1).ascFactorial k : ℝ) *
            (Polynomial.hasseDeriv k p).eval x) •
          volterraIntegral (n + k) f a x) := by
  classical
  unfold volterraIntegral
  let c : ℕ → ℝ := fun k =>
    (-1 : ℝ) ^ k * ((n + 1).ascFactorial k : ℝ) *
      (Polynomial.hasseDeriv k p).eval x
  let kernel : ℕ → ℝ → ℝ := fun m t =>
    (x - t) ^ m / (m.factorial : ℝ)
  have hkernelIntegrable (k : ℕ) :
      IntervalIntegrable (fun t => kernel (n + k) t • f t) volume a x := by
    have hscaled := hf.continuousOn_smul
      (show ContinuousOn
          (fun t : ℝ =>
            (n.factorial : ℝ) / ((n + k).factorial : ℝ) * (x - t) ^ k)
          (uIcc a x) by fun_prop)
    apply hscaled.congr
    intro t _
    change
      ((n.factorial : ℝ) / ((n + k).factorial : ℝ) * (x - t) ^ k) •
          (kernel n t • f t) = kernel (n + k) t • f t
    have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    have hnk : ((n + k).factorial : ℝ) ≠ 0 := by positivity
    have hscalar :
        ((n.factorial : ℝ) / ((n + k).factorial : ℝ) * (x - t) ^ k) *
            kernel n t = kernel (n + k) t := by
      dsimp only [kernel]
      rw [pow_add]
      field_simp [hn, hnk]
    calc
      ((n.factorial : ℝ) / ((n + k).factorial : ℝ) * (x - t) ^ k) •
          (kernel n t • f t) =
        (((n.factorial : ℝ) / ((n + k).factorial : ℝ) * (x - t) ^ k) *
          kernel n t) • f t := smul_smul _ _ _
      _ = kernel (n + k) t • f t := by rw [hscalar]
  calc
    (∫ t in a..x, kernel n t • (p.eval t • f t)) =
        ∫ t in a..x,
          ∑ k ∈ Finset.range (p.natDegree + 1),
            c k • (kernel (n + k) t • f t) := by
      apply intervalIntegral.integral_congr
      intro t _
      simp_rw [smul_smul]
      change (kernel n t * p.eval t) • f t =
        ∑ k ∈ Finset.range (p.natDegree + 1),
          (c k * kernel (n + k) t) • f t
      rw [volterraKernel_mul_polynomial_eq_sum p n x t,
        Finset.sum_smul]
    _ = ∑ k ∈ Finset.range (p.natDegree + 1),
          ∫ t in a..x, c k • (kernel (n + k) t • f t) := by
      apply intervalIntegral.integral_finsetSum
      intro k _
      exact (hkernelIntegrable k).continuousOn_smul continuousOn_const
    _ = ∑ k ∈ Finset.range (p.natDegree + 1),
          c k • ∫ t in a..x, kernel (n + k) t • f t := by
      apply Finset.sum_congr rfl
      intro k _
      exact (hkernelIntegrable k).integral_smul (c k)
    _ = ∑ k ∈ Finset.range (p.natDegree + 1),
          (((-1 : ℝ) ^ k * ((n + 1).ascFactorial k : ℝ) *
              (Polynomial.hasseDeriv k p).eval x) •
            ∫ t in a..x,
              ((x - t) ^ (n + k) / ((n + k).factorial : ℝ)) • f t) := by
      rfl

/-- If `f` itself is interval integrable, multiplication by a polynomial moves
through a normalized Volterra integral by the same finite Hasse-derivative
expansion. -/
theorem volterraIntegral_polynomial_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Polynomial ℝ) (n : ℕ) (f : ℝ → E) (a x : ℝ)
    (hf : IntervalIntegrable f volume a x) :
    volterraIntegral n (fun t => p.eval t • f t) a x =
      ∑ k ∈ Finset.range (p.natDegree + 1),
        (((-1 : ℝ) ^ k * ((n + 1).ascFactorial k : ℝ) *
            (Polynomial.hasseDeriv k p).eval x) •
          volterraIntegral (n + k) f a x) := by
  apply volterraIntegral_polynomial_smul_of_kernel_intervalIntegrable
  apply hf.continuousOn_smul
  fun_prop

/-- Monomial weights give the explicit finite commutator with binomial and
rising-factorial coefficients. -/
theorem volterraIntegral_pow_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p n : ℕ) (f : ℝ → E) (a x : ℝ)
    (hf : IntervalIntegrable f volume a x) :
    volterraIntegral n (fun t => t ^ p • f t) a x =
      ∑ k ∈ Finset.range (p + 1),
        (((-1 : ℝ) ^ k * ((n + 1).ascFactorial k : ℝ) *
            (p.choose k : ℝ) * x ^ (p - k)) •
          volterraIntegral (n + k) f a x) := by
  have hhasse (k : ℕ) :
      (Polynomial.hasseDeriv k (Polynomial.X ^ p : Polynomial ℝ)).eval x =
        (p.choose k : ℝ) * x ^ (p - k) := by
    rw [Polynomial.X_pow_eq_monomial, Polynomial.hasseDeriv_monomial,
      Polynomial.eval_monomial]
    norm_num
  have h := volterraIntegral_polynomial_smul
    (Polynomial.X ^ p) n f a x hf
  rw [Polynomial.natDegree_X_pow] at h
  simpa only [Polynomial.eval_pow, Polynomial.eval_X, hhasse, mul_assoc] using h

end Fabius
