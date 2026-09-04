import FabiusFunction.GeometricUniformDictionary
import FabiusFunction.GeometricUniformMomentPolynomial
import FabiusFunction.FiniteQBinomialCore
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Analytic bridge for geometric-uniform moment polynomials

This file identifies the recursively defined rational polynomial
`geometricUniformMomentPolynomial n` with the normalized Taylor coefficient
of the genuine geometric-uniform moment generating function.  The parameter
range `|q| < 1` includes the uniform endpoint `q = 0`, negative contractions,
and the whole compactly supported probability-law regime.

The result is deliberately stated through the actual MGF and its iterated
derivative, rather than through a second sequence satisfying the same
recurrence.  It does not construct the manuscript's complex-parameter
infinite product.

## Main declaration

* `geometricUniformMomentPolynomial_eval₂_eq_mgf_taylorCoefficient`: evaluation
  of the polynomial is the finite-q-Pochhammer normalization of the MGF
  Taylor coefficient.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset MeasureTheory Polynomial ProbabilityTheory Real Set
open intervalIntegral

namespace Fabius

open ProbabilityRepresentation

noncomputable section

private theorem ae_geometricUniformDistribution_mem_range
    {q : ℝ} (hq : |q| < 1) :
    ∀ᵐ x ∂(geometricUniformDistribution q),
      x ∈ Set.range (geometricUniformSeries q) := by
  rw [← geometricUniformDistribution_support_eq_range hq]
  exact Measure.support_mem_ae

private theorem geometricUniformDistribution_integrableExpSet
    {q : ℝ} (hq : |q| < 1) :
    integrableExpSet id (geometricUniformDistribution q) = Set.univ := by
  letI := geometricUniformDistribution_isProbabilityMeasure hq
  let K : Set ℝ := Set.range (geometricUniformSeries q)
  have hK : IsCompact K := isCompact_range (continuous_geometricUniformSeries hq)
  ext t
  simp only [Set.mem_univ, iff_true]
  unfold integrableExpSet
  rw [← Measure.restrict_eq_self_of_ae_mem
    (ae_geometricUniformDistribution_mem_range hq)]
  exact (by fun_prop : Continuous fun x : ℝ =>
    Real.exp (t * id x)).continuousOn.integrableOn_compact hK

private theorem geometricUniformDigit_integrableExpSet (q : ℝ) :
    integrableExpSet id (geometricUniformDigit q) = Set.univ := by
  ext t
  simp only [Set.mem_univ, iff_true]
  unfold integrableExpSet geometricUniformDigit
  refine (integrable_map_measure (by fun_prop) (by fun_prop)).2 ?_
  rw [← integrableOn_univ]
  exact (by fun_prop : Continuous fun u : Set.Icc (0 : ℝ) 1 =>
    Real.exp (t * ((1 - q) * (u : ℝ)))).continuousOn.integrableOn_compact isCompact_univ

private theorem moment_geometricUniformDigit (q : ℝ) (n : ℕ) :
    ProbabilityTheory.moment id n (geometricUniformDigit q) =
      (1 - q) ^ n / (n + 1) := by
  unfold ProbabilityTheory.moment geometricUniformDigit
  rw [MeasureTheory.integral_map (by fun_prop) (by fun_prop)]
  change (∫ u : Set.Icc (0 : ℝ) 1, ((1 - q) * (u : ℝ)) ^ n) = _
  simp_rw [mul_pow]
  rw [MeasureTheory.integral_const_mul]
  have hint :
      (∫ a : Set.Icc (0 : ℝ) 1, (a : ℝ) ^ n) =
        ∫ x in Set.Icc (0 : ℝ) 1, x ^ n :=
    MeasureTheory.integral_subtype_comap measurableSet_Icc (fun x : ℝ => x ^ n)
  rw [hint]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_pow]
  norm_num [div_eq_mul_inv]

private theorem normalizedMoment_geometricUniformDistribution_recurrence
    {q : ℝ} (hq : |q| < 1) (n : ℕ) :
    (1 - q ^ n) *
        (iteratedDeriv n (mgf id (geometricUniformDistribution q)) 0 /
          (n.factorial : ℝ)) =
      ∑ k ∈ range n,
        (1 - q) ^ (n - k) * q ^ k / ((n - k + 1).factorial : ℝ) *
          (iteratedDeriv k (mgf id (geometricUniformDistribution q)) 0 /
            (k.factorial : ℝ)) := by
  let M : ℝ → ℝ := mgf id (geometricUniformDistribution q)
  let D : ℝ → ℝ := mgf id (geometricUniformDigit q)
  have hMset := geometricUniformDistribution_integrableExpSet hq
  have hDset := geometricUniformDigit_integrableExpSet q
  have hMcont (r : ℕ) : ContDiff ℝ r M := by
    rw [contDiff_iff_contDiffAt]
    intro t
    exact (analyticAt_mgf (by simp [hMset])).contDiffAt.of_le (by
      exact WithTop.coe_le_coe.mpr le_top)
  have hDcont : ContDiffAt ℝ n D 0 :=
    (analyticAt_mgf (by simp [hDset])).contDiffAt.of_le (by
      exact WithTop.coe_le_coe.mpr le_top)
  have hcompcont : ContDiffAt ℝ n (fun t => M (q * t)) 0 :=
    ((hMcont n).comp (contDiff_const.mul contDiff_id)).contDiffAt
  have hDderiv (r : ℕ) :
      iteratedDeriv r D 0 = (1 - q) ^ r / (r + 1) := by
    rw [show D = mgf id (geometricUniformDigit q) from rfl,
      iteratedDeriv_mgf_zero (by simp [hDset])]
    simpa only [ProbabilityTheory.moment] using moment_geometricUniformDigit q r
  have hscale (r : ℕ) :
      iteratedDeriv r (fun t => M (q * t)) 0 =
        q ^ r * iteratedDeriv r M 0 := by
    simpa using congrFun (iteratedDeriv_comp_const_mul (hMcont r) q) 0
  have hfun : M = D * fun t => M (q * t) := by
    funext t
    change M t = D t * M (q * t)
    have h := ((geometric_tail_dictionary_geometricUniform hq 1).2.2.1 t)
    simpa only [M, D, prod_range_succ, prod_range_zero, pow_zero,
      pow_one, one_mul] using h
  have hraw :
      iteratedDeriv n M 0 =
        ∑ i ∈ range (n + 1),
          (n.choose i : ℝ) * ((1 - q) ^ i / (i + 1)) *
            (q ^ (n - i) * iteratedDeriv (n - i) M 0) := by
    have hder := congrArg (fun f : ℝ → ℝ => iteratedDeriv n f 0) hfun
    rw [iteratedDeriv_mul hDcont hcompcont] at hder
    rw [hder]
    apply sum_congr rfl
    intro i hi
    rw [hDderiv, hscale]
  have hraw' :
      iteratedDeriv n M 0 =
        ∑ k ∈ range (n + 1),
          (n.choose k : ℝ) * ((1 - q) ^ (n - k) / (n - k + 1)) *
            (q ^ k * iteratedDeriv k M 0) := by
    rw [← sum_range_reflect (fun i =>
      (n.choose i : ℝ) * ((1 - q) ^ i / (i + 1)) *
        (q ^ (n - i) * iteratedDeriv (n - i) M 0)) (n + 1)] at hraw
    rw [hraw]
    apply sum_congr rfl
    intro k hk
    have hkn : k ≤ n := by
      have := mem_range.mp hk
      omega
    have hindex : n + 1 - 1 - k = n - k := by omega
    rw [hindex, Nat.choose_symm hkn, Nat.sub_sub_self hkn,
      Nat.cast_sub hkn]
  have hterm (k : ℕ) (hk : k ∈ range (n + 1)) :
      ((n.choose k : ℝ) * ((1 - q) ^ (n - k) / (n - k + 1)) *
          (q ^ k * iteratedDeriv k M 0)) / (n.factorial : ℝ) =
        (1 - q) ^ (n - k) * q ^ k /
            ((n - k + 1).factorial : ℝ) *
          (iteratedDeriv k M 0 / (k.factorial : ℝ)) := by
    have hkn : k ≤ n := by
      have := mem_range.mp hk
      omega
    have hden : (((n - k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hfac : (((n - k + 1).factorial : ℕ) : ℝ) =
        ((n - k + 1 : ℕ) : ℝ) * (((n - k).factorial : ℕ) : ℝ) := by
      rw [show n - k + 1 = (n - k).succ by omega, Nat.factorial_succ]
      push_cast
      rfl
    have hcast : ((n - k + 1 : ℕ) : ℝ) = (n : ℝ) - k + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hkn]
      push_cast
      ring
    have hden' : ((n : ℝ) - k + 1) ≠ 0 := by
      rw [← hcast]
      exact hden
    rw [Nat.cast_choose ℝ hkn]
    rw [hfac, hcast]
    field_simp [hden']
  have hnormalized :
      iteratedDeriv n M 0 / (n.factorial : ℝ) =
        ∑ k ∈ range (n + 1),
          (1 - q) ^ (n - k) * q ^ k /
              ((n - k + 1).factorial : ℝ) *
            (iteratedDeriv k M 0 / (k.factorial : ℝ)) := by
    have hdiv := congrArg (fun x : ℝ => x / (n.factorial : ℝ)) hraw'
    rw [sum_div] at hdiv
    rw [hdiv]
    apply sum_congr rfl
    intro k hk
    exact hterm k hk
  rw [sum_range_succ] at hnormalized
  simp only [Nat.sub_self, pow_zero, one_mul] at hnormalized
  change (1 - q ^ n) *
      (iteratedDeriv n M 0 / (n.factorial : ℝ)) = _
  linear_combination hnormalized

private theorem finiteQPochhammerIn_self_mul_residual
    (q : ℝ) {k n : ℕ} (hkn : k ≤ n) :
    finiteQPochhammerIn q q k *
        (∏ j ∈ Ico (k + 1) (n + 1), (1 - q ^ j)) =
      finiteQPochhammerIn q q n := by
  unfold finiteQPochhammerIn
  rw [← Finset.prod_Ico_add' (fun j : ℕ => 1 - q ^ j) k n 1]
  simpa only [pow_succ', mul_comm] using
    Finset.prod_range_mul_prod_Ico
      (fun j : ℕ => 1 - q ^ (j + 1)) hkn

private theorem eval₂_geometricUniformMomentPolynomial_succ (q : ℝ) (n : ℕ) :
    eval₂ (algebraMap ℚ ℝ) q (geometricUniformMomentPolynomial (n + 1)) =
      ∑ k ∈ range (n + 1),
        (((n - k + 2).factorial : ℝ)⁻¹) *
          (q ^ k *
            ((∏ j ∈ Ico (k + 1) (n + 1), (1 - q ^ j)) *
              eval₂ (algebraMap ℚ ℝ) q (geometricUniformMomentPolynomial k))) := by
  rw [geometricUniformMomentPolynomial_succ]
  simp only [eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_X_pow,
    eval₂_finsetProd, eval₂_sub, eval₂_one, map_inv₀, map_natCast]

private theorem geometricUniformMomentPolynomial_bridge_summand
    (q a : ℝ) {k n : ℕ} (hkn : k ≤ n) (hq1 : 1 - q ≠ 0)
    (hk : eval₂ (algebraMap ℚ ℝ) q (geometricUniformMomentPolynomial k) =
      finiteQPochhammerIn q q k / (1 - q) ^ k * a) :
    (((n - k + 2).factorial : ℝ)⁻¹) *
          (q ^ k *
            ((∏ j ∈ Ico (k + 1) (n + 1), (1 - q ^ j)) *
              eval₂ (algebraMap ℚ ℝ) q (geometricUniformMomentPolynomial k))) =
      finiteQPochhammerIn q q n / (1 - q) ^ (n + 1) *
        ((1 - q) ^ (n + 1 - k) * q ^ k /
          ((n + 1 - k + 1).factorial : ℝ) * a) := by
  have hres :
      (∏ j ∈ Ico (k + 1) (n + 1), (1 - q ^ j)) *
          finiteQPochhammerIn q q k = finiteQPochhammerIn q q n := by
    rw [mul_comm]
    exact finiteQPochhammerIn_self_mul_residual q hkn
  have hinner :
      (∏ j ∈ Ico (k + 1) (n + 1), (1 - q ^ j)) *
          (finiteQPochhammerIn q q k / (1 - q) ^ k * a) =
        finiteQPochhammerIn q q n / (1 - q) ^ k * a := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc
      (∏ j ∈ Ico (k + 1) (n + 1), (1 - q ^ j)) *
            (finiteQPochhammerIn q q k * ((1 - q) ^ k)⁻¹ * a) =
          ((∏ j ∈ Ico (k + 1) (n + 1), (1 - q ^ j)) *
              finiteQPochhammerIn q q k) * ((1 - q) ^ k)⁻¹ * a := by ring
      _ = finiteQPochhammerIn q q n * ((1 - q) ^ k)⁻¹ * a := by rw [hres]
  rw [hk, hinner]
  have hpow : (1 - q) ^ (n + 1) =
      (1 - q) ^ k * (1 - q) ^ (n + 1 - k) := by
    rw [← pow_add]
    congr 1
    omega
  have hfac : n - k + 2 = n + 1 - k + 1 := by omega
  rw [hfac, hpow]
  field_simp [hq1]

/-- For `|q| < 1`, evaluating the recursive moment polynomial gives
exactly the finite-q-Pochhammer normalization of the Taylor coefficient of
the genuine geometric-uniform MGF.  In particular, the statement includes
the regular case `q = 0`; no independently defined recurrence
surrogate appears on the analytic side. -/
theorem geometricUniformMomentPolynomial_eval₂_eq_mgf_taylorCoefficient
    {q : ℝ} (hq : |q| < 1) (n : ℕ) :
    eval₂ (algebraMap ℚ ℝ) q (geometricUniformMomentPolynomial n) =
      finiteQPochhammerIn q q n / (1 - q) ^ n *
        (iteratedDeriv n (mgf id (geometricUniformDistribution q)) 0 /
          (n.factorial : ℝ)) := by
  have hq1 : 1 - q ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_gt (abs_lt.mp hq).2)
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          letI := geometricUniformDistribution_isProbabilityMeasure hq
          simp
      | succ n =>
          rw [eval₂_geometricUniformMomentPolynomial_succ]
          let A : ℕ → ℝ := fun r =>
            iteratedDeriv r (mgf id (geometricUniformDistribution q)) 0 /
              (r.factorial : ℝ)
          change
            (∑ k ∈ range (n + 1),
              (((n - k + 2).factorial : ℝ)⁻¹) *
                (q ^ k *
                  ((∏ j ∈ Ico (k + 1) (n + 1), (1 - q ^ j)) *
                    eval₂ (algebraMap ℚ ℝ) q
                      (geometricUniformMomentPolynomial k)))) =
              finiteQPochhammerIn q q (n + 1) / (1 - q) ^ (n + 1) * A (n + 1)
          have hrec :=
            normalizedMoment_geometricUniformDistribution_recurrence hq (n + 1)
          change
            (1 - q ^ (n + 1)) * A (n + 1) =
              ∑ k ∈ range (n + 1),
                (1 - q) ^ (n + 1 - k) * q ^ k /
                    ((n + 1 - k + 1).factorial : ℝ) * A k at hrec
          calc
            (∑ k ∈ range (n + 1),
                (((n - k + 2).factorial : ℝ)⁻¹) *
                  (q ^ k *
                    ((∏ j ∈ Ico (k + 1) (n + 1), (1 - q ^ j)) *
                      eval₂ (algebraMap ℚ ℝ) q
                        (geometricUniformMomentPolynomial k)))) =
              ∑ k ∈ range (n + 1),
                finiteQPochhammerIn q q n / (1 - q) ^ (n + 1) *
                  ((1 - q) ^ (n + 1 - k) * q ^ k /
                    ((n + 1 - k + 1).factorial : ℝ) * A k) := by
                apply sum_congr rfl
                intro k hk
                have hklt : k < n + 1 := mem_range.mp hk
                have hkle : k ≤ n := by omega
                exact geometricUniformMomentPolynomial_bridge_summand
                  q (A k) hkle hq1 (by
                    simpa only [A] using ih k hklt)
            _ = finiteQPochhammerIn q q n / (1 - q) ^ (n + 1) *
                  ∑ k ∈ range (n + 1),
                    (1 - q) ^ (n + 1 - k) * q ^ k /
                      ((n + 1 - k + 1).factorial : ℝ) * A k := by
                rw [mul_sum]
            _ = finiteQPochhammerIn q q n / (1 - q) ^ (n + 1) *
                  ((1 - q ^ (n + 1)) * A (n + 1)) := by rw [← hrec]
            _ = finiteQPochhammerIn q q (n + 1) / (1 - q) ^ (n + 1) *
                  A (n + 1) := by
                rw [finiteQPochhammerIn_succ]
                rw [show q * q ^ n = q ^ (n + 1) by ring]
                ring

end

end Fabius
