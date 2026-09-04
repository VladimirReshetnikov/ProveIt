import FabiusFunction.Basic
import FabiusFunction.GeometricUniformMomentPolynomial
import FabiusFunction.FiniteQBinomialCore
import FabiusFunction.ScaledInfiniteProducts
import Mathlib.Algebra.Group.Ext
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Complex geometric-uniform moment product

For a strict complex contraction `q`, this file constructs the entire product

`A_q(z) = ∏' j, complexExpm1Div ((1 - q) * q^j * z)`

and identifies its Taylor coefficients with the recursively defined rational
moment polynomials.  The product is genuine: convergence is locally uniform
on the whole complex plane, and the coefficient bridge is proved through its
Mahler equation and iterated derivatives rather than by introducing a second
formal recurrence.

The strict condition `‖q‖ < 1` includes `q = 0` and excludes every nonzero
root of unity; in particular it excludes `q = 1`, where the displayed
normalization by `(1 - q)^n` would be singular.

## Main declarations

* `geometricUniformComplexMomentProduct`: the pointwise infinite product;
* `hasProdLocallyUniformly_geometricUniformComplexMomentProduct`: its locally
  uniform convergence for `‖q‖ < 1`;
* `differentiable_geometricUniformComplexMomentProduct`: its entire-ness;
* `geometricUniformMomentPolynomial_eval₂_eq_complexMomentProduct_taylorCoefficient`:
  the exact finite-q-Pochhammer normalization of its Taylor coefficient.
-/

set_option autoImplicit false

open Asymptotics Filter Finset Polynomial Set
open scoped BigOperators Topology

namespace Fabius

noncomputable section

private theorem complexExpm1Div_eq_dslope_exp :
    complexExpm1Div = dslope Complex.exp 0 := by
  funext z
  by_cases hz : z = 0
  · subst z
    simp [complexExpm1Div]
  · rw [complexExpm1Div_of_ne hz, dslope_of_ne _ hz, slope_def_field]
    simp

private theorem complexExpm1Div_differentiable :
    Differentiable ℂ complexExpm1Div := by
  rw [complexExpm1Div_eq_dslope_exp, ← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (s := Set.univ) (c := 0)
    (univ_mem : Set.univ ∈ nhds (0 : ℂ))).2
      Complex.differentiable_exp.differentiableOn

private theorem complexExpm1Div_sub_one_isBigO :
    (fun z : ℂ ↦ complexExpm1Div z - 1) =O[𝓝 0] (fun z : ℂ ↦ z) := by
  simpa only [complexExpm1Div_zero, sub_zero] using
    (complexExpm1Div_differentiable 0).isBigO_sub

private theorem complexExpm1Div_hasFPowerSeriesAt :
    HasFPowerSeriesAt complexExpm1Div
      (NormedSpace.expSeries ℂ ℂ).fslope 0 := by
  rw [complexExpm1Div_eq_dslope_exp]
  apply HasFPowerSeriesAt.has_fpower_series_dslope_fslope
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.exp_hasFPowerSeriesAt_zero

private theorem iteratedDeriv_complexExpm1Div_zero (n : ℕ) :
    iteratedDeriv n complexExpm1Div 0 = ((n + 1 : ℕ) : ℂ)⁻¹ := by
  have hcanonical :=
    complexExpm1Div_hasFPowerSeriesAt.analyticAt.hasFPowerSeriesAt
  have hseries :=
    complexExpm1Div_hasFPowerSeriesAt.eq_formalMultilinearSeries hcanonical
  have hcoeff := congrArg
    (fun p : FormalMultilinearSeries ℂ ℂ ℂ ↦ p.coeff n) hseries
  simp only [FormalMultilinearSeries.coeff_fslope,
    NormedSpace.expSeries_eq_ofScalars,
    FormalMultilinearSeries.coeff_ofScalars] at hcoeff
  have hnfac : ((n.factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast n.factorial_ne_zero
  have hsucc : (((n + 1).factorial : ℕ) : ℂ) =
      ((n + 1 : ℕ) : ℂ) * (n.factorial : ℂ) := by
    rw [Nat.factorial_succ]
    push_cast
    rfl
  rw [hsucc] at hcoeff
  field_simp [hnfac] at hcoeff ⊢
  simpa [mul_comm] using hcoeff.symm

private theorem summable_norm_complex_qpow (q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ ↦ ‖q ^ n‖ := by
  simpa only [norm_pow] using
    summable_geometric_of_lt_one (norm_nonneg q) hq

private theorem summable_norm_geometricUniformComplexMomentScale
    (q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ ↦ ‖(1 - q) * q ^ n‖ := by
  simpa only [norm_mul] using
    (summable_norm_complex_qpow q hq).mul_left ‖1 - q‖

/-- The complex geometric-uniform moment product.  The removable factor
`complexExpm1Div` makes the definition total at every individual zero
argument, including the contraction endpoint `q = 0`. -/
noncomputable def geometricUniformComplexMomentProduct (q z : ℂ) : ℂ :=
  ∏' j : ℕ, complexExpm1Div ((1 - q) * q ^ j * z)

/-- For every strict complex contraction, the defining product converges
locally uniformly on the whole complex plane to
`geometricUniformComplexMomentProduct q`. -/
theorem hasProdLocallyUniformly_geometricUniformComplexMomentProduct
    {q : ℂ} (hq : ‖q‖ < 1) :
    HasProdLocallyUniformly
      (fun j z ↦ complexExpm1Div ((1 - q) * q ^ j * z))
      (geometricUniformComplexMomentProduct q) := by
  have hprod := hasProdLocallyUniformly_scaled complexExpm1Div
      (fun j : ℕ ↦ (1 - q) * q ^ j)
      (summable_norm_geometricUniformComplexMomentScale q hq)
      complexExpm1Div_sub_one_isBigO
      complexExpm1Div_differentiable.continuous
  have hmonoid :
      NormedField.toNormedCommRing.toCommRing.toCommMonoid =
        Complex.commRing.toCommMonoid := by
    apply CommMonoid.ext
    rfl
  rw [hmonoid] at hprod
  change HasProdLocallyUniformly
    (fun j z ↦ complexExpm1Div ((1 - q) * q ^ j * z))
    (fun z ↦ ∏' j : ℕ, complexExpm1Div ((1 - q) * q ^ j * z))
  simpa only [smul_eq_mul] using hprod

/-- For every strict complex contraction, the geometric-uniform moment product
is entire. -/
theorem differentiable_geometricUniformComplexMomentProduct
    {q : ℂ} (hq : ‖q‖ < 1) :
    Differentiable ℂ (geometricUniformComplexMomentProduct q) := by
  change Differentiable ℂ
    (fun z ↦ ∏' j : ℕ, complexExpm1Div (((1 - q) * q ^ j) * z))
  simpa only [smul_eq_mul] using
    differentiable_tprod_scaled_of_eq_one complexExpm1Div
      (fun j : ℕ ↦ (1 - q) * q ^ j)
      (summable_norm_geometricUniformComplexMomentScale q hq)
      complexExpm1Div_differentiable complexExpm1Div_zero

set_option maxHeartbeats 600000 in
private theorem geometricUniformComplexMomentProduct_mahler
    (q z : ℂ) (hq : ‖q‖ < 1) :
    geometricUniformComplexMomentProduct q z =
      complexExpm1Div ((1 - q) * z) *
        geometricUniformComplexMomentProduct q (q * z) := by
  have harg :
      (fun n : ℕ ↦ complexExpm1Div ((1 - q) * q ^ (n + 1) * z)) =
        fun n : ℕ ↦ complexExpm1Div ((1 - q) * q ^ n * (q * z)) :=
    funext fun n ↦ by
      congr 1
      rw [pow_succ]
      ring
  have hmult :=
    ((hasProdLocallyUniformly_geometricUniformComplexMomentProduct hq).hasProd
      (x := q * z)).multipliable
  unfold geometricUniformComplexMomentProduct
  rw [tprod_eq_zero_mul' (harg ▸ hmult), harg, pow_zero, mul_one]

private theorem normalized_geometricUniformComplexMomentProduct_recurrence
    {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    (1 - q ^ n) *
        (iteratedDeriv n (geometricUniformComplexMomentProduct q) 0 /
          (n.factorial : ℂ)) =
      ∑ k ∈ range n,
        (1 - q) ^ (n - k) * q ^ k / ((n - k + 1).factorial : ℂ) *
          (iteratedDeriv k (geometricUniformComplexMomentProduct q) 0 /
            (k.factorial : ℂ)) := by
  let M : ℂ → ℂ := geometricUniformComplexMomentProduct q
  let D : ℂ → ℂ := fun z ↦ complexExpm1Div ((1 - q) * z)
  have hMcont (r : ℕ) : ContDiff ℂ r M :=
    (differentiable_geometricUniformComplexMomentProduct hq).contDiff
  have hDcont : ContDiffAt ℂ n D 0 := by
    have hlin : ContDiff ℂ n (fun z : ℂ ↦ (1 - q) * z) := by fun_prop
    exact (complexExpm1Div_differentiable.contDiff.comp hlin).contDiffAt
  have hcompcont : ContDiffAt ℂ n (fun z ↦ M (q * z)) 0 :=
    ((hMcont n).comp (contDiff_const.mul contDiff_id)).contDiffAt
  have hDderiv (r : ℕ) :
      iteratedDeriv r D 0 = (1 - q) ^ r / (r + 1) := by
    have h := congrFun
      (iteratedDeriv_comp_const_mul
        (complexExpm1Div_differentiable.contDiff : ContDiff ℂ r complexExpm1Div)
        (1 - q)) 0
    simp only [mul_zero, iteratedDeriv_complexExpm1Div_zero] at h
    simpa only [D, div_eq_mul_inv, Nat.cast_add, Nat.cast_one] using h
  have hscale (r : ℕ) :
      iteratedDeriv r (fun z ↦ M (q * z)) 0 =
        q ^ r * iteratedDeriv r M 0 := by
    simpa using congrFun (iteratedDeriv_comp_const_mul (hMcont r) q) 0
  have hfun : M = D * fun z ↦ M (q * z) := by
    funext z
    change M z = D z * M (q * z)
    simpa only [M, D] using
      geometricUniformComplexMomentProduct_mahler q z hq
  have hraw :
      iteratedDeriv n M 0 =
        ∑ i ∈ range (n + 1),
          (n.choose i : ℂ) * ((1 - q) ^ i / (i + 1)) *
            (q ^ (n - i) * iteratedDeriv (n - i) M 0) := by
    have hder := congrArg (fun f : ℂ → ℂ ↦ iteratedDeriv n f 0) hfun
    rw [iteratedDeriv_mul hDcont hcompcont] at hder
    rw [hder]
    apply sum_congr rfl
    intro i hi
    rw [hDderiv, hscale]
  have hraw' :
      iteratedDeriv n M 0 =
        ∑ k ∈ range (n + 1),
          (n.choose k : ℂ) * ((1 - q) ^ (n - k) / (n - k + 1)) *
            (q ^ k * iteratedDeriv k M 0) := by
    rw [← sum_range_reflect (fun i ↦
      (n.choose i : ℂ) * ((1 - q) ^ i / (i + 1)) *
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
      ((n.choose k : ℂ) * ((1 - q) ^ (n - k) / (n - k + 1)) *
          (q ^ k * iteratedDeriv k M 0)) / (n.factorial : ℂ) =
        (1 - q) ^ (n - k) * q ^ k /
            ((n - k + 1).factorial : ℂ) *
          (iteratedDeriv k M 0 / (k.factorial : ℂ)) := by
    have hkn : k ≤ n := by
      have := mem_range.mp hk
      omega
    have hden : (((n - k + 1 : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast (by omega : n - k + 1 ≠ 0)
    have hnfac : ((n.factorial : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast n.factorial_ne_zero
    have hkfac : ((k.factorial : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast k.factorial_ne_zero
    have hfac : (((n - k + 1).factorial : ℕ) : ℂ) =
        ((n - k + 1 : ℕ) : ℂ) * (((n - k).factorial : ℕ) : ℂ) := by
      rw [show n - k + 1 = (n - k).succ by omega, Nat.factorial_succ]
      push_cast
      rfl
    have hcast : ((n - k + 1 : ℕ) : ℂ) = (n : ℂ) - k + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hkn]
      push_cast
      ring
    have hden' : (n : ℂ) - k + 1 ≠ 0 := by
      rw [← hcast]
      exact hden
    rw [Nat.cast_choose ℂ hkn]
    rw [hfac, hcast]
    field_simp [hden', hnfac, hkfac]
  have hnormalized :
      iteratedDeriv n M 0 / (n.factorial : ℂ) =
        ∑ k ∈ range (n + 1),
          (1 - q) ^ (n - k) * q ^ k /
              ((n - k + 1).factorial : ℂ) *
            (iteratedDeriv k M 0 / (k.factorial : ℂ)) := by
    have hdiv := congrArg (fun x : ℂ ↦ x / (n.factorial : ℂ)) hraw'
    rw [sum_div] at hdiv
    rw [hdiv]
    apply sum_congr rfl
    intro k hk
    exact hterm k hk
  rw [sum_range_succ] at hnormalized
  simp only [Nat.sub_self, pow_zero, one_mul] at hnormalized
  change (1 - q ^ n) *
      (iteratedDeriv n M 0 / (n.factorial : ℂ)) = _
  linear_combination hnormalized

private theorem finiteQPochhammerIn_self_mul_complex_residual
    (q : ℂ) {k n : ℕ} (hkn : k ≤ n) :
    finiteQPochhammerIn q q k *
        (∏ j ∈ Ico (k + 1) (n + 1), (1 - q ^ j)) =
      finiteQPochhammerIn q q n := by
  unfold finiteQPochhammerIn
  rw [← Finset.prod_Ico_add' (fun j : ℕ ↦ 1 - q ^ j) k n 1]
  simpa only [pow_succ', mul_comm] using
    Finset.prod_range_mul_prod_Ico
      (fun j : ℕ ↦ 1 - q ^ (j + 1)) hkn

private theorem eval₂_geometricUniformMomentPolynomial_succ_complex
    (q : ℂ) (n : ℕ) :
    eval₂ (algebraMap ℚ ℂ) q (geometricUniformMomentPolynomial (n + 1)) =
      ∑ k ∈ range (n + 1),
        (((n - k + 2).factorial : ℂ)⁻¹) *
          (q ^ k *
            ((∏ j ∈ Ico (k + 1) (n + 1), (1 - q ^ j)) *
              eval₂ (algebraMap ℚ ℂ) q
                (geometricUniformMomentPolynomial k))) := by
  rw [geometricUniformMomentPolynomial_succ]
  simp only [eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_X_pow,
    eval₂_finsetProd, eval₂_sub, eval₂_one, map_inv₀, map_natCast]

private theorem geometricUniformMomentPolynomial_complex_bridge_summand
    (q a : ℂ) {k n : ℕ} (hkn : k ≤ n) (hq1 : 1 - q ≠ 0)
    (hk : eval₂ (algebraMap ℚ ℂ) q (geometricUniformMomentPolynomial k) =
      finiteQPochhammerIn q q k / (1 - q) ^ k * a) :
    (((n - k + 2).factorial : ℂ)⁻¹) *
          (q ^ k *
            ((∏ j ∈ Ico (k + 1) (n + 1), (1 - q ^ j)) *
              eval₂ (algebraMap ℚ ℂ) q
                (geometricUniformMomentPolynomial k))) =
      finiteQPochhammerIn q q n / (1 - q) ^ (n + 1) *
        ((1 - q) ^ (n + 1 - k) * q ^ k /
          ((n + 1 - k + 1).factorial : ℂ) * a) := by
  have hres :
      (∏ j ∈ Ico (k + 1) (n + 1), (1 - q ^ j)) *
          finiteQPochhammerIn q q k = finiteQPochhammerIn q q n := by
    rw [mul_comm]
    exact finiteQPochhammerIn_self_mul_complex_residual q hkn
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

/-- For `‖q‖ < 1`, evaluation of the recursive moment polynomial is
exactly the finite-q-Pochhammer normalization of the Taylor coefficient of
the genuine locally-uniform complex product.  The statement includes
`q = 0`; no formal recurrence surrogate appears on the analytic side. -/
theorem geometricUniformMomentPolynomial_eval₂_eq_complexMomentProduct_taylorCoefficient
    {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    eval₂ (algebraMap ℚ ℂ) q (geometricUniformMomentPolynomial n) =
      finiteQPochhammerIn q q n / (1 - q) ^ n *
        (iteratedDeriv n (geometricUniformComplexMomentProduct q) 0 /
          (n.factorial : ℂ)) := by
  have hq1 : 1 - q ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    subst q
    simp at hq
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simp [geometricUniformComplexMomentProduct]
      | succ n =>
          rw [eval₂_geometricUniformMomentPolynomial_succ_complex]
          let A : ℕ → ℂ := fun r ↦
            iteratedDeriv r (geometricUniformComplexMomentProduct q) 0 /
              (r.factorial : ℂ)
          change
            (∑ k ∈ range (n + 1),
              (((n - k + 2).factorial : ℂ)⁻¹) *
                (q ^ k *
                  ((∏ j ∈ Ico (k + 1) (n + 1), (1 - q ^ j)) *
                    eval₂ (algebraMap ℚ ℂ) q
                      (geometricUniformMomentPolynomial k)))) =
              finiteQPochhammerIn q q (n + 1) / (1 - q) ^ (n + 1) *
                A (n + 1)
          have hrec :=
            normalized_geometricUniformComplexMomentProduct_recurrence hq (n + 1)
          change
            (1 - q ^ (n + 1)) * A (n + 1) =
              ∑ k ∈ range (n + 1),
                (1 - q) ^ (n + 1 - k) * q ^ k /
                    ((n + 1 - k + 1).factorial : ℂ) * A k at hrec
          calc
            (∑ k ∈ range (n + 1),
                (((n - k + 2).factorial : ℂ)⁻¹) *
                  (q ^ k *
                    ((∏ j ∈ Ico (k + 1) (n + 1), (1 - q ^ j)) *
                      eval₂ (algebraMap ℚ ℂ) q
                        (geometricUniformMomentPolynomial k)))) =
              ∑ k ∈ range (n + 1),
                finiteQPochhammerIn q q n / (1 - q) ^ (n + 1) *
                  ((1 - q) ^ (n + 1 - k) * q ^ k /
                    ((n + 1 - k + 1).factorial : ℂ) * A k) := by
                apply sum_congr rfl
                intro k hk
                have hklt : k < n + 1 := mem_range.mp hk
                have hkle : k ≤ n := by omega
                exact geometricUniformMomentPolynomial_complex_bridge_summand
                  q (A k) hkle hq1 (by
                    simpa only [A] using ih k hklt)
            _ = finiteQPochhammerIn q q n / (1 - q) ^ (n + 1) *
                  ∑ k ∈ range (n + 1),
                    (1 - q) ^ (n + 1 - k) * q ^ k /
                      ((n + 1 - k + 1).factorial : ℂ) * A k := by
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
