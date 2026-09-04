import FabiusFunction.GeometricUniformComplexMomentProduct

/-!
# Exterior complex geometric-uniform moment germ

For `1 < ‖q‖`, the geometric-uniform series no longer defines a probability
law.  The manuscript instead uses the reciprocal germ

`M_q(z) = (A_{q⁻¹}(-z))⁻¹`,

where `A_r` is the genuine locally-uniform complex product at the strict
contraction `r = q⁻¹`.  This file defines that same object, proves that it is
analytic at the origin, and identifies its Taylor coefficients with the
already constructed rational moment polynomials.

The inverse is a total Lean function, but only its analytic germ at zero is
claimed here.  No global holomorphy across its poles, pole divisor, boundary
case `‖q‖ = 1`, or rational-function continuation in the parameter is asserted.

## Main declarations

* `geometricUniformExteriorComplexMomentGerm`: the reciprocal exterior germ;
* `analyticAt_geometricUniformExteriorComplexMomentGerm`: analyticity at zero;
* `geometricUniformMomentPolynomial_eval₂_eq_exteriorComplexMomentGerm_taylorCoefficient`:
  the exact finite-q-Pochhammer normalization of its Taylor coefficient.
-/

set_option autoImplicit false

open Asymptotics Filter Finset Polynomial Set
open scoped BigOperators Topology

namespace Fabius

noncomputable section

private theorem exterior_complexExpm1Div_eq_dslope_exp :
    complexExpm1Div = dslope Complex.exp 0 := by
  funext z
  by_cases hz : z = 0
  · subst z
    simp [complexExpm1Div]
  · rw [complexExpm1Div_of_ne hz, dslope_of_ne _ hz, slope_def_field]
    simp

private theorem exterior_complexExpm1Div_differentiable :
    Differentiable ℂ complexExpm1Div := by
  rw [exterior_complexExpm1Div_eq_dslope_exp, ← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (s := Set.univ) (c := 0)
    (univ_mem : Set.univ ∈ nhds (0 : ℂ))).2
      Complex.differentiable_exp.differentiableOn

private theorem exterior_complexExpm1Div_hasFPowerSeriesAt :
    HasFPowerSeriesAt complexExpm1Div
      (NormedSpace.expSeries ℂ ℂ).fslope 0 := by
  rw [exterior_complexExpm1Div_eq_dslope_exp]
  apply HasFPowerSeriesAt.has_fpower_series_dslope_fslope
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.exp_hasFPowerSeriesAt_zero

private theorem exterior_iteratedDeriv_complexExpm1Div_zero (n : ℕ) :
    iteratedDeriv n complexExpm1Div 0 = ((n + 1 : ℕ) : ℂ)⁻¹ := by
  have hcanonical :=
    exterior_complexExpm1Div_hasFPowerSeriesAt.analyticAt.hasFPowerSeriesAt
  have hseries :=
    exterior_complexExpm1Div_hasFPowerSeriesAt.eq_formalMultilinearSeries hcanonical
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

/-- The exterior reciprocal complex moment germ.

For `1 < ‖q‖`, the parameter `q⁻¹` is a strict contraction, and reindexing
the product shows that this is exactly
`[∏' j ≥ 1, complexExpm1Div ((1 - q) * q⁻ʲ * z)]⁻¹`.
The total inverse supplies values at poles only to make a total Lean function;
the analytic assertion below is local at the origin. -/
noncomputable def geometricUniformExteriorComplexMomentGerm (q z : ℂ) : ℂ :=
  (geometricUniformComplexMomentProduct q⁻¹ (-z))⁻¹

/-- For an exterior parameter `1 < ‖q‖`, the reciprocal product is analytic
at the origin. -/
theorem analyticAt_geometricUniformExteriorComplexMomentGerm
    {q : ℂ} (hq : 1 < ‖q‖) :
    AnalyticAt ℂ (geometricUniformExteriorComplexMomentGerm q) 0 := by
  have hq0 : q ≠ 0 := by
    exact norm_ne_zero_iff.mp (ne_of_gt (lt_trans zero_lt_one hq))
  have hqi : ‖q⁻¹‖ < 1 := by
    rw [norm_inv, inv_lt_one_iff₀]
    exact Or.inr hq
  have hdiff : Differentiable ℂ
      (fun z ↦ geometricUniformComplexMomentProduct q⁻¹ (-z)) :=
    (differentiable_geometricUniformComplexMomentProduct hqi).comp
      (by fun_prop)
  have hzero : geometricUniformComplexMomentProduct q⁻¹ (-(0 : ℂ)) ≠ 0 := by
    simp [geometricUniformComplexMomentProduct]
  change AnalyticAt ℂ
    (fun z ↦ (geometricUniformComplexMomentProduct q⁻¹ (-z))⁻¹) 0
  exact (hdiff.analyticAt 0).inv hzero

private theorem exterior_innerProduct_mahler
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

private theorem normalized_exteriorComplexMomentGerm_recurrence
    {q : ℂ} (hq : 1 < ‖q‖) (n : ℕ) :
    (1 - q ^ n) *
        (iteratedDeriv n (geometricUniformExteriorComplexMomentGerm q) 0 /
          (n.factorial : ℂ)) =
      ∑ k ∈ range n,
        (1 - q) ^ (n - k) * q ^ k / ((n - k + 1).factorial : ℂ) *
          (iteratedDeriv k (geometricUniformExteriorComplexMomentGerm q) 0 /
            (k.factorial : ℂ)) := by
  have hq0 : q ≠ 0 := by
    exact norm_ne_zero_iff.mp (ne_of_gt (lt_trans zero_lt_one hq))
  let r : ℂ := q⁻¹
  have hr : ‖r‖ < 1 := by
    simp only [r, norm_inv]
    rw [inv_lt_one_iff₀]
    exact Or.inr hq
  let D : ℂ → ℂ := fun z ↦ geometricUniformComplexMomentProduct r (-z)
  let M : ℂ → ℂ := geometricUniformExteriorComplexMomentGerm q
  let L : ℂ → ℂ := fun z ↦ complexExpm1Div ((r - 1) * z)
  have hDdiff : Differentiable ℂ D := by
    exact (differentiable_geometricUniformComplexMomentProduct hr).comp
      (by fun_prop)
  have hDzero : D 0 = 1 := by
    simp [D, geometricUniformComplexMomentProduct]
  let s : Set ℂ := {z | D z ≠ 0}
  have hsopen : IsOpen s := by
    exact isOpen_ne_fun hDdiff.continuous continuous_const
  have hzeros : 0 ∈ s := by
    simpa only [s, Set.mem_setOf_eq, hDzero] using one_ne_zero
  have hM_eq (z : ℂ) : M z = (D z)⁻¹ := by
    rfl
  have hdenominator (z : ℂ) :
      D z = L z * D (r * z) := by
    change geometricUniformComplexMomentProduct r (-z) =
      complexExpm1Div ((r - 1) * z) *
        geometricUniformComplexMomentProduct r (-(r * z))
    convert exterior_innerProduct_mahler r (-z) hr using 1
    all_goals ring_nf
  have hrs : MapsTo (fun z : ℂ ↦ r * z) s s := by
    intro z hz
    change D (r * z) ≠ 0
    intro hzero
    apply hz
    rw [hdenominator z, hzero, mul_zero]
  have hManalytic (z : ℂ) (hz : z ∈ s) : AnalyticAt ℂ M z := by
    change AnalyticAt ℂ (fun w ↦ (D w)⁻¹) z
    exact (hDdiff.analyticAt z).inv hz
  have hMcontOn (m : ℕ) : ContDiffOn ℂ m M s := by
    intro z hz
    exact (hManalytic z hz).contDiffAt.contDiffWithinAt
  have hMcont (m : ℕ) : ContDiffAt ℂ m M 0 :=
    (hManalytic 0 hzeros).contDiffAt
  have hLcont : ContDiffAt ℂ n L 0 := by
    have hlin : ContDiff ℂ n (fun z : ℂ ↦ (r - 1) * z) := by fun_prop
    exact (exterior_complexExpm1Div_differentiable.contDiff.comp hlin).contDiffAt
  have hLderiv (m : ℕ) :
      iteratedDeriv m L 0 = (r - 1) ^ m / (m + 1) := by
    have h := congrFun
      (iteratedDeriv_comp_const_mul
        (exterior_complexExpm1Div_differentiable.contDiff :
          ContDiff ℂ m complexExpm1Div) (r - 1)) 0
    simp only [mul_zero, exterior_iteratedDeriv_complexExpm1Div_zero] at h
    simpa only [L, div_eq_mul_inv, Nat.cast_add, Nat.cast_one] using h
  have hscale (m : ℕ) :
      iteratedDeriv m (fun z ↦ M (r * z)) 0 =
        r ^ m * iteratedDeriv m M 0 := by
    have hwithin := iteratedDerivWithin_comp_const_smul
      (n := m) hzeros hsopen.uniqueDiffOn (hMcontOn m) r hrs
    simp only [mul_zero, smul_eq_mul] at hwithin
    rw [iteratedDerivWithin_of_isOpen hsopen hzeros,
      iteratedDerivWithin_of_isOpen hsopen hzeros] at hwithin
    exact hwithin
  have hlocal :
      (fun z ↦ M (r * z)) =ᶠ[𝓝 0] (fun z ↦ L z * M z) := by
    filter_upwards [hsopen.mem_nhds hzeros] with z hz
    have hprod : L z * D (r * z) ≠ 0 := by
      rw [← hdenominator z]
      exact hz
    have hLzero : L z ≠ 0 := left_ne_zero_of_mul hprod
    have hDrzero : D (r * z) ≠ 0 := right_ne_zero_of_mul hprod
    rw [hM_eq, hM_eq, hdenominator z]
    field_simp [hLzero, hDrzero]
  have hraw :
      r ^ n * iteratedDeriv n M 0 =
        ∑ i ∈ range (n + 1),
          (n.choose i : ℂ) * ((r - 1) ^ i / (i + 1)) *
            iteratedDeriv (n - i) M 0 := by
    have hder := hlocal.iteratedDeriv_eq n
    change iteratedDeriv n (fun z ↦ M (r * z)) 0 =
      iteratedDeriv n (L * M) 0 at hder
    rw [iteratedDeriv_mul hLcont (hMcont n)] at hder
    rw [hscale n] at hder
    rw [hder]
    apply sum_congr rfl
    intro i hi
    rw [hLderiv]
  have hraw' :
      r ^ n * iteratedDeriv n M 0 =
        ∑ k ∈ range (n + 1),
          (n.choose k : ℂ) * ((r - 1) ^ (n - k) / (n - k + 1)) *
            iteratedDeriv k M 0 := by
    rw [← sum_range_reflect (fun i ↦
      (n.choose i : ℂ) * ((r - 1) ^ i / (i + 1)) *
        iteratedDeriv (n - i) M 0) (n + 1)] at hraw
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
      ((n.choose k : ℂ) * ((r - 1) ^ (n - k) / (n - k + 1)) *
          iteratedDeriv k M 0) / (n.factorial : ℂ) =
        (r - 1) ^ (n - k) / ((n - k + 1).factorial : ℂ) *
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
  let B : ℕ → ℂ := fun m ↦ iteratedDeriv m M 0 / (m.factorial : ℂ)
  have hnormalized :
      r ^ n * B n =
        ∑ k ∈ range (n + 1),
          (r - 1) ^ (n - k) / ((n - k + 1).factorial : ℂ) * B k := by
    have hdiv := congrArg (fun x : ℂ ↦ x / (n.factorial : ℂ)) hraw'
    rw [sum_div] at hdiv
    calc
      r ^ n * B n = (r ^ n * iteratedDeriv n M 0) / (n.factorial : ℂ) := by
        simp only [B]
        ring
      _ = ∑ k ∈ range (n + 1),
          ((n.choose k : ℂ) * ((r - 1) ^ (n - k) / (n - k + 1)) *
            iteratedDeriv k M 0) / (n.factorial : ℂ) := hdiv
      _ = ∑ k ∈ range (n + 1),
          (r - 1) ^ (n - k) / ((n - k + 1).factorial : ℂ) * B k := by
        apply sum_congr rfl
        intro k hk
        simpa only [B] using hterm k hk
  have hreciprocal :
      (r ^ n - 1) * B n =
        ∑ k ∈ range n,
          (r - 1) ^ (n - k) / ((n - k + 1).factorial : ℂ) * B k := by
    rw [sum_range_succ] at hnormalized
    simp only [Nat.sub_self, pow_zero] at hnormalized
    linear_combination hnormalized
  have hqri : q * (r - 1) = 1 - q := by
    simp only [r]
    field_simp [hq0]
  have hleft : q ^ n * (r ^ n - 1) = 1 - q ^ n := by
    calc
      q ^ n * (r ^ n - 1) = (q * r) ^ n - q ^ n := by
        rw [mul_sub, mul_one, mul_pow]
      _ = 1 - q ^ n := by simp [r, hq0]
  change (1 - q ^ n) * B n = _
  calc
    (1 - q ^ n) * B n = q ^ n * ((r ^ n - 1) * B n) := by
      rw [← hleft]
      ring
    _ = q ^ n * ∑ k ∈ range n,
        (r - 1) ^ (n - k) / ((n - k + 1).factorial : ℂ) * B k := by
      rw [hreciprocal]
    _ = ∑ k ∈ range n,
        (1 - q) ^ (n - k) * q ^ k / ((n - k + 1).factorial : ℂ) * B k := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      have hkn : k ≤ n := (mem_range.mp hk).le
      have hqpow : q ^ n = q ^ (n - k) * q ^ k := by
        rw [← pow_add]
        congr 1
        omega
      have hscalePow : q ^ (n - k) * (r - 1) ^ (n - k) =
          (1 - q) ^ (n - k) := by
        rw [← mul_pow, hqri]
      calc
        q ^ n * ((r - 1) ^ (n - k) /
            ((n - k + 1).factorial : ℂ) * B k) =
          (q ^ (n - k) * (r - 1) ^ (n - k)) * q ^ k /
              ((n - k + 1).factorial : ℂ) * B k := by
            rw [hqpow]
            ring
        _ = (1 - q) ^ (n - k) * q ^ k /
              ((n - k + 1).factorial : ℂ) * B k := by
            rw [hscalePow]

private theorem exterior_finiteQPochhammerIn_self_mul_residual
    (q : ℂ) {k n : ℕ} (hkn : k ≤ n) :
    finiteQPochhammerIn q q k *
        (∏ j ∈ Ico (k + 1) (n + 1), (1 - q ^ j)) =
      finiteQPochhammerIn q q n := by
  unfold finiteQPochhammerIn
  rw [← Finset.prod_Ico_add' (fun j : ℕ ↦ 1 - q ^ j) k n 1]
  simpa only [pow_succ', mul_comm] using
    Finset.prod_range_mul_prod_Ico
      (fun j : ℕ ↦ 1 - q ^ (j + 1)) hkn

private theorem exterior_eval₂_geometricUniformMomentPolynomial_succ
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

private theorem exterior_geometricUniformMomentPolynomial_bridge_summand
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
    exact exterior_finiteQPochhammerIn_self_mul_residual q hkn
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

/-- For `1 < ‖q‖`, evaluation of the recursive moment polynomial is exactly
the finite-q-Pochhammer normalization of the Taylor coefficient of the
exterior reciprocal complex germ.  This is the same analytic object as the
manuscript's `j ≥ 1` reciprocal product, not a recurrence-only surrogate. -/
theorem geometricUniformMomentPolynomial_eval₂_eq_exteriorComplexMomentGerm_taylorCoefficient
    {q : ℂ} (hq : 1 < ‖q‖) (n : ℕ) :
    eval₂ (algebraMap ℚ ℂ) q (geometricUniformMomentPolynomial n) =
      finiteQPochhammerIn q q n / (1 - q) ^ n *
        (iteratedDeriv n (geometricUniformExteriorComplexMomentGerm q) 0 /
          (n.factorial : ℂ)) := by
  have hq1 : 1 - q ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    subst q
    norm_num at hq
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simp [geometricUniformExteriorComplexMomentGerm,
            geometricUniformComplexMomentProduct]
      | succ n =>
          rw [exterior_eval₂_geometricUniformMomentPolynomial_succ]
          let A : ℕ → ℂ := fun r ↦
            iteratedDeriv r (geometricUniformExteriorComplexMomentGerm q) 0 /
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
            normalized_exteriorComplexMomentGerm_recurrence hq (n + 1)
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
                exact exterior_geometricUniformMomentPolynomial_bridge_summand
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
