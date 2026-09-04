import FabiusFunction.ThetaQuasiPeriodicity
import FabiusFunction.QPochhammerInfinite
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The zeros of the theta function are simple

For `0 < ‖q‖ < 1` the theta function `θ(z;q) = ∑_{k ∈ ℤ} q^{k(k-1)/2} z^k` vanishes exactly at
`z = -q^m`, `m ∈ ℤ` (`bilateralTheta_eq_zero_iff`).  Each zero is simple: `θ` has a nonzero
derivative there (`exists_hasDerivAt_bilateralTheta_zero`, `deriv_bilateralTheta_ne_zero`),
which is the simplicity clause of cor:theta-quasi.

The proof isolates the vanishing factor of the triple product
`θ(z;q) = (-z;q)_∞ (-q/z;q)_∞ (q;q)_∞`: at `z₀ = -q^{-j}` (`j ≥ 0`) the factor is
`1 + zq^j` of `(-z;q)_∞`, at `z₀ = -q^{j+1}` it is `1 + q^{j+1}/z` of `(-q/z;q)_∞`; the
remaining product `G` is differentiable and nonvanishing at `z₀`, so `θ = u · G` near `z₀` has
derivative `u'(z₀) G(z₀) ≠ 0` (`hasDerivAt_of_eventuallyEq_mul`).
-/

set_option autoImplicit false

open Filter Topology

namespace Fabius

/-- **Simple-zero criterion.**  If `f = u · G` near `z₀`, `u z₀ = 0`, `u` has derivative `u'`
at `z₀` and `G` is differentiable at `z₀`, then `f` has derivative `u' · G z₀` at `z₀`. -/
theorem hasDerivAt_of_eventuallyEq_mul {f u G : ℂ → ℂ} {z₀ u' : ℂ}
    (hf : f =ᶠ[𝓝 z₀] fun z => u z * G z) (hu : HasDerivAt u u' z₀) (hu0 : u z₀ = 0)
    (hG : DifferentiableAt ℂ G z₀) : HasDerivAt f (u' * G z₀) z₀ := by
  have h := hu.mul hG.hasDerivAt
  rw [hu0, zero_mul, add_zero] at h
  exact h.congr_of_eventuallyEq hf

variable {q : ℂ}

/-- `(q^{-j};q)_j = ∏_{i<j} (1 - q^{i-j}) ≠ 0` for `0 < ‖q‖ < 1`. -/
theorem finiteQPochhammerIn_zpow_neg_self_ne_zero (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (j : ℕ) :
    finiteQPochhammerIn (q ^ (-(j : ℤ))) q j ≠ 0 := by
  rw [finiteQPochhammerIn]
  refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
  rw [Finset.mem_range] at hi
  intro h
  have h1 : q ^ (-(j : ℤ)) * q ^ i = 1 := (sub_eq_zero.mp h).symm
  rw [← zpow_natCast q i, ← zpow_add₀ hq0, show (-(j : ℤ) + i) = -((j - i : ℕ) : ℤ) by omega,
    zpow_neg, zpow_natCast, inv_eq_one] at h1
  have h2 : ‖q ^ (j - i)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (Nat.sub_ne_zero_of_lt hi)
  rw [h1, norm_one] at h2
  exact lt_irrefl _ h2

/-- **Simplicity at `z₀ = -q^{-j}`**: the vanishing factor is `1 + zq^j` of `(-z;q)_∞`. -/
theorem exists_hasDerivAt_bilateralTheta_neg_zpow_neg (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (j : ℕ) :
    ∃ D : ℂ, D ≠ 0 ∧ HasDerivAt (bilateralTheta q) D (-q ^ (-(j : ℤ))) := by
  set z₀ : ℂ := -q ^ (-(j : ℤ)) with hz₀
  have hz0 : z₀ ≠ 0 := neg_ne_zero.mpr (zpow_ne_zero _ hq0)
  set G : ℂ → ℂ := fun z => finiteQPochhammerIn (-z) q j * qPochhammerInfIn (-z * q ^ (j + 1)) q *
    qPochhammerInfIn (-(q / z)) q * qPochhammerInfIn q q with hG
  have hf : bilateralTheta q =ᶠ[𝓝 z₀] fun z => (1 + z * q ^ j) * G z := by
    filter_upwards [isOpen_ne.mem_nhds hz0] with z hz
    rw [bilateralTheta_eq_prod hq hz, qPochhammerInfIn_eq_finite_mul_shift (-z) hq (j + 1),
      finiteQPochhammerIn_succ, hG]
    ring
  have hu : HasDerivAt (fun z : ℂ => 1 + z * q ^ j) (1 * q ^ j) z₀ :=
    ((hasDerivAt_id z₀).mul_const (q ^ j)).const_add 1
  have hu0 : (1 : ℂ) + z₀ * q ^ j = 0 := by
    rw [hz₀, neg_mul, ← zpow_natCast q j, ← zpow_add₀ hq0, neg_add_cancel, zpow_zero]
    ring
  have hdiv : DifferentiableAt ℂ (fun z : ℂ => qPochhammerInfIn (-(q / z)) q) z₀ :=
    (differentiable_qPochhammerInfIn hq).differentiableAt.comp z₀
      (((differentiableAt_const q).div differentiableAt_id hz0).neg)
  have hGd : DifferentiableAt ℂ G z₀ := by
    have h1 : Differentiable ℂ fun z : ℂ => finiteQPochhammerIn (-z) q j :=
      (differentiable_finiteQPochhammerIn q j).comp differentiable_neg
    have h2 : Differentiable ℂ fun z : ℂ => qPochhammerInfIn (-z * q ^ (j + 1)) q :=
      (differentiable_qPochhammerInfIn hq).comp (differentiable_neg.mul_const _)
    exact ((h1.differentiableAt.mul h2.differentiableAt).mul hdiv).mul_const _
  have hG0 : G z₀ ≠ 0 := by
    have e1 : -z₀ = q ^ (-(j : ℤ)) := by rw [hz₀, neg_neg]
    have e2 : -z₀ * q ^ (j + 1) = q := by
      rw [e1, ← zpow_natCast q (j + 1), ← zpow_add₀ hq0,
        show (-(j : ℤ) + ((j + 1 : ℕ) : ℤ)) = 1 by push_cast; ring, zpow_one]
    have e3 : -(q / z₀) = q ^ (j + 1) := by
      rw [hz₀, div_neg, neg_neg, zpow_neg, div_inv_eq_mul, zpow_natCast, pow_succ']
    rw [hG]
    dsimp only
    rw [e2, e3, e1]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (qPochhammerInfIn_self_ne_zero hq)) ?_)
      (qPochhammerInfIn_self_ne_zero hq)
    · exact finiteQPochhammerIn_zpow_neg_self_ne_zero hq hq0 j
    · refine qPochhammerInfIn_ne_zero_of_norm_lt_one hq ?_
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero j)
  exact ⟨1 * q ^ j * G z₀, mul_ne_zero (mul_ne_zero one_ne_zero (pow_ne_zero _ hq0)) hG0,
    hasDerivAt_of_eventuallyEq_mul hf hu hu0 hGd⟩

/-- **Simplicity at `z₀ = -q^{j+1}`**: the vanishing factor is `1 + q^{j+1}/z` of
`(-q/z;q)_∞`. -/
theorem exists_hasDerivAt_bilateralTheta_neg_pow_succ (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (j : ℕ) :
    ∃ D : ℂ, D ≠ 0 ∧ HasDerivAt (bilateralTheta q) D (-q ^ (j + 1)) := by
  set z₀ : ℂ := -q ^ (j + 1) with hz₀
  have hz0 : z₀ ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ hq0)
  set G : ℂ → ℂ := fun z => qPochhammerInfIn (-z) q * finiteQPochhammerIn (-(q / z)) q j *
    qPochhammerInfIn (-(q / z) * q ^ (j + 1)) q * qPochhammerInfIn q q with hG
  have hf : bilateralTheta q =ᶠ[𝓝 z₀] fun z => (1 + q ^ (j + 1) * z⁻¹) * G z := by
    filter_upwards [isOpen_ne.mem_nhds hz0] with z hz
    have hu' : (1 : ℂ) - -(q / z) * q ^ j = 1 + q ^ (j + 1) * z⁻¹ := by
      field_simp
      ring
    rw [bilateralTheta_eq_prod hq hz, qPochhammerInfIn_eq_finite_mul_shift (-(q / z)) hq (j + 1),
      finiteQPochhammerIn_succ, hu', hG]
    ring
  have hu : HasDerivAt (fun z : ℂ => 1 + q ^ (j + 1) * z⁻¹) (q ^ (j + 1) * -(z₀ ^ 2)⁻¹) z₀ :=
    ((hasDerivAt_inv hz0).const_mul (q ^ (j + 1))).const_add 1
  have hu0 : (1 : ℂ) + q ^ (j + 1) * z₀⁻¹ = 0 := by
    rw [hz₀, inv_neg, mul_neg, mul_inv_cancel₀ (pow_ne_zero _ hq0)]
    ring
  have hdivneg : DifferentiableAt ℂ (fun z : ℂ => -(q / z)) z₀ :=
    ((differentiableAt_const q).div differentiableAt_id hz0).neg
  have hGd : DifferentiableAt ℂ G z₀ := by
    have h1 : Differentiable ℂ fun z : ℂ => qPochhammerInfIn (-z) q :=
      (differentiable_qPochhammerInfIn hq).comp differentiable_neg
    have h2 : DifferentiableAt ℂ (fun z : ℂ => finiteQPochhammerIn (-(q / z)) q j) z₀ :=
      (differentiable_finiteQPochhammerIn q j).differentiableAt.comp z₀ hdivneg
    have h3 : DifferentiableAt ℂ (fun z : ℂ => qPochhammerInfIn (-(q / z) * q ^ (j + 1)) q) z₀ :=
      (differentiable_qPochhammerInfIn hq).differentiableAt.comp z₀ (hdivneg.mul_const _)
    exact ((h1.differentiableAt.mul h2).mul h3).mul_const _
  have hG0 : G z₀ ≠ 0 := by
    have e1 : -z₀ = q ^ (j + 1) := by rw [hz₀, neg_neg]
    have e2 : -(q / z₀) = q ^ (-(j : ℤ)) := by
      rw [hz₀, div_neg, neg_neg, pow_succ', ← div_div, div_self hq0, one_div, ← zpow_natCast,
        ← zpow_neg]
    have e3 : -(q / z₀) * q ^ (j + 1) = q := by
      rw [e2, ← zpow_natCast q (j + 1), ← zpow_add₀ hq0,
        show (-(j : ℤ) + ((j + 1 : ℕ) : ℤ)) = 1 by push_cast; ring, zpow_one]
    rw [hG]
    dsimp only
    rw [e3, e2, e1]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_
      (finiteQPochhammerIn_zpow_neg_self_ne_zero hq hq0 j)) (qPochhammerInfIn_self_ne_zero hq))
      (qPochhammerInfIn_self_ne_zero hq)
    refine qPochhammerInfIn_ne_zero_of_norm_lt_one hq ?_
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero j)
  refine ⟨q ^ (j + 1) * -(z₀ ^ 2)⁻¹ * G z₀, ?_, hasDerivAt_of_eventuallyEq_mul hf hu hu0 hGd⟩
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hq0) (neg_ne_zero.mpr (inv_ne_zero
    (pow_ne_zero _ hz0)))) hG0

/-- **The zeros of `θ(·;q)` are simple** (cor:theta-quasi): at every zero `-q^m`, `m ∈ ℤ`, the
theta function has a nonzero derivative. -/
theorem exists_hasDerivAt_bilateralTheta_zero (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (m : ℤ) :
    ∃ D : ℂ, D ≠ 0 ∧ HasDerivAt (bilateralTheta q) D (-q ^ m) := by
  rcases Int.eq_nat_or_neg m with ⟨j, rfl | rfl⟩
  · rcases j with _ | j
    · simpa using exists_hasDerivAt_bilateralTheta_neg_zpow_neg hq hq0 0
    · have h := exists_hasDerivAt_bilateralTheta_neg_pow_succ hq hq0 j
      rwa [← zpow_natCast q (j + 1)] at h
  · exact exists_hasDerivAt_bilateralTheta_neg_zpow_neg hq hq0 j

/-- The derivative of `θ(·;q)` does not vanish at any zero `-q^m`. -/
theorem deriv_bilateralTheta_ne_zero (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (m : ℤ) :
    deriv (bilateralTheta q) (-q ^ m) ≠ 0 := by
  obtain ⟨D, hD, h⟩ := exists_hasDerivAt_bilateralTheta_zero hq hq0 m
  rw [h.deriv]
  exact hD

end Fabius
