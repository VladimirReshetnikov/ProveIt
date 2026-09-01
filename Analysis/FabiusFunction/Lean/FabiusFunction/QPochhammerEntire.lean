import FabiusFunction.RvachevPochhammerFactorization
import Mathlib.Analysis.Analytic.Order

/-!
# Entire complex q-Pochhammer products

For every strict complex contraction `q`, this module promotes the infinite
q-Pochhammer product

`(a;q)_∞ = ∏' j : ℕ, (1 - a * q ^ j)`

from pointwise convergence to a locally uniformly convergent entire function
of `a`.  Its zero set is exactly the set detected by the displayed factors,
in a division-free form that includes the degenerate nome `q = 0`.  Each of
those zeros is simple.

## Main results

* `hasProdLocallyUniformly_complexQPochhammerInf` gives locally uniform
  convergence on the whole complex plane.
* `complexQPochhammerInf_differentiable` proves that `(·;q)_∞` is entire.
* `complexQPochhammerInf_eq_zero_iff` gives the exact factor-zero locus,
  without dividing by a power of `q`.
* `analyticOrderAt_complexQPochhammerInf_of_eq_zero` proves that every zero
  has analytic order one, including the unique zero at `a = 1` when `q = 0`.
-/

set_option autoImplicit false

open Asymptotics Filter Topology
open scoped BigOperators

namespace Fabius

noncomputable section

-- Keep the analytic product API on the standard noncomputable complex
-- C-star-algebra hierarchy, as in `RvachevPochhammerFactorization`.
attribute [-instance] Complex.commRing

private theorem one_sub_sub_one_isBigO :
    (fun z : ℂ => (1 - z) - 1) =O[𝓝 0] (fun z : ℂ => z) := by
  have hdiff : Differentiable ℂ (fun z : ℂ => 1 - z) := by
    fun_prop
  simpa using (hdiff 0).isBigO_sub

/-- For `‖q‖ < 1`, the factors defining `(a;q)_∞` converge locally
uniformly as functions of `a` on the whole complex plane. -/
theorem hasProdLocallyUniformly_complexQPochhammerInf
    (q : ℂ) (hq : ‖q‖ < 1) :
    HasProdLocallyUniformly
      (fun (j : ℕ) (a : ℂ) => 1 - a * q ^ j)
      (fun a : ℂ => complexQPochhammerInf a q) := by
  have hprod := hasProdLocallyUniformly_scaled
    (fun z : ℂ => 1 - z) (fun j : ℕ => q ^ j)
    (summable_norm_qpow q hq) one_sub_sub_one_isBigO
    (by fun_prop : Continuous fun z : ℂ => 1 - z)
  simpa only [smul_eq_mul, mul_comm, complexQPochhammerInf] using hprod

/-- For every strict complex contraction `q`, the function
`a ↦ (a;q)_∞` is entire. -/
theorem complexQPochhammerInf_differentiable
    (q : ℂ) (hq : ‖q‖ < 1) :
    Differentiable ℂ (fun a : ℂ => complexQPochhammerInf a q) := by
  have hdiff := differentiable_tprod_scaled_of_eq_one
    (fun z : ℂ => 1 - z) (fun j : ℕ => q ^ j)
    (summable_norm_qpow q hq)
    (by fun_prop : Differentiable ℂ fun z : ℂ => 1 - z)
    (by simp)
  simpa only [smul_eq_mul, mul_comm, complexQPochhammerInf] using hdiff

/-- The infinite complex q-Pochhammer product vanishes exactly when one of
its displayed factors vanishes.  The factor-zero form is intentional: it
remains correct for the degenerate strict contraction `q = 0`. -/
theorem complexQPochhammerInf_eq_zero_iff
    (a q : ℂ) (hq : ‖q‖ < 1) :
    complexQPochhammerInf a q = 0 ↔
      ∃ j : ℕ, 1 - a * q ^ j = 0 := by
  have hzero := tprod_scaled_eq_zero_iff
    (fun z : ℂ => 1 - z) (fun j : ℕ => q ^ j)
    (summable_norm_qpow q hq) one_sub_sub_one_isBigO a
  simpa only [smul_eq_mul, mul_comm, complexQPochhammerInf] using hzero

set_option maxHeartbeats 400000 in
private theorem complexQPochhammerInf_eq_finite_mul_shift
    (a q : ℂ) (hq : ‖q‖ < 1) (n : ℕ) :
    complexQPochhammerInf a q =
      finiteQPochhammerIn a q n *
        complexQPochhammerInf (a * q ^ n) q := by
  have htail : HasProd
      (fun k : ℕ => 1 - a * q ^ (k + n))
      (complexQPochhammerInf (a * q ^ n) q) := by
    refine (hasProd_complexQPochhammerInf (a * q ^ n) hq).congr_fun ?_
    intro k
    rw [pow_add]
    ring
  rw [finiteQPochhammerIn]
  exact htail.prod_range_mul.tprod_eq

private theorem complexQPochhammerFactor_zero_index_unique
    (a q : ℂ) (hq : ‖q‖ < 1) {j k : ℕ}
    (hj : 1 - a * q ^ j = 0) (hk : 1 - a * q ^ k = 0) :
    j = k := by
  have haj : a * q ^ j = 1 := (sub_eq_zero.mp hj).symm
  have hak : a * q ^ k = 1 := (sub_eq_zero.mp hk).symm
  by_cases hq0 : q = 0
  · subst q
    have hj0 : j = 0 := by
      by_contra hjne
      rw [zero_pow hjne, mul_zero] at haj
      exact zero_ne_one haj
    have hk0 : k = 0 := by
      by_contra hkne
      rw [zero_pow hkne, mul_zero] at hak
      exact zero_ne_one hak
    exact hj0.trans hk0.symm
  · have ha0 : a ≠ 0 := by
      intro ha
      rw [ha, zero_mul] at haj
      exact zero_ne_one haj
    have hpows : q ^ j = q ^ k := by
      apply mul_left_cancel₀ ha0
      exact haj.trans hak.symm
    apply pow_right_injective₀ (norm_pos_iff.mpr hq0) (ne_of_lt hq)
    simpa only [norm_pow] using congrArg norm hpows

private theorem complexQPochhammerInf_eq_sub_mul_cofactor
    (a q : ℂ) (hq : ‖q‖ < 1) {j : ℕ}
    (hj : 1 - a * q ^ j = 0) (z : ℂ) :
    complexQPochhammerInf z q =
      (z - a) *
        ((-q ^ j) * finiteQPochhammerIn z q j *
          complexQPochhammerInf (z * q ^ (j + 1)) q) := by
  have haj : a * q ^ j = 1 := (sub_eq_zero.mp hj).symm
  have hfactor : 1 - z * q ^ j = (z - a) * (-q ^ j) := by
    calc
      1 - z * q ^ j = a * q ^ j - z * q ^ j := by rw [haj]
      _ = (z - a) * (-q ^ j) := by ring
  rw [complexQPochhammerInf_eq_finite_mul_shift z q hq (j + 1),
    finiteQPochhammerIn_succ, hfactor]
  ring

/-- Every zero of the entire function `a ↦ (a;q)_∞` is simple.  The result
uses the raw factor-zero hypothesis and therefore includes `q = 0`, where
the only zero is the factor at index zero. -/
theorem analyticOrderAt_complexQPochhammerInf_of_eq_zero
    (a q : ℂ) (hq : ‖q‖ < 1)
    (ha : complexQPochhammerInf a q = 0) :
    analyticOrderAt (fun z : ℂ => complexQPochhammerInf z q) a = 1 := by
  obtain ⟨j, hj⟩ := (complexQPochhammerInf_eq_zero_iff a q hq).mp ha
  have haj : a * q ^ j = 1 := (sub_eq_zero.mp hj).symm
  have hqj : q ^ j ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at haj
    exact zero_ne_one haj
  have hprefix : finiteQPochhammerIn a q j ≠ 0 := by
    rw [finiteQPochhammerIn, Finset.prod_ne_zero_iff]
    intro k hk hzero
    have hkj := complexQPochhammerFactor_zero_index_unique
      a q hq hj hzero
    have hlt : k < j := Finset.mem_range.mp hk
    omega
  have htail :
      complexQPochhammerInf (a * q ^ (j + 1)) q ≠ 0 := by
    intro hzero
    obtain ⟨k, hk⟩ :=
      (complexQPochhammerInf_eq_zero_iff
        (a * q ^ (j + 1)) q hq).mp hzero
    have hshift : 1 - a * q ^ ((j + 1) + k) = 0 := by
      simpa only [pow_add, mul_assoc] using hk
    have hindices := complexQPochhammerFactor_zero_index_unique
      a q hq hj hshift
    omega
  let U : ℂ → ℂ := fun z =>
    (-q ^ j) * finiteQPochhammerIn z q j *
      complexQPochhammerInf (z * q ^ (j + 1)) q
  have hfinite :
      Differentiable ℂ (fun z : ℂ => finiteQPochhammerIn z q j) := by
    unfold finiteQPochhammerIn
    fun_prop
  have htailDiff : Differentiable ℂ (fun z : ℂ =>
      complexQPochhammerInf (z * q ^ (j + 1)) q) :=
    (complexQPochhammerInf_differentiable q hq).comp (by fun_prop)
  have hU : Differentiable ℂ U := by
    dsimp only [U]
    fun_prop
  have hUa : U a ≠ 0 := by
    dsimp only [U]
    exact mul_ne_zero
      (mul_ne_zero (neg_ne_zero.mpr hqj) hprefix) htail
  have hAn : AnalyticAt ℂ
      (fun z : ℂ => complexQPochhammerInf z q) a :=
    (complexQPochhammerInf_differentiable q hq).analyticAt a
  refine hAn.analyticOrderAt_eq_natCast.mpr ⟨U, hU.analyticAt a, hUa, ?_⟩
  exact Filter.Eventually.of_forall fun z => by
    simpa only [pow_one, smul_eq_mul, U] using
      complexQPochhammerInf_eq_sub_mul_cofactor a q hq hj z

end

end Fabius
