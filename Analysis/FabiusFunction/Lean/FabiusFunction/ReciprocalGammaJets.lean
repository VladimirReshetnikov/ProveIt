import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Exact first jets of the reciprocal Gamma function

Mathlib proves that `s ↦ (Complex.Gamma s)⁻¹` is entire and records its
functional equation

`Γ(s)⁻¹ = s * Γ(s + 1)⁻¹`.

Iterating the derivative of this identity gives the exact simple-zero
coefficient at every nonpositive integer:

`(Γ⁻¹)'(-r) = (-1)^r r!`.

This is the reusable local input needed whenever a reciprocal Gamma factor
cancels a Mellin pole.  In particular, it upgrades the origin-only lemma used
by the Thue--Morse Dirichlet continuation to all of its trivial zeros.

## Main results

* `hasDerivAt_Gamma_inv_neg_nat` gives the exact derivative at `-r`.
* `deriv_Gamma_inv_neg_nat` is the corresponding `deriv` formula.
* `analyticOrderAt_Gamma_inv_neg_nat` says every zero is simple.
* `tendsto_Gamma_inv_div_add_nat` packages the exact first-order local
  coefficient as a punctured-neighbourhood limit.
-/

set_option autoImplicit false

open Complex Filter
open scoped Topology

namespace Fabius

/-- Exact derivative value of the reciprocal Gamma function at `-r`.

The proof is division-free at the Gamma poles.  Starting from
`Γ(s)⁻¹ = s * Γ(s+1)⁻¹`, the step from `-r` to `-(r+1)` multiplies the
previous derivative by `-(r+1)`. -/
theorem deriv_Gamma_inv_neg_nat (r : ℕ) :
    deriv (fun s : ℂ => (Complex.Gamma s)⁻¹) (-(r : ℂ)) =
      (-1 : ℂ) ^ r * r.factorial := by
  induction r with
  | zero =>
      norm_num
      have hg : Differentiable ℂ
          (fun s : ℂ => (Complex.Gamma (s + 1))⁻¹) :=
        Complex.differentiable_one_div_Gamma.comp
          (differentiable_id.add_const 1)
      have hd := (hasDerivAt_id (0 : ℂ)).mul (hg 0).hasDerivAt
      have heq : (fun s : ℂ => (Complex.Gamma s)⁻¹) =
          id * fun s : ℂ => (Complex.Gamma (s + 1))⁻¹ := by
        funext s
        simpa only [Pi.mul_apply, id_eq] using
          Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one s
      rw [heq, hd.deriv]
      simp [Complex.Gamma_one]
  | succ r ihr =>
      let x : ℂ := -((r + 1 : ℕ) : ℂ)
      have hx : x + 1 = -(r : ℂ) := by
        dsimp only [x]
        push_cast
        ring
      have hg : Differentiable ℂ
          (fun s : ℂ => (Complex.Gamma (s + 1))⁻¹) :=
        Complex.differentiable_one_div_Gamma.comp
          (differentiable_id.add_const 1)
      have houter : HasDerivAt (fun s : ℂ => (Complex.Gamma s)⁻¹)
          ((-1 : ℂ) ^ r * r.factorial) (x + 1) := by
        have houter0 : HasDerivAt (fun s : ℂ => (Complex.Gamma s)⁻¹)
            (deriv (fun s : ℂ => (Complex.Gamma s)⁻¹) (x + 1)) (x + 1) :=
          (Complex.differentiable_one_div_Gamma (x + 1)).hasDerivAt
        exact houter0.congr_deriv (by rw [hx, ihr])
      have hderivShift :
          deriv (fun s : ℂ => (Complex.Gamma (s + 1))⁻¹) x =
            (-1 : ℂ) ^ r * r.factorial :=
        (HasDerivAt.comp_add_const x 1 houter).deriv
      have heq : (fun s : ℂ => (Complex.Gamma s)⁻¹) =
          id * fun s : ℂ => (Complex.Gamma (s + 1))⁻¹ := by
        funext s
        simpa only [Pi.mul_apply, id_eq] using
          Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one s
      change deriv (fun s : ℂ => (Complex.Gamma s)⁻¹) x = _
      rw [heq, deriv_mul differentiableAt_id (hg x),
        deriv_id, hderivShift, hx, Complex.Gamma_neg_nat_eq_zero,
        inv_zero, one_mul, zero_add, id_eq]
      dsimp only [x]
      rw [Nat.factorial_succ, pow_succ]
      push_cast
      ring

/-- **Exact first jet of the reciprocal Gamma function.**  At every
nonpositive integer `-r`, the entire function `s ↦ Γ(s)⁻¹` has derivative
`(-1)^r r!`. -/
theorem hasDerivAt_Gamma_inv_neg_nat (r : ℕ) :
    HasDerivAt (fun s : ℂ => (Complex.Gamma s)⁻¹)
      ((-1 : ℂ) ^ r * r.factorial) (-(r : ℂ)) := by
  simpa only [deriv_Gamma_inv_neg_nat] using
    (Complex.differentiable_one_div_Gamma (-(r : ℂ))).hasDerivAt

/-- Compatibility name for the origin case: `(Γ⁻¹)'(0) = 1`. -/
theorem hasDerivAt_Gamma_inv_zero :
    HasDerivAt (fun s : ℂ => (Complex.Gamma s)⁻¹) 1 0 := by
  simpa using hasDerivAt_Gamma_inv_neg_nat 0

/-- Every nonpositive integer is a simple zero of the reciprocal Gamma
function. -/
theorem analyticOrderAt_Gamma_inv_neg_nat (r : ℕ) :
    analyticOrderAt (fun s : ℂ => (Complex.Gamma s)⁻¹) (-(r : ℂ)) = 1 := by
  apply (Complex.differentiable_one_div_Gamma.analyticAt (-(r : ℂ)))
    |>.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · rw [Complex.Gamma_neg_nat_eq_zero, inv_zero]
  · rw [deriv_Gamma_inv_neg_nat]
    exact mul_ne_zero (pow_ne_zero r (by norm_num))
      (Nat.cast_ne_zero.mpr r.factorial_ne_zero)

/-- Exact local coefficient at the reciprocal-Gamma zero `-r`:
`Γ(s)⁻¹ / (s+r) → (-1)^r r!` as `s → -r` off the center. -/
theorem tendsto_Gamma_inv_div_add_nat (r : ℕ) :
    Tendsto (fun s : ℂ => (Complex.Gamma s)⁻¹ / (s + (r : ℂ)))
      (𝓝[≠] (-(r : ℂ))) (𝓝 ((-1 : ℂ) ^ r * r.factorial)) := by
  have h := (hasDerivAt_Gamma_inv_neg_nat r).tendsto_slope
  have hzero : (Complex.Gamma (-(r : ℂ)))⁻¹ = 0 := by
    rw [Complex.Gamma_neg_nat_eq_zero, inv_zero]
  convert h using 1
  · funext s
    simp only [slope, hzero, vsub_eq_sub, sub_zero, sub_neg_eq_add, smul_eq_mul]
    rw [inv_mul_eq_div]

end Fabius
