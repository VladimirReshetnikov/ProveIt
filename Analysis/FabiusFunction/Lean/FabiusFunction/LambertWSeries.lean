import FabiusFunction.LagrangeInversion
import Mathlib.RingTheory.PowerSeries.Exp

/-!
# The Lambert `W` series at the origin

The Lambert function satisfies `W(z) e^{W(z)} = z`, equivalently `W = z e^{-W}`, which is the
Lagrange functional equation with `φ(w) = e^{-w}`.  Since `e^{-w}` is invertible with inverse
`e^{w}`, the construction of `Fabius.Lagrange.solution` applies and produces the series directly,
so nothing here is conditional:

`W = ∑_{n ≥ 1} (-n)^{n-1} z^n / n!`  (`coeff_lambertW`).

The radius of convergence `e^{-1}` is analytic and is not formalized.

## Main results

* `expNeg`, `expNeg_mul_exp`, `expNeg_pow`.
* `lambertW`, `lambertW_eq`, `lambertW_mul_exp_subst`.
* `coeff_lambertW`, `coeff_lambertW_one`, `coeff_lambertW_two`.
-/

set_option autoImplicit false

open PowerSeries

namespace Fabius

/-- The series `e^{-w}`. -/
noncomputable def expNeg : ℚ⟦X⟧ := rescale (-1 : ℚ) (exp ℚ)

/-- `e^{0·w} = 1`. -/
theorem rescale_zero_exp' : rescale (0 : ℚ) (exp ℚ) = 1 := by
  rw [rescale_zero, RingHom.comp_apply, constantCoeff_exp, map_one]

/-- `e^{-w} e^{w} = 1`. -/
theorem expNeg_mul_exp : expNeg * exp ℚ = 1 := by
  have h : rescale (-1 : ℚ) (exp ℚ) * rescale (1 : ℚ) (exp ℚ) = 1 := by
    rw [exp_mul_exp_eq_exp_add, show (-1 : ℚ) + 1 = 0 by ring, rescale_zero_exp']
  rwa [rescale_one, RingHom.id_apply] at h

/-- `(e^{-w})^n = e^{-n w}`. -/
theorem expNeg_pow (n : ℕ) : expNeg ^ n = rescale (-(n : ℚ)) (exp ℚ) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, neg_zero, rescale_zero_exp']
  | succ n ih =>
    rw [pow_succ, ih, expNeg, exp_mul_exp_eq_exp_add]
    congr 1
    push_cast
    ring

/-- **The Lambert `W` series**, as the solution of `W = z e^{-W}`. -/
noncomputable def lambertW : ℚ⟦X⟧ := Lagrange.solution expNeg (exp ℚ) expNeg_mul_exp

/-- The defining equation `W = z e^{-W}`. -/
theorem lambertW_eq : lambertW = X * expNeg.subst lambertW :=
  Lagrange.solution_eq expNeg (exp ℚ) expNeg_mul_exp

/-- `W e^{W} = z`, the usual form of the defining equation. -/
theorem lambertW_mul_exp_subst : lambertW * (exp ℚ).subst lambertW = X := by
  have hone := Lagrange.subst_solution_mul expNeg (exp ℚ) expNeg_mul_exp
  rw [← lambertW] at hone
  calc lambertW * (exp ℚ).subst lambertW
      = X * expNeg.subst lambertW * (exp ℚ).subst lambertW := by rw [← lambertW_eq]
    _ = X * (expNeg.subst lambertW * (exp ℚ).subst lambertW) := by ring
    _ = X := by rw [hone, mul_one]

/-- **The coefficients:** `[z^{n+1}] W = (-(n+1))^n / (n+1)!`. -/
theorem coeff_lambertW (n : ℕ) :
    coeff (n + 1) lambertW = (-((n : ℚ) + 1)) ^ n / (n + 1).factorial := by
  have h := Lagrange.coeff_solution expNeg (exp ℚ) expNeg_mul_exp (n + 1) (by omega)
  rw [← lambertW, Nat.add_sub_cancel, expNeg_pow, coeff_rescale, coeff_exp,
    Algebra.algebraMap_self, RingHom.id_apply] at h
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hf : ((n).factorial : ℚ) ≠ 0 := by positivity
  push_cast at h ⊢
  rw [Nat.factorial_succ]
  push_cast
  field_simp at h ⊢
  linarith [h]

@[simp] theorem coeff_lambertW_one : coeff 1 lambertW = 1 := by
  have h := coeff_lambertW 0
  norm_num at h
  exact h

theorem coeff_lambertW_two : coeff 2 lambertW = -1 := by
  have h := coeff_lambertW 1
  norm_num at h
  exact h

end Fabius
