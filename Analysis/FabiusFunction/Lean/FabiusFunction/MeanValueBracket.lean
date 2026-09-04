import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Two-sided mean-value brackets and residual-to-error transfer

The Lambert-inverse transseries drafts state, as `thm:residual-general`, that a
derivative bracket transfers a *residual* into an *error*: if `F` is strictly
increasing with `0 < m ≤ F' ≤ M` between the exact inverse value `G(X)` and an
approximation `H(X)`, and `R = F(H) - X`, then

`|R|/M ≤ |H - G| ≤ |R|/m`.

That is the shape every numerical certificate in those drafts uses, so it is
worth having once, for an arbitrary function on an arbitrary convex set, rather
than re-proved at each instance.

The two halves are Mathlib's mean-value inequalities in absolute-value form
(`abs_sub_le_of_le_deriv`, `mul_abs_sub_le_abs_sub_of_le_deriv`), and the
transfer is their composition with a right inverse (`abs_sub_right_inverse_le`,
`le_abs_sub_right_inverse`).

Nothing here mentions the Lambert function; `LambertShiftInverse` instantiates
it at `F = f`, `m = 1`, `M = 2`.
-/

set_option autoImplicit false

open Set

namespace Fabius

variable {D : Set ℝ} {f : ℝ → ℝ} {m M x y : ℝ}

/-- **Upper mean-value bracket**, in absolute value: if `f' ≤ M` on the interior
of a convex set, then `f` moves points by at most `M` times their distance. -/
theorem abs_sub_le_of_le_deriv (hD : Convex ℝ D) (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (interior D))
    (hM : ∀ z ∈ interior D, deriv f z ≤ M)
    (hm : ∀ z ∈ interior D, m ≤ deriv f z)
    (hx : x ∈ D) (hy : y ∈ D) :
    |f x - f y| ≤ M * |x - y| := by
  rcases le_total x y with h | h
  · have hup := Convex.image_sub_le_mul_sub_of_deriv_le hD hf hf' hM x hx y hy h
    have hlo := Convex.mul_sub_le_image_sub_of_le_deriv hD hf hf' hm x hx y hy h
    rw [abs_sub_comm x y, abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - x)]
    rcases le_total (f x) (f y) with hfxy | hfxy
    · rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ f y - f x)]
      exact hup
    · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ f x - f y)]
      nlinarith [hlo, hup]
  · have hup := Convex.image_sub_le_mul_sub_of_deriv_le hD hf hf' hM y hy x hx h
    have hlo := Convex.mul_sub_le_image_sub_of_le_deriv hD hf hf' hm y hy x hx h
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - y)]
    rcases le_total (f y) (f x) with hfxy | hfxy
    · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ f x - f y)]
      exact hup
    · rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ f y - f x)]
      nlinarith [hlo, hup]

/-- **Lower mean-value bracket**, in absolute value: if `m ≤ f'` on the interior
of a convex set, then `f` moves points by at least `m` times their distance. -/
theorem mul_abs_sub_le_abs_sub_of_le_deriv (hD : Convex ℝ D) (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (interior D))
    (hm : ∀ z ∈ interior D, m ≤ deriv f z)
    (hx : x ∈ D) (hy : y ∈ D) :
    m * |x - y| ≤ |f x - f y| := by
  rcases le_total x y with h | h
  · have hlo := Convex.mul_sub_le_image_sub_of_le_deriv hD hf hf' hm x hx y hy h
    rw [abs_sub_comm x y, abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - x)]
    calc m * (y - x) ≤ f y - f x := hlo
      _ ≤ |f y - f x| := le_abs_self _
      _ = |f x - f y| := abs_sub_comm _ _
  · have hlo := Convex.mul_sub_le_image_sub_of_le_deriv hD hf hf' hm y hy x hx h
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - y)]
    calc m * (x - y) ≤ f x - f y := hlo
      _ ≤ |f x - f y| := le_abs_self _

/-- **Residual-to-error transfer, upper half.**  With `g` a right inverse of `f`
on `D` and `m ≤ f'`, the distance to the exact value is at most the residual
divided by `m`: here in the cleared form `m |x - g z| ≤ |f x - z|`. -/
theorem mul_abs_sub_right_inverse_le (hD : Convex ℝ D) (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (interior D))
    (hm : ∀ z ∈ interior D, m ≤ deriv f z)
    {g : ℝ → ℝ} {z : ℝ} (hgz : g z ∈ D) (hfg : f (g z) = z) (hx : x ∈ D) :
    m * |x - g z| ≤ |f x - z| := by
  have h := mul_abs_sub_le_abs_sub_of_le_deriv hD hf hf' hm hx hgz
  rwa [hfg] at h

/-- **Residual-to-error transfer, lower half.**  With `f' ≤ M`, the residual is
at most `M` times the distance to the exact value. -/
theorem abs_sub_le_mul_abs_sub_right_inverse (hD : Convex ℝ D) (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (interior D))
    (hM : ∀ z ∈ interior D, deriv f z ≤ M)
    (hm : ∀ z ∈ interior D, m ≤ deriv f z)
    {g : ℝ → ℝ} {z : ℝ} (hgz : g z ∈ D) (hfg : f (g z) = z) (hx : x ∈ D) :
    |f x - z| ≤ M * |x - g z| := by
  have h := abs_sub_le_of_le_deriv hD hf hf' hM hm hx hgz
  rwa [hfg] at h

/-- The drafts' `eq:residual-error-bound` in its divided form: for `0 < m`,
`|R|/M ≤ |H - G| ≤ |R|/m`. -/
theorem abs_sub_right_inverse_le_div (hD : Convex ℝ D) (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (interior D))
    (hm : ∀ z ∈ interior D, m ≤ deriv f z) (hmpos : 0 < m)
    {g : ℝ → ℝ} {z : ℝ} (hgz : g z ∈ D) (hfg : f (g z) = z) (hx : x ∈ D) :
    |x - g z| ≤ |f x - z| / m := by
  rw [le_div_iff₀ hmpos, mul_comm]
  exact mul_abs_sub_right_inverse_le hD hf hf' hm hgz hfg hx

end Fabius
