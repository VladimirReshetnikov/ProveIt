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

## The sign hypothesis is necessary

`abs_sub_le_of_le_deriv` assumes `0 ≤ m` as well as `f' ≤ M`, and it must: with
`f' ≡ -10`, `m = -10` and `M = 0` the derivative bracket holds while
`|f x - f y| = 10|x - y|` exceeds `M|x - y| = 0`.  What makes the absolute-value
form work is that `0 ≤ m ≤ f'` forces `f` to be monotone, so `|f x - f y|` is the
signed increment and Mathlib's one-sided inequality applies to it directly.  The
drafts' hypothesis `0 < m` is exactly this.  The lower bracket needs no sign
condition.

Nothing here mentions the Lambert function; `LambertShiftInverse` instantiates
it at `F = f`, `m = 1`, `M = 2`.
-/

set_option autoImplicit false

open Set

namespace Fabius

variable {D : Set ℝ} {f : ℝ → ℝ} {m M x y : ℝ}

/-- **Upper mean-value bracket**, in absolute value: if `0 ≤ m ≤ f' ≤ M` on the
interior of a convex set, then `f` moves points by at most `M` times their
distance.  The hypothesis `0 ≤ m` is necessary; see the module docstring. -/
theorem abs_sub_le_of_le_deriv (hD : Convex ℝ D) (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (interior D))
    (hM : ∀ z ∈ interior D, deriv f z ≤ M)
    (hm : ∀ z ∈ interior D, m ≤ deriv f z) (hm0 : 0 ≤ m)
    (hx : x ∈ D) (hy : y ∈ D) :
    |f x - f y| ≤ M * |x - y| := by
  rcases le_total x y with h | h
  · have hup := Convex.image_sub_le_mul_sub_of_deriv_le hD hf hf' hM x hx y hy h
    have hlo := Convex.mul_sub_le_image_sub_of_le_deriv hD hf hf' hm x hx y hy h
    have hmono : 0 ≤ f y - f x := le_trans (by nlinarith) hlo
    rw [abs_sub_comm x y, abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - x),
      abs_sub_comm, abs_of_nonneg hmono]
    exact hup
  · have hup := Convex.image_sub_le_mul_sub_of_deriv_le hD hf hf' hM y hy x hx h
    have hlo := Convex.mul_sub_le_image_sub_of_le_deriv hD hf hf' hm y hy x hx h
    have hmono : 0 ≤ f x - f y := le_trans (by nlinarith) hlo
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - y), abs_of_nonneg hmono]
    exact hup

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
and `m ≤ f'`, the error is controlled by the residual: `m |x - g z| ≤ |f x - z|`. -/
theorem mul_abs_sub_right_inverse_le (hD : Convex ℝ D) (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (interior D))
    (hm : ∀ z ∈ interior D, m ≤ deriv f z)
    {g : ℝ → ℝ} {z : ℝ} (hgz : g z ∈ D) (hfg : f (g z) = z) (hx : x ∈ D) :
    m * |x - g z| ≤ |f x - z| := by
  have h := mul_abs_sub_le_abs_sub_of_le_deriv hD hf hf' hm hx hgz
  rwa [hfg] at h

/-- **Residual-to-error transfer, lower half.**  With `0 ≤ m ≤ f' ≤ M`, the
residual is at most `M` times the error. -/
theorem abs_sub_le_mul_abs_sub_right_inverse (hD : Convex ℝ D) (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (interior D))
    (hM : ∀ z ∈ interior D, deriv f z ≤ M)
    (hm : ∀ z ∈ interior D, m ≤ deriv f z) (hm0 : 0 ≤ m)
    {g : ℝ → ℝ} {z : ℝ} (hgz : g z ∈ D) (hfg : f (g z) = z) (hx : x ∈ D) :
    |f x - z| ≤ M * |x - g z| := by
  have h := abs_sub_le_of_le_deriv hD hf hf' hM hm hm0 hx hgz
  rwa [hfg] at h

/-- The drafts' `eq:residual-error-bound`, divided form: `|H - G| ≤ |R|/m`. -/
theorem abs_sub_right_inverse_le_div (hD : Convex ℝ D) (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (interior D))
    (hm : ∀ z ∈ interior D, m ≤ deriv f z) (hmpos : 0 < m)
    {g : ℝ → ℝ} {z : ℝ} (hgz : g z ∈ D) (hfg : f (g z) = z) (hx : x ∈ D) :
    |x - g z| ≤ |f x - z| / m := by
  rw [le_div_iff₀ hmpos, mul_comm]
  exact mul_abs_sub_right_inverse_le hD hf hf' hm hgz hfg hx

/-- The other half of `eq:residual-error-bound`: `|R|/M ≤ |H - G|`. -/
theorem div_le_abs_sub_right_inverse (hD : Convex ℝ D) (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (interior D))
    (hM : ∀ z ∈ interior D, deriv f z ≤ M)
    (hm : ∀ z ∈ interior D, m ≤ deriv f z) (hm0 : 0 ≤ m) (hMpos : 0 < M)
    {g : ℝ → ℝ} {z : ℝ} (hgz : g z ∈ D) (hfg : f (g z) = z) (hx : x ∈ D) :
    |f x - z| / M ≤ |x - g z| := by
  rw [div_le_iff₀ hMpos, mul_comm]
  exact abs_sub_le_mul_abs_sub_right_inverse hD hf hf' hM hm hm0 hgz hfg hx

end Fabius
