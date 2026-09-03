import FabiusFunction.LacunaryRieszIntegral

/-!
# Reflection about the midpoint, and the half mass

Two facts, each stated where it actually lives.

**Reflection is an integrality phenomenon, not a dyadic one.**  For
*any* integer `k`, `sin(πk(1−t)) = ±sin(πkt)`, so absolute values and
squares are reflection-invariant; the lacunary product `∏sin(π2ʲt)` is
one instance, and so is any product over any index set of integer
multipliers.

**Half mass is a statement about symmetric functions.**  If
`f(1−t) = f(t)` and `f` is integrable on `[0,½]` and on `[½,1]`, then
`∫₀^{1/2} f = ½∫₀¹ f` — nothing else about `f` is used.

Specialising both to `∏_{j<n} sin²(π2ʲt)`, whose total mass is the
exact `2⁻ⁿ` of `integral_prod_sin_sq_two_pow`, gives

`∫₀^{1/2} ∏_{j<n} sin²(π2ʲt) dt = 2^{−(n+1)}`.

* `abs_sin_int_mul_reflect`, `sin_sq_int_mul_reflect` — the integer
  reflection.
* `prod_abs_sin_reflect`, `prod_sin_sq_reflect` — products over an
  arbitrary index set.
* `integral_half_of_reflect_of_intervalIntegrable` — half mass for any
  symmetric function integrable on the two halves.
* `integral_half_of_reflect` — the same under integrability on every
  interval.
* `integral_prod_sin_sq_two_pow_half` — the dyadic instance.
-/

set_option autoImplicit false

open Finset Real MeasureTheory

namespace Fabius

/-! ## Reflection at integer multiples -/

/-- **The reflection**: at an integer multiplier the sine reverses
sign under `t ↦ 1 − t`, so its modulus is symmetric. -/
theorem abs_sin_int_mul_reflect (k : ℤ) (t : ℝ) :
    |Real.sin (π * k * (1 - t))| = |Real.sin (π * k * t)| := by
  have harg : π * (k:ℝ) * (1 - t) = (k:ℝ) * π - π * (k:ℝ) * t := by
    ring
  rw [harg, Real.sin_int_mul_pi_sub, abs_neg, abs_mul, abs_zpow]
  norm_num

/-- The squared sine at an integer multiplier is reflection-invariant. -/
theorem sin_sq_int_mul_reflect (k : ℤ) (t : ℝ) :
    Real.sin (π * k * (1 - t)) ^ 2 = Real.sin (π * k * t) ^ 2 := by
  rw [← sq_abs (Real.sin (π * (k:ℝ) * (1 - t))),
    ← sq_abs (Real.sin (π * (k:ℝ) * t)), abs_sin_int_mul_reflect]

/-- Any product of `|sin|` at integer multipliers is
reflection-invariant. -/
theorem prod_abs_sin_reflect {ι : Type*} (s : Finset ι) (k : ι → ℤ)
    (t : ℝ) :
    ∏ i ∈ s, |Real.sin (π * (k i) * (1 - t))| =
      ∏ i ∈ s, |Real.sin (π * (k i) * t)| :=
  Finset.prod_congr rfl (fun i _ => abs_sin_int_mul_reflect (k i) t)

/-- Any product of `sin²` at integer multipliers is
reflection-invariant. -/
theorem prod_sin_sq_reflect {ι : Type*} (s : Finset ι) (k : ι → ℤ)
    (t : ℝ) :
    ∏ i ∈ s, Real.sin (π * (k i) * (1 - t)) ^ 2 =
      ∏ i ∈ s, Real.sin (π * (k i) * t) ^ 2 :=
  Finset.prod_congr rfl (fun i _ => sin_sq_int_mul_reflect (k i) t)

/-! ## Half mass of a symmetric function -/

/-- **Half mass**: a function symmetric about `1/2` puts half of its
mass on each side.  Only the symmetry and integrability on the two
halves `[0, ½]` and `[½, 1]` are used. -/
theorem integral_half_of_reflect_of_intervalIntegrable {f : ℝ → ℝ}
    (hsymm : ∀ x : ℝ, f (1 - x) = f x)
    (hint₀ : IntervalIntegrable f MeasureTheory.volume 0 (1/2))
    (hint₁ : IntervalIntegrable f MeasureTheory.volume (1/2) 1) :
    ∫ t in (0:ℝ)..(1/2), f t = (∫ t in (0:ℝ)..1, f t) / 2 := by
  have hrefl : ∫ t in (1/2:ℝ)..1, f t = ∫ t in (0:ℝ)..(1/2), f t := by
    have hsub := intervalIntegral.integral_comp_sub_left
      (a := (0:ℝ)) (b := (1/2 : ℝ)) f 1
    rw [intervalIntegral.integral_congr (g := f)
      (fun x _ => hsymm x)] at hsub
    norm_num at hsub
    exact hsub.symm
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (a := (0:ℝ)) (b := (1/2 : ℝ)) (c := (1:ℝ)) hint₀ hint₁
  rw [hrefl] at hsplit
  linarith

/-- **Half mass** under integrability on every interval: the special
case of `integral_half_of_reflect_of_intervalIntegrable` in which `f`
is interval-integrable everywhere. -/
theorem integral_half_of_reflect {f : ℝ → ℝ}
    (hsymm : ∀ x : ℝ, f (1 - x) = f x)
    (hint : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b) :
    ∫ t in (0:ℝ)..(1/2), f t = (∫ t in (0:ℝ)..1, f t) / 2 :=
  integral_half_of_reflect_of_intervalIntegrable hsymm (hint 0 (1/2))
    (hint (1/2) 1)

/-! ## The dyadic instance -/

/-- The lacunary squared product is reflection-invariant (the case
`k j = 2ʲ` of `prod_sin_sq_reflect`). -/
theorem prod_sin_sq_two_pow_reflect (n : ℕ) (t : ℝ) :
    ∏ j ∈ range n, Real.sin (π * 2 ^ j * (1 - t)) ^ 2 =
      ∏ j ∈ range n, Real.sin (π * 2 ^ j * t) ^ 2 := by
  have h := prod_sin_sq_reflect (range n) (fun j => (2 ^ j : ℤ)) t
  push_cast at h
  exact h

/-- **The half mass of the lacunary square**:
`∫₀^{1/2} ∏_{j<n} sin²(π2ʲt) dt = 2^{−(n+1)}`. -/
theorem integral_prod_sin_sq_two_pow_half (n : ℕ) :
    ∫ t in (0:ℝ)..(1/2), ∏ j ∈ range n, Real.sin (π * 2 ^ j * t) ^ 2 =
      (1 / 2 : ℝ) ^ (n + 1) := by
  have hcont : Continuous
      (fun t : ℝ => ∏ j ∈ range n, Real.sin (π * 2 ^ j * t) ^ 2) :=
    continuous_finsetProd _ (fun j _ => by fun_prop)
  rw [integral_half_of_reflect_of_intervalIntegrable
      (prod_sin_sq_two_pow_reflect n)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _),
    integral_prod_sin_sq_two_pow n, pow_succ]
  ring

end Fabius
