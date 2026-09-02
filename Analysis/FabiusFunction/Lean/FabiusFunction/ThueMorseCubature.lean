import FabiusFunction.BaseDigitProduct
import FabiusFunction.DyadicClosedForm
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Thue–Morse block sum as a nested integral of the `m`-th derivative

The atlas's integral cubature formula `p1:cor:integral-cubature`: for
`f ∈ C^m` and `h ≥ 0`,

`∑_{n < 2^m} ε_n f(x + n h)
  = (-1)^m ∫_0^h ∫_0^{2h} ⋯ ∫_0^{2^{m-1} h} f^{(m)}(x + t_0 + ⋯ + t_{m-1}) dt_{m-1} ⋯ dt_0`,

and its consequence `p1:cor:complete-monotone`: if `(-1)^m f^{(m)} ≥ 0` on
the interval `[x, x + (2^m - 1) h]` then the block sum is nonnegative.

## Method

Split the block `[0, 2^{m+1})` by the low bit: `ε_{2n} = ε_n`,
`ε_{2n+1} = -ε_n`, so

`∑_{n<2^{m+1}} ε_n f(x + n h) = ∑_{n<2^m} ε_n (f(x + 2n h) - f(x + 2n h + h))`,

and each difference is `-∫_0^h f'(x + 2n h + t) dt`.  Interchanging the
finite sum with the integral leaves, inside the integral, the block sum of
length `2^m` for `f'` at base point `x + t` with step `2h` — the induction
hypothesis.  This is why the nested integral is defined with the outermost
variable on `[0, h]` and the step doubling inward: exactly the order of
the atlas's display.

The identity is proved for every base point at once, which is what makes
the interchange legitimate without any theory of parametric integrals: the
integrand at the next level is a finite sum of continuous functions, never
an unknown nested integral.

## Main declarations

* `nestedDyadicIntegral m g x h` — the nested integral of the display.
* `thueMorseBlockSum m f x h` — `∑_{n<2^m} ε_n f(x + n h)`.
* `thueMorseBlockSum_eq_nestedDyadicIntegral` — **`p1:eq:integral-cubature`**.
* `nestedDyadicIntegral_nonneg`, `thueMorseBlockSum_nonneg` — **`p1:eq:complete-monotone-sign`**.
-/

set_option autoImplicit false

namespace Fabius

open Finset intervalIntegral

/-- The nested dyadic integral
`∫_0^h ∫_0^{2h} ⋯ ∫_0^{2^{m-1} h} g(x + t_0 + ⋯ + t_{m-1}) dt_{m-1} ⋯ dt_0`,
defined with the outermost variable on `[0, h]` and the step doubling at
each level inward. -/
noncomputable def nestedDyadicIntegral : ℕ → (ℝ → ℝ) → ℝ → ℝ → ℝ
  | 0, g, x, _ => g x
  | m + 1, g, x, h => ∫ t in (0 : ℝ)..h, nestedDyadicIntegral m g (x + t) (2 * h)

@[simp] theorem nestedDyadicIntegral_zero (g : ℝ → ℝ) (x h : ℝ) :
    nestedDyadicIntegral 0 g x h = g x := rfl

theorem nestedDyadicIntegral_succ (m : ℕ) (g : ℝ → ℝ) (x h : ℝ) :
    nestedDyadicIntegral (m + 1) g x h
      = ∫ t in (0 : ℝ)..h, nestedDyadicIntegral m g (x + t) (2 * h) := rfl

/-- The Thue–Morse block sum `∑_{n<2^m} ε_n f(x + n h)`. -/
noncomputable def thueMorseBlockSum (m : ℕ) (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  ∑ n ∈ range (2 ^ m), (thueMorseSign n : ℝ) * f (x + n * h)

/-- Splitting the block by the low bit. -/
theorem thueMorseBlockSum_succ (m : ℕ) (f : ℝ → ℝ) (x h : ℝ) :
    thueMorseBlockSum (m + 1) f x h
      = ∑ n ∈ range (2 ^ m), (thueMorseSign n : ℝ) *
          (f (x + 2 * n * h) - f (x + (2 * n + 1) * h)) := by
  unfold thueMorseBlockSum
  rw [pow_succ', sum_range_mul_eq_sum_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [sum_range_succ, sum_range_one]
  simp only [add_zero, thueMorseSign_two_mul, thueMorseSign_two_mul_add_one]
  push_cast
  ring

/-- **The integral cubature formula** (`p1:eq:integral-cubature`).  For
`f ∈ C^m` and every `x`, `h`,

`∑_{n<2^m} ε_n f(x + n h) = (-1)^m · nestedDyadicIntegral m f^{(m)} x h`. -/
theorem thueMorseBlockSum_eq_nestedDyadicIntegral (m : ℕ) :
    ∀ f : ℝ → ℝ, ContDiff ℝ m f → ∀ x h : ℝ,
      thueMorseBlockSum m f x h = (-1) ^ m * nestedDyadicIntegral m (iteratedDeriv m f) x h := by
  induction m with
  | zero =>
      intro f _ x h
      simp [thueMorseBlockSum, thueMorseSign, binaryWeight]
  | succ m ih =>
      intro f hf x h
      have hf1 : ContDiff ℝ ((m : WithTop ℕ∞) + 1) f := by
        have := hf
        rwa [Nat.cast_succ] at this
      have hd : Differentiable ℝ f := (contDiff_succ_iff_deriv.mp hf1).1
      have hf' : ContDiff ℝ m (deriv f) := (contDiff_succ_iff_deriv.mp hf1).2.2
      have hcd : Continuous (deriv f) :=
        hf.continuous_deriv (by exact_mod_cast Nat.le_add_left 1 m)
      rw [thueMorseBlockSum_succ]
      -- each difference is the integral of the derivative over `[0, h]`
      have hstep : ∀ n : ℕ, f (x + 2 * n * h) - f (x + (2 * n + 1) * h)
          = -∫ t in (0 : ℝ)..h, deriv f (x + 2 * n * h + t) := by
        intro n
        have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) h,
            HasDerivAt (fun t => f (x + 2 * n * h + t)) (deriv f (x + 2 * n * h + t)) t := by
          intro t _
          have := (hd (x + 2 * n * h + t)).hasDerivAt.comp t
            ((hasDerivAt_id t).const_add (x + 2 * n * h))
          simpa [Function.comp] using this
        have hint : IntervalIntegrable (fun t => deriv f (x + 2 * n * h + t)) MeasureTheory.volume 0 h :=
          (hcd.comp (continuous_const.add continuous_id)).intervalIntegrable 0 h
        rw [integral_eq_sub_of_hasDerivAt hderiv hint]
        have e1 : x + (2 * n + 1) * h = x + 2 * n * h + h := by ring
        rw [e1, add_zero, neg_sub]
      simp_rw [hstep, mul_neg]
      rw [sum_neg_distrib]
      simp_rw [← integral_const_mul]
      have hint2 : ∀ n ∈ range (2 ^ m), IntervalIntegrable
          (fun t => (thueMorseSign n : ℝ) * deriv f (x + 2 * n * h + t)) MeasureTheory.volume 0 h :=
        fun n _ => (continuous_const.mul
          (hcd.comp (continuous_const.add continuous_id))).intervalIntegrable 0 h
      rw [← integral_finsetSum hint2]
      -- the integrand is the block sum of length `2^m` for `deriv f` at `x + t` with step `2h`
      have hinner : ∀ t : ℝ, ∑ n ∈ range (2 ^ m), (thueMorseSign n : ℝ) * deriv f (x + 2 * n * h + t)
          = thueMorseBlockSum m (deriv f) (x + t) (2 * h) := by
        intro t
        unfold thueMorseBlockSum
        refine sum_congr rfl fun n _ => ?_
        rw [show x + 2 * n * h + t = x + t + n * (2 * h) by ring]
      simp_rw [hinner, ih (deriv f) hf', integral_const_mul]
      rw [← iteratedDeriv_succ', nestedDyadicIntegral_succ]
      ring

/-! ## Sign for completely monotone kernels -/

/-- A nested dyadic integral of a function nonnegative on
`[x, x + (2^m - 1) h]` is nonnegative (`h ≥ 0`). -/
theorem nestedDyadicIntegral_nonneg (m : ℕ) (g : ℝ → ℝ) :
    ∀ x h : ℝ, 0 ≤ h → (∀ y ∈ Set.Icc x (x + (2 ^ m - 1) * h), 0 ≤ g y) →
      0 ≤ nestedDyadicIntegral m g x h := by
  induction m with
  | zero =>
      intro x h _ hg
      exact hg x ⟨le_refl x, by simp⟩
  | succ m ih =>
      intro x h hh hg
      rw [nestedDyadicIntegral_succ]
      refine integral_nonneg hh fun t ht => ?_
      refine ih (x + t) (2 * h) (by linarith) fun y hy => hg y ⟨?_, ?_⟩
      · linarith [ht.1, hy.1]
      · have h2 : (2 : ℝ) ^ (m + 1) = 2 * 2 ^ m := by ring
        rw [h2]
        nlinarith [ht.2, hy.2, hh, (by positivity : (0 : ℝ) ≤ 2 ^ m)]

/-- Constants pass through the nested integral. -/
theorem nestedDyadicIntegral_const_mul (m : ℕ) (c : ℝ) (g : ℝ → ℝ) :
    ∀ x h : ℝ, nestedDyadicIntegral m (fun y => c * g y) x h = c * nestedDyadicIntegral m g x h := by
  induction m with
  | zero => intro x h; rfl
  | succ m ih =>
      intro x h
      rw [nestedDyadicIntegral_succ, nestedDyadicIntegral_succ]
      simp_rw [ih]
      exact integral_const_mul c _

/-- **Sign for completely monotone kernels** (`p1:eq:complete-monotone-sign`):
if `(-1)^m f^{(m)} ≥ 0` on `[x, x + (2^m - 1) h]` and `h ≥ 0`, then
`∑_{n<2^m} ε_n f(x + n h) ≥ 0`. -/
theorem thueMorseBlockSum_nonneg (m : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ m f) (x h : ℝ)
    (hh : 0 ≤ h)
    (hsign : ∀ y ∈ Set.Icc x (x + (2 ^ m - 1) * h), 0 ≤ (-1) ^ m * iteratedDeriv m f y) :
    0 ≤ thueMorseBlockSum m f x h := by
  rw [thueMorseBlockSum_eq_nestedDyadicIntegral m f hf x h, ← nestedDyadicIntegral_const_mul]
  exact nestedDyadicIntegral_nonneg m _ x h hh hsign

/-! ## The finite-difference bound -/

/-- The nested dyadic integral of a function bounded by `C` on
`[x, x + (2^m - 1) h]` is bounded by `C` times the box volume
`h^m 2^{0+1+⋯+(m-1)}` (`h ≥ 0`). -/
theorem abs_nestedDyadicIntegral_le (m : ℕ) (g : ℝ → ℝ) (C : ℝ) :
    ∀ x h : ℝ, 0 ≤ h → (∀ y ∈ Set.Icc x (x + (2 ^ m - 1) * h), |g y| ≤ C) →
      |nestedDyadicIntegral m g x h| ≤ C * (2 ^ (∑ i ∈ range m, i) * h ^ m) := by
  induction m with
  | zero =>
      intro x h _ hg
      simpa using hg x ⟨le_refl x, by simp⟩
  | succ m ih =>
      intro x h hh hg
      rw [nestedDyadicIntegral_succ]
      have hb : ∀ t ∈ Set.uIoc (0 : ℝ) h,
          ‖nestedDyadicIntegral m g (x + t) (2 * h)‖
            ≤ C * (2 ^ (∑ i ∈ range m, i) * (2 * h) ^ m) := by
        intro t ht
        rw [Set.uIoc_of_le hh] at ht
        rw [Real.norm_eq_abs]
        refine ih (x + t) (2 * h) (by linarith) fun y hy => hg y ⟨?_, ?_⟩
        · linarith [ht.1, hy.1]
        · have h2 : (2 : ℝ) ^ (m + 1) = 2 * 2 ^ m := by ring
          rw [h2]
          nlinarith [ht.2, hy.2, hh, (by positivity : (0 : ℝ) ≤ 2 ^ m)]
      have hI := norm_integral_le_of_norm_le_const hb
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hh] at hI
      calc |∫ t in (0 : ℝ)..h, nestedDyadicIntegral m g (x + t) (2 * h)|
          ≤ C * (2 ^ (∑ i ∈ range m, i) * (2 * h) ^ m) * h := hI
        _ = C * (2 ^ (∑ i ∈ range (m + 1), i) * h ^ (m + 1)) := by
            rw [sum_range_succ, pow_add, mul_pow, pow_succ]
            ring

/-- **The finite-difference bound** (`p1:eq:finite-difference-bound`): if
`|f^{(m)}| ≤ C` on `[x, x + (2^m - 1) h]` and `h ≥ 0`, then

`|∑_{n<2^m} ε_n f(x + n h)| ≤ C · 2^{0+1+⋯+(m-1)} h^m`. -/
theorem abs_thueMorseBlockSum_le (m : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ m f) (x h : ℝ)
    (hh : 0 ≤ h) (C : ℝ)
    (hC : ∀ y ∈ Set.Icc x (x + (2 ^ m - 1) * h), |iteratedDeriv m f y| ≤ C) :
    |thueMorseBlockSum m f x h| ≤ C * (2 ^ (∑ i ∈ range m, i) * h ^ m) := by
  rw [thueMorseBlockSum_eq_nestedDyadicIntegral m f hf x h, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, one_mul]
  exact abs_nestedDyadicIntegral_le m _ C x h hh hC

/-- The Gauss sum in the exponent is the binomial coefficient:
`0 + 1 + ⋯ + (m-1) = C(m, 2)`. -/
theorem sum_range_id_eq_choose_two (m : ℕ) : ∑ i ∈ range m, i = m.choose 2 := by
  rw [Nat.choose_two_right]
  exact (Nat.div_eq_of_eq_mul_left two_pos (Finset.sum_range_id_mul_two m).symm).symm

end Fabius
