import FabiusFunction.BaseDigitProduct
import FabiusFunction.DyadicClosedForm
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic.LinearCombination
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

/-- The empty nest of integrations is evaluation: `I_0 g x h = g x`. -/
@[simp] theorem nestedDyadicIntegral_zero (g : ℝ → ℝ) (x h : ℝ) :
    nestedDyadicIntegral 0 g x h = g x := rfl

/-- Peeling the outermost integration of the nested dyadic integral, with
the step doubling at each level.  This is the defining recursion, exposed
so that clients need not unfold the definition. -/
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
          exact (hd (x + 2 * n * h + t)).hasDerivAt.comp_const_add (x + 2 * n * h) t
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

/-! ## Strict positivity -/

/-- The block sum is linear in `f`: negation. -/
theorem thueMorseBlockSum_neg (m : ℕ) (f : ℝ → ℝ) (x h : ℝ) :
    thueMorseBlockSum m (-f) x h = -thueMorseBlockSum m f x h := by
  unfold thueMorseBlockSum
  rw [← Finset.sum_neg_distrib]
  exact sum_congr rfl fun n _ => by simp only [Pi.neg_apply]; ring

/-- For continuous `f`, the block sum is continuous in the base point. -/
theorem continuous_thueMorseBlockSum_base (m : ℕ) {f : ℝ → ℝ} (hf : Continuous f) (x h : ℝ) :
    Continuous fun t => thueMorseBlockSum m f (x + t) h := by
  unfold thueMorseBlockSum
  refine continuous_finset_sum _ fun n _ => continuous_const.mul (hf.comp ?_)
  exact (continuous_const.add continuous_id).add continuous_const

/-- The one-step reduction behind the cubature formula, as a statement on
its own: for `f ∈ C^{m+1}`,
`∑_{n<2^{m+1}} ε_n f(x + n h) = -∫_0^h (∑_{n<2^m} ε_n f'(x + t + n·2h)) dt`. -/
theorem thueMorseBlockSum_succ_eq_neg_integral (m : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ (m + 1) f) (x h : ℝ) :
    thueMorseBlockSum (m + 1) f x h
      = -∫ t in (0 : ℝ)..h, thueMorseBlockSum m (deriv f) (x + t) (2 * h) := by
  have hf1 : ContDiff ℝ ((m : WithTop ℕ∞) + 1) f := hf
  have hf' : ContDiff ℝ m (deriv f) := (contDiff_succ_iff_deriv.mp hf1).2.2
  have hsq : ((-1 : ℝ) ^ m) * (-1) ^ m = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [thueMorseBlockSum_eq_nestedDyadicIntegral (m + 1) f hf x h, nestedDyadicIntegral_succ,
    iteratedDeriv_succ']
  have : ∀ t : ℝ, nestedDyadicIntegral m (iteratedDeriv m (deriv f)) (x + t) (2 * h)
      = (-1) ^ m * thueMorseBlockSum m (deriv f) (x + t) (2 * h) := by
    intro t
    rw [thueMorseBlockSum_eq_nestedDyadicIntegral m (deriv f) hf' (x + t) (2 * h), ← mul_assoc,
      hsq, one_mul]
  simp_rw [this]
  rw [integral_const_mul, pow_succ]
  set I := ∫ t in (0 : ℝ)..h, thueMorseBlockSum m (deriv f) (x + t) (2 * h) with hI
  linear_combination (-I) * hsq

/-- **Strict positivity for completely monotone kernels**: if `h > 0` and
`(-1)^m f^{(m)} > 0` on `[x, x + (2^m - 1) h]`, then
`∑_{n<2^m} ε_n f(x + n h) > 0`.  This is the strict form behind the
atlas's `> 0` displays. -/
theorem thueMorseBlockSum_pos (m : ℕ) :
    ∀ f : ℝ → ℝ, ContDiff ℝ m f → ∀ x h : ℝ, 0 < h →
      (∀ y ∈ Set.Icc x (x + (2 ^ m - 1) * h), 0 < (-1) ^ m * iteratedDeriv m f y) →
      0 < thueMorseBlockSum m f x h := by
  induction m with
  | zero =>
      intro f _ x h _ hsign
      have := hsign x ⟨le_refl x, by simp⟩
      simpa [thueMorseBlockSum, thueMorseSign, binaryWeight] using this
  | succ m ih =>
      intro f hf x h hh hsign
      have hf1 : ContDiff ℝ ((m : WithTop ℕ∞) + 1) f := by
        have := hf
        rwa [Nat.cast_succ] at this
      have hf' : ContDiff ℝ m (deriv f) := (contDiff_succ_iff_deriv.mp hf1).2.2
      have hcd : Continuous (deriv f) :=
        hf.continuous_deriv (by exact_mod_cast Nat.le_add_left 1 m)
      rw [thueMorseBlockSum_succ_eq_neg_integral m f hf x h, neg_pos]
      -- the integrand is negative on `[0, h]`
      have hneg : ∀ t ∈ Set.Icc (0 : ℝ) h, thueMorseBlockSum m (deriv f) (x + t) (2 * h) < 0 := by
        intro t ht
        have hpos := ih (-deriv f) hf'.neg (x + t) (2 * h) (by linarith) ?_
        · rw [thueMorseBlockSum_neg] at hpos
          linarith
        · intro y hy
          rw [iteratedDeriv_neg, ← iteratedDeriv_succ']
          have hy' : y ∈ Set.Icc x (x + (2 ^ (m + 1) - 1) * h) := by
            refine ⟨by linarith [ht.1, hy.1], ?_⟩
            have h2 : (2 : ℝ) ^ (m + 1) = 2 * 2 ^ m := by ring
            rw [h2]
            nlinarith [ht.2, hy.2, hh.le, (by positivity : (0 : ℝ) ≤ 2 ^ m)]
          have := hsign y hy'
          rw [pow_succ] at this
          linarith
      have hcont : Continuous fun t => thueMorseBlockSum m (deriv f) (x + t) (2 * h) :=
        continuous_thueMorseBlockSum_base m hcd x (2 * h)
      have hI : 0 < ∫ t in (0 : ℝ)..h, -thueMorseBlockSum m (deriv f) (x + t) (2 * h) := by
        refine intervalIntegral_pos_of_pos_on (hcont.neg.intervalIntegrable 0 h) ?_ hh
        intro t ht
        have := hneg t ⟨ht.1.le, ht.2.le⟩
        linarith
      rw [integral_neg] at hI
      linarith

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

/-! ## The unit-cube form -/

/-- The nested unit-cube integral
`∫_0^1 ⋯ ∫_0^1 g(x + h (u_0 + 2 u_1 + ⋯ + 2^{m-1} u_{m-1})) du_{m-1} ⋯ du_0`,
defined recursively with the outermost variable `u_0` and the step doubling
inward, in parallel with `nestedDyadicIntegral`. -/
noncomputable def nestedUnitIntegral : ℕ → (ℝ → ℝ) → ℝ → ℝ → ℝ
  | 0, g, x, _ => g x
  | m + 1, g, x, h => ∫ u in (0 : ℝ)..1, nestedUnitIntegral m g (x + h * u) (2 * h)

/-- Peeling the outermost integration of the unit-cube form, whose inner
variable ranges over `[0,1]` while the step doubles.  The defining
recursion, exposed for clients. -/
theorem nestedUnitIntegral_succ (m : ℕ) (g : ℝ → ℝ) (x h : ℝ) :
    nestedUnitIntegral (m + 1) g x h
      = ∫ u in (0 : ℝ)..1, nestedUnitIntegral m g (x + h * u) (2 * h) := rfl

/-- **Rescaling to the unit cube**: the nested dyadic integral is the box
volume `h^m 2^{0+1+⋯+(m-1)}` times the nested unit-cube integral, by the
substitution `t_j = 2^j h u_j` one level at a time. -/
theorem nestedDyadicIntegral_eq_unit (m : ℕ) (g : ℝ → ℝ) :
    ∀ x h : ℝ, nestedDyadicIntegral m g x h
      = h ^ m * 2 ^ (∑ i ∈ range m, i) * nestedUnitIntegral m g x h := by
  induction m with
  | zero => intro x h; simp [nestedUnitIntegral]
  | succ m ih =>
      intro x h
      rw [nestedDyadicIntegral_succ, nestedUnitIntegral_succ]
      simp_rw [ih]
      rw [integral_const_mul]
      have hsub : ∫ t in (0 : ℝ)..h, nestedUnitIntegral m g (x + t) (2 * h)
          = h * ∫ u in (0 : ℝ)..1, nestedUnitIntegral m g (x + h * u) (2 * h) := by
        have := smul_integral_comp_mul_left (fun t => nestedUnitIntegral m g (x + t) (2 * h))
          (a := (0 : ℝ)) (b := 1) h
        simp only [mul_zero, mul_one, smul_eq_mul] at this
        exact this.symm
      rw [hsub, sum_range_succ, pow_add, pow_succ]
      ring

/-- **The unit-cube cubature formula** (`p1:eq:unit-cube-cubature`): for
`f ∈ C^m`,

`∑_{n<2^m} ε_n f(x + n h)
  = (-1)^m 2^{0+1+⋯+(m-1)} h^m ∫_{[0,1]^m} f^{(m)}(x + h ∑_j 2^j u_j) du`,

the box integral written as the nested unit-cube integral. -/
theorem thueMorseBlockSum_eq_nestedUnitIntegral (m : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ m f)
    (x h : ℝ) :
    thueMorseBlockSum m f x h
      = (-1) ^ m * 2 ^ (∑ i ∈ range m, i) * h ^ m *
          nestedUnitIntegral m (iteratedDeriv m f) x h := by
  rw [thueMorseBlockSum_eq_nestedDyadicIntegral m f hf x h, nestedDyadicIntegral_eq_unit]
  ring

end Fabius
