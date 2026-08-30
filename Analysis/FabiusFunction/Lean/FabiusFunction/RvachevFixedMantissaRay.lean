import FabiusFunction.BirkhoffProductBridge
import FabiusFunction.SincProductShells

/-!
# Exact fixed-mantissa rays of the Rvachev Fourier product

This file isolates the finite algebra behind the arithmetic-ray chapter of
`Fabius_Arithmetic_Rays_Frontier_Report`.  Its basic object is the normalized
dyadic sine product

`Q n t = ∏ j < n, |2 sin (π 2^j t)|`.

The useful structure is more general than the rational-ray application:

* `normalizedDyadicSineProduct_add` is the exact cocycle law for every real
  seed;
* `normalizedDyadicSineProduct_add_int` records invariance under every
  integral translation, not merely the shift from `y` to `y - 1` used in the
  report;
* `normalizedDyadicSineProduct_add_of_dyadic_period` and
  `normalizedDyadicSineProduct_mul_add_of_dyadic_period` give the one-block
  recurrence and its finite quotient--remainder iteration whenever a dyadic
  seed returns modulo an integer.  No rationality, multiplicative order, or
  cyclotomic field is needed;
* `norm_rvachevFourierProduct_fixedMantissa_cross` is the zero-valid exact
  factorization on an arbitrary real ray, obtained directly from the general
  shell identity in `SincProductShells` at base point `y / 2`;
* `norm_rvachevFourierProduct_fixedMantissa` divides by the nonzero geometric
  denominator when `y ≠ 0`, and
  `norm_rvachevFourierProduct_fixedMantissa_of_mem_Ioo` recovers the report's
  displayed normalization for `1 < y < 2`.

The bounded tail called `H(y)` in the report is represented exactly by
`rvachevFixedMantissaTail y = ‖rvachevFourierProduct (y / 2)‖`.  This is the
modulus of the infinite product beginning with
`sinc (π y / 2)`, so the finite orbit product and the analytic tail remain
cleanly separated.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The normalized length-`n` sine product along the dyadic orbit of `t`:
`Qₙ(t) = ∏_{j<n} |2 sin (π 2ʲ t)|`.

This is the finite arithmetic factor in a fixed-mantissa shell of the Rvachev
Fourier product. -/
noncomputable def normalizedDyadicSineProduct (n : ℕ) (t : ℝ) : ℝ :=
  ∏ j ∈ range n, |2 * Real.sin (Real.pi * ((2 : ℝ) ^ j * t))|

/-- The empty normalized dyadic sine product is one. -/
@[simp] theorem normalizedDyadicSineProduct_zero (t : ℝ) :
    normalizedDyadicSineProduct 0 t = 1 := by
  simp [normalizedDyadicSineProduct]

/-- Every normalized dyadic sine product is nonnegative. -/
theorem normalizedDyadicSineProduct_nonneg (n : ℕ) (t : ℝ) :
    0 ≤ normalizedDyadicSineProduct n t := by
  unfold normalizedDyadicSineProduct
  positivity

/-- The normalized product is the absolute value of the un-normalized signed
finite product used by `BirkhoffProductBridge`. -/
theorem normalizedDyadicSineProduct_eq_abs_prod (n : ℕ) (t : ℝ) :
    normalizedDyadicSineProduct n t =
      |∏ j ∈ range n, 2 * Real.sin (Real.pi * ((2 : ℝ) ^ j * t))| := by
  rw [normalizedDyadicSineProduct, Finset.abs_prod]

/-- Pulling the positive normalization `2` out of every factor gives
`Qₙ(t) = 2ⁿ ∏_{j<n} |sin (π 2ʲ t)|`. -/
theorem normalizedDyadicSineProduct_eq_two_pow_mul (n : ℕ) (t : ℝ) :
    normalizedDyadicSineProduct n t =
      (2 : ℝ) ^ n *
        ∏ j ∈ range n, |Real.sin (Real.pi * ((2 : ℝ) ^ j * t))| := by
  unfold normalizedDyadicSineProduct
  simp_rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

/-- Off the finite zero set, the logarithm of `Qₙ` is the Birkhoff sum of
the logarithmic sine cocycle.  This packages the pointwise bridge from
`BirkhoffProductBridge` for the named finite product. -/
theorem log_normalizedDyadicSineProduct (n : ℕ) {t : ℝ}
    (hne : ∀ j, j < n →
      Real.sin (Real.pi * (doublingMap^[j] t)) ≠ 0) :
    Real.log (normalizedDyadicSineProduct n t) =
      ∑ j ∈ range n,
        Real.log |2 * Real.sin (Real.pi * (doublingMap^[j] t))| := by
  rw [normalizedDyadicSineProduct_eq_abs_prod]
  exact log_abs_prod_two_sin_global n hne

/-- **Dyadic product cocycle.**  Splitting a product after `m` factors
rescales the seed of the remaining `n` factors by `2ᵐ`:
`Q_{m+n}(t) = Q_m(t) Q_n(2ᵐ t)`. -/
theorem normalizedDyadicSineProduct_add (m n : ℕ) (t : ℝ) :
    normalizedDyadicSineProduct (m + n) t =
      normalizedDyadicSineProduct m t *
        normalizedDyadicSineProduct n ((2 : ℝ) ^ m * t) := by
  unfold normalizedDyadicSineProduct
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  have harg :
      Real.pi * ((2 : ℝ) ^ (m + j) * t) =
        Real.pi * ((2 : ℝ) ^ j * ((2 : ℝ) ^ m * t)) := by
    rw [pow_add]
    ring
  rw [harg]

/-- Integral translation does not change a normalized dyadic sine product:
`Qₙ(t + z) = Qₙ(t)` for every integer `z`.

At level `j` the phase changes by the integral multiple `2ʲ z` of `π`;
the possible sign disappears under the absolute value. -/
theorem normalizedDyadicSineProduct_add_int (n : ℕ) (t : ℝ) (z : ℤ) :
    normalizedDyadicSineProduct n (t + (z : ℝ)) =
      normalizedDyadicSineProduct n t := by
  unfold normalizedDyadicSineProduct
  apply Finset.prod_congr rfl
  intro j _
  let q : ℤ := ((2 : ℕ) ^ j : ℤ) * z
  have harg :
      Real.pi * ((2 : ℝ) ^ j * (t + (z : ℝ))) =
        Real.pi * ((2 : ℝ) ^ j * t) + q * Real.pi := by
    dsimp [q]
    push_cast
    ring
  have hsign : |((-1 : ℝ) ^ q)| = 1 := by
    rw [abs_zpow, abs_neg, abs_one, one_zpow]
  rw [abs_mul, abs_mul, harg, Real.sin_add_int_mul_pi, abs_mul, hsign,
    one_mul]

/-- The report's shift from the mantissa `y` to the orbit seed `y - 1`:
`Qₙ(y - 1) = Qₙ(y)`.  It is the unit-shift specialization of the full
integer-translation law. -/
theorem normalizedDyadicSineProduct_sub_one (n : ℕ) (y : ℝ) :
    normalizedDyadicSineProduct n (y - 1) =
      normalizedDyadicSineProduct n y := by
  have h := normalizedDyadicSineProduct_add_int n (y - 1) 1
  simpa using h.symm

/-- **One-block recurrence for a repeating dyadic seed.**  If `2ᵈ t`
returns to `t` modulo an integer, then every following block of `n` factors is
identical to the initial one:
`Q_{n+d}(t) = Q_d(t) Q_n(t)`.

The hypothesis is deliberately free of rational denominators and
multiplicative orders; those enter only when constructing a returning seed. -/
theorem normalizedDyadicSineProduct_add_of_dyadic_period
    (n d : ℕ) (t : ℝ) (z : ℤ)
    (hperiod : (2 : ℝ) ^ d * t = t + (z : ℝ)) :
    normalizedDyadicSineProduct (n + d) t =
      normalizedDyadicSineProduct d t * normalizedDyadicSineProduct n t := by
  calc
    normalizedDyadicSineProduct (n + d) t =
        normalizedDyadicSineProduct (d + n) t := by rw [Nat.add_comm]
    _ = normalizedDyadicSineProduct d t *
        normalizedDyadicSineProduct n ((2 : ℝ) ^ d * t) :=
      normalizedDyadicSineProduct_add d n t
    _ = normalizedDyadicSineProduct d t *
        normalizedDyadicSineProduct n (t + (z : ℝ)) := by rw [hperiod]
    _ = normalizedDyadicSineProduct d t * normalizedDyadicSineProduct n t := by
      rw [normalizedDyadicSineProduct_add_int]

/-- **Finite periodic-block formula.**  Under the same returning-seed
hypothesis, `q` complete blocks and a remainder `r` satisfy
`Q_{qd+r}(t) = Q_d(t)^q Q_r(t)`.

This is the algebraic engine of every later rational-ray recurrence, but the
statement itself uses only a dyadic return modulo an integer. -/
theorem normalizedDyadicSineProduct_mul_add_of_dyadic_period
    (q r d : ℕ) (t : ℝ) (z : ℤ)
    (hperiod : (2 : ℝ) ^ d * t = t + (z : ℝ)) :
    normalizedDyadicSineProduct (q * d + r) t =
      normalizedDyadicSineProduct d t ^ q *
        normalizedDyadicSineProduct r t := by
  induction q with
  | zero => simp
  | succ q ih =>
      calc
        normalizedDyadicSineProduct ((q + 1) * d + r) t =
            normalizedDyadicSineProduct ((q * d + r) + d) t := by
          rw [show (q + 1) * d + r = (q * d + r) + d by ring]
        _ = normalizedDyadicSineProduct d t *
            normalizedDyadicSineProduct (q * d + r) t :=
          normalizedDyadicSineProduct_add_of_dyadic_period
            (q * d + r) d t z hperiod
        _ = normalizedDyadicSineProduct d t *
            (normalizedDyadicSineProduct d t ^ q *
              normalizedDyadicSineProduct r t) := by rw [ih]
        _ = normalizedDyadicSineProduct d t ^ (q + 1) *
            normalizedDyadicSineProduct r t := by
          rw [pow_succ]
          ring

/-- The bounded analytic tail in the fixed-mantissa factorization.

With the report's indexing this is
`H(y) = |∏_{r≥1} sinc (π y / 2ʳ)|`; the shift by one in the infinite
product is exactly the evaluation of `rvachevFourierProduct` at `y / 2`. -/
noncomputable def rvachevFixedMantissaTail (y : ℝ) : ℝ :=
  ‖rvachevFourierProduct ((y / 2 : ℝ) : ℂ)‖

/-- The fixed-mantissa tail is nonnegative. -/
theorem rvachevFixedMantissaTail_nonneg (y : ℝ) :
    0 ≤ rvachevFixedMantissaTail y := by
  exact norm_nonneg _

private theorem prod_abs_sin_shell_half_eq (n : ℕ) (y : ℝ) :
    (∏ j ∈ range n,
        |Real.sin ((2 : ℝ) ^ (j + 1) * Real.pi * (y / 2))|) =
      ∏ j ∈ range n,
        |Real.sin (Real.pi * ((2 : ℝ) ^ j * y))| := by
  apply Finset.prod_congr rfl
  intro j _
  have harg :
      (2 : ℝ) ^ (j + 1) * Real.pi * (y / 2) =
        Real.pi * ((2 : ℝ) ^ j * y) := by
    rw [pow_succ]
    ring
  rw [harg]

/-- **Half-base shell factorization, total form.**  For every real `y` and
every finite shell length `n`, including `y = 0`,

`2^{n(n+1)/2} (π|y|)^n ‖Φ(2ⁿ y/2)‖ = Qₙ(y-1) H(y)`.

This is the reusable form of the report's exact factorization.  It follows
from `norm_rvachevFourierProduct_two_pow_mul_cross n (y / 2)` by multiplying
through by the `2ⁿ` absorbed into the normalized orbit product. -/
theorem norm_rvachevFourierProduct_two_pow_mul_half_cross (n : ℕ) (y : ℝ) :
    ((2 : ℝ) ^ (n * (n + 1) / 2) * (Real.pi * |y|) ^ n) *
        ‖rvachevFourierProduct
          ((2 : ℂ) ^ n * ((y / 2 : ℝ) : ℂ))‖ =
      normalizedDyadicSineProduct n (y - 1) *
        rvachevFixedMantissaTail y := by
  have hshell :=
    norm_rvachevFourierProduct_two_pow_mul_cross n (y / 2)
  have hden :
      (2 : ℝ) ^ n *
          ((2 : ℝ) ^ (n * (n + 1) / 2) *
            (Real.pi * |y / 2|) ^ n) =
        (2 : ℝ) ^ (n * (n + 1) / 2) *
          (Real.pi * |y|) ^ n := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hpi : Real.pi * (|y| / 2) = (Real.pi * |y|) / 2 := by ring
    rw [hpi, div_pow]
    field_simp
  have hscaled := congrArg (fun x : ℝ => (2 : ℝ) ^ n * x) hshell
  calc
    ((2 : ℝ) ^ (n * (n + 1) / 2) * (Real.pi * |y|) ^ n) *
        ‖rvachevFourierProduct
          ((2 : ℂ) ^ n * ((y / 2 : ℝ) : ℂ))‖ =
      (2 : ℝ) ^ n *
        (((2 : ℝ) ^ (n * (n + 1) / 2) *
          (Real.pi * |y / 2|) ^ n) *
            ‖rvachevFourierProduct
              ((2 : ℂ) ^ n * ((y / 2 : ℝ) : ℂ))‖) := by
        rw [← hden]
        ring
    _ = (2 : ℝ) ^ n *
        ((∏ j ∈ range n,
            |Real.sin ((2 : ℝ) ^ (j + 1) * Real.pi * (y / 2))|) *
          rvachevFixedMantissaTail y) := by
      simpa only [rvachevFixedMantissaTail] using hscaled
    _ = normalizedDyadicSineProduct n (y - 1) *
        rvachevFixedMantissaTail y := by
      rw [prod_abs_sin_shell_half_eq,
        normalizedDyadicSineProduct_sub_one,
        normalizedDyadicSineProduct_eq_two_pow_mul]
      ring

/-- **Half-base shell factorization, divided form.**  If `y ≠ 0`, then

`‖Φ(2ⁿ y/2)‖ = Qₙ(y-1) /
  (2^{n(n+1)/2} (π|y|)^n) · H(y)`.

This is the direct specialization of
`norm_rvachevFourierProduct_two_pow_mul n (y / 2)`; the only subsequent
work is the finite normalization `Qₙ = 2ⁿ ∏ |sin|`. -/
theorem norm_rvachevFourierProduct_two_pow_mul_half
    (n : ℕ) (y : ℝ) (hy : y ≠ 0) :
    ‖rvachevFourierProduct
        ((2 : ℂ) ^ n * ((y / 2 : ℝ) : ℂ))‖ =
      normalizedDyadicSineProduct n (y - 1) /
          ((2 : ℝ) ^ (n * (n + 1) / 2) *
            (Real.pi * |y|) ^ n) *
        rvachevFixedMantissaTail y := by
  have hyhalf : y / 2 ≠ 0 := div_ne_zero hy (by norm_num)
  rw [norm_rvachevFourierProduct_two_pow_mul n (y / 2) hyhalf,
    prod_abs_sin_shell_half_eq,
    normalizedDyadicSineProduct_sub_one,
    normalizedDyadicSineProduct_eq_two_pow_mul,
    rvachevFixedMantissaTail,
    abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpi : Real.pi * (|y| / 2) = (Real.pi * |y|) / 2 := by ring
  rw [hpi, div_pow]
  field_simp [Real.pi_ne_zero, abs_ne_zero.mpr hy] <;> ring

/-- **Exact fixed-mantissa factorization, zero-valid form.**  For all
`N : ℕ` and all real mantissas `y`,

`2^{(N+1)(N+2)/2} (π|y|)^{N+1} ‖Φ(2ᴺ y)‖
  = Q_{N+1}(y-1) H(y)`.

Unlike the divided identity, this cross-multiplied statement remains valid at
`y = 0` and whenever either side vanishes. -/
theorem norm_rvachevFourierProduct_fixedMantissa_cross (N : ℕ) (y : ℝ) :
    ((2 : ℝ) ^ ((N + 1) * (N + 2) / 2) *
      (Real.pi * |y|) ^ (N + 1)) *
        ‖rvachevFourierProduct ((2 : ℂ) ^ N * (y : ℂ))‖ =
      normalizedDyadicSineProduct (N + 1) (y - 1) *
        rvachevFixedMantissaTail y := by
  have h := norm_rvachevFourierProduct_two_pow_mul_half_cross (N + 1) y
  have harg :
      (2 : ℂ) ^ (N + 1) * (((y / 2 : ℝ) : ℂ)) =
        (2 : ℂ) ^ N * (y : ℂ) := by
    push_cast
    rw [pow_succ]
    ring
  have htri :
      (N + 1) * ((N + 1) + 1) / 2 = (N + 1) * (N + 2) / 2 := by
    simp only [Nat.add_assoc]
  simpa only [harg, htri] using h

/-- **Exact fixed-mantissa factorization, divided form.**  Away from the
single removable denominator point `y = 0`, the total identity reads

`‖Φ(2ᴺ y)‖ = Q_{N+1}(y-1) /
  (2^{(N+1)(N+2)/2} (π|y|)^{N+1}) · H(y)`.

No positivity, upper bound, rationality, or nonvanishing of the orbit product
is required. -/
theorem norm_rvachevFourierProduct_fixedMantissa
    (N : ℕ) (y : ℝ) (hy : y ≠ 0) :
    ‖rvachevFourierProduct ((2 : ℂ) ^ N * (y : ℂ))‖ =
      normalizedDyadicSineProduct (N + 1) (y - 1) /
          ((2 : ℝ) ^ ((N + 1) * (N + 2) / 2) *
            (Real.pi * |y|) ^ (N + 1)) *
        rvachevFixedMantissaTail y := by
  have h :=
    norm_rvachevFourierProduct_two_pow_mul_half (N + 1) y hy
  have harg :
      (2 : ℂ) ^ (N + 1) * (((y / 2 : ℝ) : ℂ)) =
        (2 : ℂ) ^ N * (y : ℂ) := by
    push_cast
    rw [pow_succ]
    ring
  have htri :
      (N + 1) * ((N + 1) + 1) / 2 = (N + 1) * (N + 2) / 2 := by
    simp only [Nat.add_assoc]
  simpa only [harg, htri] using h

/-- **The report's exact ray factorization.**  If `1 < y < 2`, then

`‖Φ(2ᴺ y)‖ = 2^{-N(N+1)/2} (πy)^{-(N+1)} H(y)
  2^{-(N+1)} Q_{N+1}(y-1)`.

The interval assumption identifies `|y|` with `y`; all substantive algebra
already holds under the weaker hypothesis `y ≠ 0` in
`norm_rvachevFourierProduct_fixedMantissa`. -/
theorem norm_rvachevFourierProduct_fixedMantissa_of_mem_Ioo
    (N : ℕ) (y : ℝ) (hy : y ∈ Set.Ioo (1 : ℝ) 2) :
    ‖rvachevFourierProduct ((2 : ℂ) ^ N * (y : ℂ))‖ =
      ((2 : ℝ) ^ (N * (N + 1) / 2))⁻¹ *
        ((Real.pi * y) ^ (N + 1))⁻¹ *
        rvachevFixedMantissaTail y *
        ((2 : ℝ) ^ (N + 1))⁻¹ *
        normalizedDyadicSineProduct (N + 1) (y - 1) := by
  have hypos : 0 < y := lt_trans (by norm_num) hy.1
  have hyne : y ≠ 0 := ne_of_gt hypos
  have hpow :
      (2 : ℝ) ^ ((N + 1) * (N + 2) / 2) =
        (2 : ℝ) ^ (N * (N + 1) / 2) * (2 : ℝ) ^ (N + 1) := by
    calc
      (2 : ℝ) ^ ((N + 1) * (N + 2) / 2) =
          ∏ j ∈ range (N + 1), (2 : ℝ) ^ (j + 1) := by
        have h := prod_range_pow_succ (2 : ℝ) (N + 1)
        have htri :
            (N + 1) * ((N + 1) + 1) / 2 =
              (N + 1) * (N + 2) / 2 := by
          simp only [Nat.add_assoc]
        simpa only [htri] using h.symm
      _ = (∏ j ∈ range N, (2 : ℝ) ^ (j + 1)) *
          (2 : ℝ) ^ (N + 1) := by
        rw [Finset.prod_range_succ]
      _ = (2 : ℝ) ^ (N * (N + 1) / 2) *
          (2 : ℝ) ^ (N + 1) := by
        rw [prod_range_pow_succ]
  rw [norm_rvachevFourierProduct_fixedMantissa N y hyne,
    abs_of_pos hypos, hpow]
  field_simp [Real.pi_ne_zero, hyne]

end Fabius
