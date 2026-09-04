import FabiusFunction.ClassicalHypergeometricLimit
import FabiusFunction.StirlingFirstModH
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Pochhammer splitting, its first parameter derivative, and the Beta integral

This module formalizes the algebraic layer of the Pochhammer section of the
manuscript `Combinatorial_Coefficient_Calculus.tex` (chapter
`ch:merged-gamma-barnes`).  Four manuscript statements are in scope; what is
proved here, and what is deliberately not, is spelled out below.

## Manuscript statements covered

* `thm:merged-pochhammer`.
  - The *splitting rules* `eq:merged-pochhammer-split`
    `(a)_{m+n} = (a)_m (a+m)_n` and
    `a^{\underline{m+n}} = a^{\underline m}(a-m)^{\underline n}` are proved in
    full generality, at the level of polynomial evaluation in an arbitrary
    commutative semiring resp. ring: `ascPochhammer_eval_add_index` and
    `descPochhammer_eval_add_index`, with the `ℕ`-level corollaries
    `ascFactorial_add_index` and `descFactorial_add_index` (the latter is a
    genuine statement about truncated subtraction, not a transport).
  - The *Gamma quotient* `eq:merged-pochhammer-gamma` `(a)_n = Γ(a+n)/Γ(a)` is
    proved as `Gamma_add_natCast_eq_ascPochhammer_mul` (the product form
    `Γ(a+n) = (a)_n Γ(a)`, valid whenever no shifted argument vanishes) and
    `ascPochhammer_eval_eq_Gamma_div` (the quotient form for `Re a > 0`).
* `thm:merged-pochhammer-derivatives`, **case `m = 1` only**.
  `derivative_ascPochhammer` is the hypothesis-free polynomial identity
  `d/dX (X)_n = ∑_{k<n} ∏_{j<n, j≠k} (X+j)`, which is the manuscript's
  "the right side extends polynomially across all removable singularities" for
  `m = 1`.  Away from the zeros it takes the logarithmic form
  `∂_a (a)_n = (a)_n H_n(a)` of `eq:merged-pochhammer-derivatives` with
  `B_1(x_1) = x_1`: `derivative_ascPochhammer_eval` and
  `hasDerivAt_ascPochhammer_eval`.
* `cor:merged-reciprocal-pochhammer`, **case `m = 1` only**.
  `hasDerivAt_inv_ascPochhammer_eval`: `∂_a (a)_n⁻¹ = -H_n(a)/(a)_n`, the
  alternating sign `(-1)^m` of `eq:merged-reciprocal-pochhammer` at `m = 1`.
* `prop:merged-beta-integral`.  Mathlib already has the induction of the
  manuscript proof in `Complex.betaIntegral_eval_nat_add_one_right`; the
  content added here is the Pochhammer normal form
  `betaIntegral_eq_factorial_div_ascPochhammer` and the literal manuscript
  statement `integral_cpow_mul_one_sub_natPow`
  `∫₀¹ t^{a-1}(1-t)^n dt = n!/(a)_{n+1}` with a natural-number power on
  `(1-t)`.

The shifted generalized harmonic sums `eq:merged-shifted-harmonic`
`H_n^{(r)}(a) = ∑_{j<n} (a+j)^{-r}` are named `shiftedHarmonic`.

## Deliberately not proved

* **The general-`m` Bell-polynomial derivative formulas.**  Both
  `eq:merged-pochhammer-derivatives` and `eq:merged-reciprocal-pochhammer` for
  `m ≥ 2` need the exponential Faà di Bruno formula for the `m`-th derivative
  of `exp ∘ L`, which the corpus does not have: `Fabius.completeBellPolynomial`
  (in `MomentCumulantAlgebra`) and its partition expansion
  `Fabius.completeBellPolynomial_eq_partitionExpSum` (in `ExponentialBell`) are
  purely formal-power-series objects, with no bridge to iterated derivatives of
  a real or complex function.  Only `m = 1` is proved here, where the Bell
  polynomial degenerates to `B_1(x_1) = x_1` and no Faà di Bruno is needed.
* **The sign-flip identity `eq:merged-bell-sign-flip`**
  `B_m(-x_1, x_2, …, (-1)^m x_m) = (-1)^m B_m(x_1, …, x_m)`, which is the
  manuscript's bridge from `thm:merged-pochhammer-derivatives` to
  `cor:merged-reciprocal-pochhammer`.  It is genuinely algebraic and is
  reachable from `Fabius.partitionExpSum` (each weighted partition contributes
  `(-1)^{∑ j m_j} = (-1)^m`), but it is only useful together with the
  general-`m` derivative formula above, so it is left out with it.
* **The binomial series `eq:merged-binomial-series`** `(1-z)^{-a} = ∑ (a)_n z^n/n!`.
  Mathlib has it as `Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero`,
  with coefficients written as `Ring.choose (a+n-1) n`; converting those to
  `(a)_n/n!` is a `Ring.choose`/`descPochhammer.smeval` computation that is
  orthogonal to everything else in this file.
* **Chu--Vandermonde `eq:merged-vandermonde-rising`** is not restated: the
  binomial-convolution identity is already available in falling-factorial form
  as `Fabius.descPochhammer_eval_add` (in `FallingFactorialSeries`), proved
  there from the formal binomial series rather than from the analytic argument
  of the manuscript.
-/

set_option autoImplicit false

open Finset MeasureTheory Polynomial
open scoped BigOperators Nat

namespace Fabius

/-! ### Shifted generalized harmonic sums -/

/-- The shifted generalized harmonic sum `H_n^{(r)}(a) = ∑_{j<n} (a+j)^{-r}`
of `eq:merged-shifted-harmonic`.  For `r = 1` this is the `H_n(a)` that appears
as the first Bell argument in the parameter derivatives of a Pochhammer
symbol. -/
def shiftedHarmonic {K : Type*} [DivisionRing K] (a : K) (n r : ℕ) : K :=
  ∑ j ∈ Finset.range n, ((a + (j : K)) ^ r)⁻¹

/-- `H_n(a) = H_n^{(1)}(a) = ∑_{j<n} (a+j)⁻¹`. -/
theorem shiftedHarmonic_one {K : Type*} [DivisionRing K] (a : K) (n : ℕ) :
    shiftedHarmonic a n 1 = ∑ j ∈ Finset.range n, (a + (j : K))⁻¹ := by
  simp [shiftedHarmonic]

/-! ### Pochhammer splitting -/

/-- **Rising Pochhammer splitting**, the first half of
`eq:merged-pochhammer-split`: `(a)_{m+n} = (a)_m (a+m)_n`.  The product
`a(a+1)⋯(a+m+n-1)` breaks after its `m`-th factor. -/
theorem ascPochhammer_eval_add_index {S : Type*} [CommSemiring S] (m n : ℕ) (a : S) :
    (ascPochhammer S (m + n)).eval a
      = (ascPochhammer S m).eval a * (ascPochhammer S n).eval (a + (m : S)) := by
  have h : ∏ j ∈ Finset.range n, (a + ((m + j : ℕ) : S))
      = ∏ j ∈ Finset.range n, ((a + (m : S)) + (j : S)) :=
    Finset.prod_congr rfl fun j _ => by push_cast; ring
  simp only [ascPochhammer_eval_eq_prod_range, Finset.prod_range_add]
  exact congrArg (fun t : S => (∏ j ∈ Finset.range m, (a + (j : S))) * t) h

/-- **Falling Pochhammer splitting**, the second half of
`eq:merged-pochhammer-split`:
`a^{\underline{m+n}} = a^{\underline m} (a-m)^{\underline n}`.  This is the
same identity read in the opposite direction. -/
theorem descPochhammer_eval_add_index {R : Type*} [CommRing R] (m n : ℕ) (a : R) :
    (descPochhammer R (m + n)).eval a
      = (descPochhammer R m).eval a * (descPochhammer R n).eval (a - (m : R)) := by
  have h : ∏ j ∈ Finset.range n, (a - ((m + j : ℕ) : R))
      = ∏ j ∈ Finset.range n, ((a - (m : R)) - (j : R)) :=
    Finset.prod_congr rfl fun j _ => by push_cast; ring
  simp only [descPochhammer_eval_eq_prod_range, Finset.prod_range_add]
  exact congrArg (fun t : R => (∏ j ∈ Finset.range m, (a - (j : R))) * t) h

/-- The splitting rule for `Nat.ascFactorial`:
`a^{(m+n)} = a^{(m)} (a+m)^{(n)}`. -/
theorem ascFactorial_add_index (a m n : ℕ) :
    a.ascFactorial (m + n) = a.ascFactorial m * (a + m).ascFactorial n := by
  have h := ascPochhammer_eval_add_index (S := ℕ) m n a
  simpa only [ascPochhammer_nat_eq_ascFactorial, Nat.cast_id] using h

/-- The splitting rule for `Nat.descFactorial`:
`a^{\underline{m+n}} = a^{\underline m} (a-m)^{\underline n}`.  Unlike
`descPochhammer_eval_add_index` this is a statement about truncated
subtraction, and it holds unconditionally: when `m > a` both sides vanish. -/
theorem descFactorial_add_index (a m n : ℕ) :
    a.descFactorial (m + n) = a.descFactorial m * (a - m).descFactorial n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [← add_assoc, Nat.descFactorial_succ, ih, Nat.descFactorial_succ, Nat.sub_sub]
      ring

/-! ### The first parameter derivative -/

/-- The polynomial derivative of a rising factorial:
`d/dX (X)_n = ∑_{k<n} ∏_{j<n, j ≠ k} (X + j)`.  This is the `m = 1` case of
`eq:merged-pochhammer-derivatives` in the form that carries no hypotheses and
therefore "extends polynomially across all removable singularities". -/
theorem derivative_ascPochhammer (S : Type*) [CommSemiring S] (n : ℕ) :
    Polynomial.derivative (ascPochhammer S n)
      = ∑ k ∈ Finset.range n,
          ∏ j ∈ (Finset.range n).erase k, (Polynomial.X + Polynomial.C (j : S)) := by
  rw [ascPochhammer_eq_prod_range, Polynomial.derivative_prod_finset]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp

/-- **First parameter derivative of a rising factorial**, the `m = 1` case of
`eq:merged-pochhammer-derivatives`: away from the zeros of `(a)_n`,
`∂_a (a)_n = (a)_n H_n(a)`.  The complete Bell polynomial of
`eq:merged-pochhammer-derivatives` degenerates to `B_1(x_1) = x_1` here. -/
theorem derivative_ascPochhammer_eval {K : Type*} [Field K] {n : ℕ} {a : K}
    (ha : ∀ j : ℕ, j < n → a + (j : K) ≠ 0) :
    (Polynomial.derivative (ascPochhammer K n)).eval a
      = (ascPochhammer K n).eval a * shiftedHarmonic a n 1 := by
  rw [shiftedHarmonic_one, ascPochhammer_eval_eq_prod_range n a, Finset.mul_sum,
    derivative_ascPochhammer]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_prod, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : a + (k : K) ≠ 0 := ha k (Finset.mem_range.mp hk)
  have hmul : (a + (k : K)) * ∏ j ∈ (Finset.range n).erase k, (a + (j : K))
      = ∏ j ∈ Finset.range n, (a + (j : K)) :=
    Finset.mul_prod_erase (Finset.range n) (fun j : ℕ => a + (j : K)) hk
  rw [← hmul, mul_right_comm, mul_inv_cancel₀ hk', one_mul]

/-- The analytic form of `derivative_ascPochhammer_eval`: the rising factorial
`x ↦ (x)_n` is differentiable with derivative `(a)_n H_n(a)` at every point
where no factor vanishes. -/
theorem hasDerivAt_ascPochhammer_eval {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ} {a : 𝕜}
    (ha : ∀ j : ℕ, j < n → a + (j : 𝕜) ≠ 0) :
    HasDerivAt (fun x : 𝕜 => (ascPochhammer 𝕜 n).eval x)
      ((ascPochhammer 𝕜 n).eval a * shiftedHarmonic a n 1) a := by
  have h := (ascPochhammer 𝕜 n).hasDerivAt a
  rwa [derivative_ascPochhammer_eval ha] at h

/-- **Derivative of a reciprocal Pochhammer symbol**, the `m = 1` case of
`eq:merged-reciprocal-pochhammer`: `∂_a (a)_n⁻¹ = -H_n(a)/(a)_n`.  Compared
with `hasDerivAt_ascPochhammer_eval` the derivative array is multiplied by
`(-1)^m` at `m = 1`, exactly as `cor:merged-reciprocal-pochhammer` asserts. -/
theorem hasDerivAt_inv_ascPochhammer_eval {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ} {a : 𝕜}
    (ha : ∀ j : ℕ, j < n → a + (j : 𝕜) ≠ 0) :
    HasDerivAt (fun x : 𝕜 => ((ascPochhammer 𝕜 n).eval x)⁻¹)
      (-(shiftedHarmonic a n 1 / (ascPochhammer 𝕜 n).eval a)) a := by
  have hP : (ascPochhammer 𝕜 n).eval a ≠ 0 := ascPochhammer_eval_ne_zero ha
  have h : HasDerivAt (fun x : 𝕜 => ((ascPochhammer 𝕜 n).eval x)⁻¹)
      (-((ascPochhammer 𝕜 n).eval a * shiftedHarmonic a n 1)
        / (ascPochhammer 𝕜 n).eval a ^ 2) a :=
    (hasDerivAt_ascPochhammer_eval ha).inv hP
  have hdiv : -((ascPochhammer 𝕜 n).eval a * shiftedHarmonic a n 1)
        / (ascPochhammer 𝕜 n).eval a ^ 2
      = -(shiftedHarmonic a n 1 / (ascPochhammer 𝕜 n).eval a) := by
    rw [neg_div, neg_inj, div_eq_div_iff (pow_ne_zero 2 hP) hP]
    ring
  rwa [hdiv] at h

/-! ### The Gamma quotient -/

/-- **The Gamma recursion in Pochhammer form**, the product half of
`eq:merged-pochhammer-gamma`: `Γ(a+n) = (a)_n Γ(a)` whenever none of
`a, a+1, …, a+n-1` vanishes.  This is the iteration of `Γ(w+1) = w Γ(w)` from
the manuscript proof. -/
theorem Gamma_add_natCast_eq_ascPochhammer_mul {a : ℂ} (n : ℕ)
    (ha : ∀ j : ℕ, j < n → a + (j : ℂ) ≠ 0) :
    Complex.Gamma (a + (n : ℂ)) = (ascPochhammer ℂ n).eval a * Complex.Gamma a := by
  revert ha
  induction n with
  | zero => intro _; simp
  | succ n ih =>
      intro ha
      have hn : a + (n : ℂ) ≠ 0 := ha n (by omega)
      have hrec := ih fun j hj => ha j (by omega)
      have hcast : a + ((n + 1 : ℕ) : ℂ) = a + (n : ℂ) + 1 := by push_cast; ring
      rw [hcast, Complex.Gamma_add_one _ hn, hrec, ascPochhammer_succ_eval]
      ring

/-- **The Gamma quotient** `eq:merged-pochhammer-gamma`:
`(a)_n = Γ(a+n)/Γ(a)` for `Re a > 0`, where the denominator is nonzero and
every shifted argument `a+j` has positive real part. -/
theorem ascPochhammer_eval_eq_Gamma_div {a : ℂ} (ha : 0 < a.re) (n : ℕ) :
    (ascPochhammer ℂ n).eval a = Complex.Gamma (a + (n : ℂ)) / Complex.Gamma a := by
  have hne : ∀ j : ℕ, j < n → a + (j : ℂ) ≠ 0 := by
    intro j _ h
    have hre : a.re + (j : ℝ) = 0 := by
      have h2 := congrArg Complex.re h
      simpa using h2
    have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
    linarith
  have hG : Complex.Gamma a ≠ 0 := Complex.Gamma_ne_zero_of_re_pos ha
  rw [Gamma_add_natCast_eq_ascPochhammer_mul n hne, mul_div_assoc, div_self hG, mul_one]

/-! ### The Beta integral with an integer parameter -/

/-- **Beta integral with an integer parameter**, `prop:merged-beta-integral` in
Pochhammer normal form: `Β(a, n+1) = n!/(a)_{n+1}` for `Re a > 0`.  The
induction of the manuscript proof is Mathlib's
`Complex.betaIntegral_eval_nat_add_one_right`; what is added here is the
identification of its denominator `∏_{j≤n}(a+j)` with `(a)_{n+1}`. -/
theorem betaIntegral_eq_factorial_div_ascPochhammer {a : ℂ} (ha : 0 < a.re) (n : ℕ) :
    Complex.betaIntegral a ((n : ℂ) + 1) = (n ! : ℂ) / (ascPochhammer ℂ (n + 1)).eval a := by
  rw [Complex.betaIntegral_eval_nat_add_one_right ha n,
    ascPochhammer_eval_eq_prod_range (n + 1) a]

/-- `prop:merged-beta-integral` verbatim, `eq:merged-beta-integral`:
`∫₀¹ t^{a-1}(1-t)^n dt = n!/(a)_{n+1}` for `Re a > 0` and every integer
`n ≥ 0`, with an honest natural-number power on `(1-t)` rather than the
complex power of `Complex.betaIntegral`. -/
theorem integral_cpow_mul_one_sub_natPow {a : ℂ} (ha : 0 < a.re) (n : ℕ) :
    (∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ n)
      = (n ! : ℂ) / (ascPochhammer ℂ (n + 1)).eval a := by
  have hfun : (fun t : ℝ => (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ n)
      = fun t : ℝ => (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (((n : ℂ) + 1) - 1) := by
    funext t
    rw [show ((n : ℂ) + 1) - 1 = (n : ℂ) by ring, Complex.cpow_natCast]
  rw [hfun]
  exact betaIntegral_eq_factorial_div_ascPochhammer ha n

end Fabius
