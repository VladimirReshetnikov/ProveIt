import FabiusFunction.ThueMorseMoments
import FabiusFunction.ThueMorsePrefix
import FabiusFunction.MomentCumulantAlgebra
import FabiusFunction.SaddleLogProductAlgebra
import Mathlib.NumberTheory.Bernoulli
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# Bell-polynomial moments of Thue–Morse blocks

The atlas's `p1:thm:Bell-moments`: with `M_{m,n} = ∑_{k < 2^m} ε_k k^n`,
for `m ≥ 1` and `r ≥ 0`,

`M_{m,m+r} = (-1)^m 2^{C(m,2)} (m+r)!/r! · B_r(κ_1^{(m)}, …, κ_r^{(m)})`,

where `B_r` is the complete exponential Bell polynomial and the cumulants
are `κ_1^{(m)} = (2^m - 1)/2`,
`κ_{2ℓ}^{(m)} = B_{2ℓ}/(2ℓ) · (4^{ℓm} - 1)/(4^ℓ - 1)`, `κ_{2ℓ+1}^{(m)} = 0`
(`ℓ ≥ 1`).  The statement holds for `m = 0` too.

## Method

Everything is formal power-series algebra over `ℚ`.  The corpus already
has the exponential generating function of the block, `∑ ε_k e^{kt} =
∏_{j<m} (1 - e^{2^j t}) = (-1)^m t^m ∏_j F_j` with `F_j = ∑_q (2^j)^{q+1}
t^q/(q+1)!` (`prod_one_sub_exp_two_pow`), the EGF dictionary
`[t^n] ∑ ε_k e^{kt} = M_{m,n}/n!`, and the recursive formal logarithm
`logCoeff` with its rescaling law and product law.  What is new here:

* **the Bernoulli logarithm of `(e^y - 1)/y`**,
  `[y^n] log((e^y-1)/y) = B'_n/(n·n!)` for `n ≥ 1` (with `B'_n = (-1)^n B_n`
  the second Bernoulli numbers), proved by uniqueness of the recursive
  logarithm from the identity `y G' = (B'(y) - 1) G`, itself a consequence
  of Mathlib's `B'(y)(e^y - 1) = y e^y`;
* **the logarithm of a finite product** of unit series is the sum of the
  logarithms (`logCoeff_prod_range`);
* the assembly: `F_j = 2^j · G(2^j y)`, so `∏_j F_j = 2^{C(m,2)} exp(Λ_m)`
  with `Λ_m = ∑_j log G(2^j y)`, whose coefficients are the cumulants
  divided by factorials; the complete Bell polynomial is, by definition
  in `MomentCumulantAlgebra`, `r!` times the `r`-th coefficient of
  `exp(∑ κ_n y^n/n!)`.

## Main declarations

* `bernoulliLogCoefficient`, `expm1Div_logCoeff_eq_bernoulli` — **the
  Bernoulli logarithm of `(e^y - 1)/y`**.
* `logCoeff_prod_range` — logarithm of a finite product.
* `blockCumulant m n` — `κ_n^{(m)}`, with `blockCumulant_one`,
  `blockCumulant_even`, `blockCumulant_odd`.
* `thueMorsePowerSum_eq_completeBellPolynomial` — **`p1:eq:Bell-moments`**.
* `thueMorsePowerSum_self'` — the `r = 0` case `M_{m,m} = (-1)^m 2^{C(m,2)} m!`,
  recovered as a corollary.
-/

set_option autoImplicit false

namespace Fabius

open Finset PowerSeries SaddleExpansion

/-! ## The Bernoulli logarithm of `(e^y - 1)/y` -/

/-- Coefficients of `G(y) = (e^y - 1)/y`: `1/(q+1)!`. -/
def expm1DivCoefficient (q : ℕ) : ℚ := 1 / ((q + 1).factorial : ℚ)

@[simp] theorem expm1DivCoefficient_zero : expm1DivCoefficient 0 = 1 := by
  simp [expm1DivCoefficient]

/-- The Bernoulli candidate for `[y^n] log((e^y-1)/y)`: `B'_n/(n·n!)` for
`n ≥ 1`, and `0` at `n = 0`. -/
def bernoulliLogCoefficient (n : ℕ) : ℚ :=
  if n = 0 then 0 else bernoulli' n / (n * n.factorial)

@[simp] theorem bernoulliLogCoefficient_zero : bernoulliLogCoefficient 0 = 0 := by
  simp [bernoulliLogCoefficient]

theorem coeff_bernoulli'PowerSeries_rat (n : ℕ) :
    coeff n (bernoulli'PowerSeries ℚ) = bernoulli' n / n.factorial := by
  simp [bernoulli'PowerSeries, coeff_mk]

/-- `y · G(y) = e^y - 1`. -/
theorem X_mul_massSeries_expm1Div :
    (X : PowerSeries ℚ) * massSeries expm1DivCoefficient = exp ℚ - 1 := by
  ext n
  rcases n with _ | n
  · simp [coeff_zero_X_mul, coeff_exp, massSeries, expm1DivCoefficient]
  · rw [coeff_succ_X_mul, coeff_massSeries, map_sub, coeff_exp, coeff_one,
      if_neg (Nat.succ_ne_zero n)]
    simp [expm1DivCoefficient]

/-- `y · G'(y) = e^y - G(y)`. -/
theorem X_mul_derivative_massSeries_expm1Div :
    (X : PowerSeries ℚ) * d⁄dX ℚ (massSeries expm1DivCoefficient)
      = exp ℚ - massSeries expm1DivCoefficient := by
  ext n
  rcases n with _ | n
  · simp [coeff_zero_X_mul, coeff_exp, massSeries, expm1DivCoefficient]
  · rw [coeff_succ_X_mul, coeff_derivative, coeff_massSeries, map_sub, coeff_exp, coeff_massSeries]
    simp only [expm1DivCoefficient, Algebra.algebraMap_self, RingHom.id_apply]
    rw [Nat.factorial_succ (n + 1)]
    push_cast
    have hne : ((n + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    field_simp
    ring

/-- `y · Λ'(y) = B'(y) - 1` for the Bernoulli candidate `Λ`. -/
theorem X_mul_derivative_bernoulliLog :
    (X : PowerSeries ℚ) * d⁄dX ℚ (mk bernoulliLogCoefficient) = bernoulli'PowerSeries ℚ - 1 := by
  ext n
  rcases n with _ | n
  · simp [coeff_zero_X_mul, bernoulli'PowerSeries, bernoulli'_zero]
  · rw [coeff_succ_X_mul, coeff_derivative, coeff_mk, map_sub, coeff_bernoulli'PowerSeries_rat,
      coeff_one, if_neg (Nat.succ_ne_zero n)]
    simp only [bernoulliLogCoefficient, Nat.succ_ne_zero, if_false]
    have hne : ((n + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hfac : ((n + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    push_cast
    field_simp
    ring

/-- `B'(y) · G(y) = e^y`. -/
theorem bernoulli'PowerSeries_mul_massSeries_expm1Div :
    bernoulli'PowerSeries ℚ * massSeries expm1DivCoefficient = exp ℚ := by
  have h := bernoulli'PowerSeries_mul_exp_sub_one ℚ
  rw [← X_mul_massSeries_expm1Div] at h
  have h' : (X : PowerSeries ℚ) * (bernoulli'PowerSeries ℚ * massSeries expm1DivCoefficient)
      = X * exp ℚ := by
    rw [← h]
    ring
  exact mul_left_cancel₀ X_ne_zero h'

/-- `G · Λ' = G'`: the hypothesis of the uniqueness theorem for the recursive
logarithm. -/
theorem expm1Div_mul_derivative_bernoulliLog :
    massSeries expm1DivCoefficient * d⁄dX ℚ (mk bernoulliLogCoefficient)
      = d⁄dX ℚ (massSeries expm1DivCoefficient) := by
  have h1 := X_mul_derivative_bernoulliLog
  have h2 := X_mul_derivative_massSeries_expm1Div
  have h3 := bernoulli'PowerSeries_mul_massSeries_expm1Div
  have h : (X : PowerSeries ℚ) * (massSeries expm1DivCoefficient *
      d⁄dX ℚ (mk bernoulliLogCoefficient))
      = X * d⁄dX ℚ (massSeries expm1DivCoefficient) := by
    linear_combination massSeries expm1DivCoefficient * h1 - h2 + h3
  exact mul_left_cancel₀ X_ne_zero h

/-- **The Bernoulli logarithm of `(e^y - 1)/y`**:
`[y^n] log((e^y - 1)/y) = B'_n / (n · n!)` for `n ≥ 1`, i.e. `1/2` at
`n = 1`, `B_{2ℓ}/(2ℓ (2ℓ)!)` at `n = 2ℓ`, and `0` at odd `n ≥ 3`. -/
theorem expm1Div_logCoeff_eq_bernoulli (n : ℕ) :
    logCoeff expm1DivCoefficient n = bernoulliLogCoefficient n := by
  have hzero : constantCoeff (mk bernoulliLogCoefficient : PowerSeries ℚ) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]
    simp
  have h := coeff_eq_logCoeff_of_derivative_mul_eq expm1DivCoefficient expm1DivCoefficient_zero
    expm1Div_mul_derivative_bernoulliLog hzero n
  rw [coeff_mk] at h
  exact h.symm

/-! ## Logarithm of a finite product -/

/-- The coefficient family of a power series. -/
noncomputable def coeffFamily (F : PowerSeries ℚ) : ℕ → ℚ := fun n => coeff n F

@[simp] theorem massSeries_coeffFamily (F : PowerSeries ℚ) : massSeries (coeffFamily F) = F := by
  ext n
  simp [coeffFamily, coeff_massSeries]

@[simp] theorem coeffFamily_massSeries (a : ℕ → ℚ) : coeffFamily (massSeries a) = a := by
  funext n
  simp [coeffFamily, coeff_massSeries]

/-- The logarithm of a product of two unit series is the sum of the logarithms. -/
theorem logCoeff_coeffFamily_mul (A B : PowerSeries ℚ) (hA : coeff 0 A = 1) (hB : coeff 0 B = 1)
    (n : ℕ) :
    logCoeff (coeffFamily (A * B)) n = logCoeff (coeffFamily A) n + logCoeff (coeffFamily B) n := by
  have h : coeffFamily (A * B) = coefficientConvolution (coeffFamily A) (coeffFamily B) := by
    have := massSeries_coefficientConvolution (coeffFamily A) (coeffFamily B)
    rw [massSeries_coeffFamily, massSeries_coeffFamily] at this
    rw [← this, coeffFamily_massSeries]
  rw [h]
  exact logCoeff_coefficientConvolution (coeffFamily A) (coeffFamily B) hA hB n

/-- **Logarithm of a finite product.**  For unit series `A_j`,
`log ∏_{j<m} A_j = ∑_{j<m} log A_j` coefficientwise. -/
theorem logCoeff_prod_range (A : ℕ → PowerSeries ℚ) (hA : ∀ j, coeff 0 (A j) = 1) (m n : ℕ) :
    logCoeff (coeffFamily (∏ j ∈ range m, A j)) n = ∑ j ∈ range m, logCoeff (coeffFamily (A j)) n := by
  induction m with
  | zero =>
      simp only [prod_range_zero, sum_range_zero]
      have h1 : coeffFamily (1 : PowerSeries ℚ) = fun k => if k = 0 then 1 else 0 := by
        funext k
        simp [coeffFamily, coeff_one]
      rw [h1]
      rcases n with _ | n
      · simp
      · rw [logCoeff_congr_of_pos (b := fun _ => 0) (n + 1) (fun j hj _ => by simp [hj.ne'])]
        induction n with
        | zero => simp
        | succ k ih =>
            rw [logCoeff_succ]
            simp
  | succ m ih =>
      have h0 : coeff 0 (∏ j ∈ range m, A j) = 1 := by
        rw [coeff_zero_eq_constantCoeff_apply, map_prod]
        refine prod_eq_one fun j _ => ?_
        rw [← coeff_zero_eq_constantCoeff_apply]
        exact hA j
      rw [prod_range_succ, sum_range_succ, logCoeff_coeffFamily_mul _ _ h0 (hA m), ih]

/-! ## The block cumulants -/

/-- The block cumulant `κ_n^{(m)} = n! · ∑_{j<m} (2^j)^n · [y^n] log((e^y-1)/y)`. -/
def blockCumulant (m n : ℕ) : ℚ :=
  (n.factorial : ℚ) * ∑ j ∈ range m, ((2 : ℚ) ^ j) ^ n * bernoulliLogCoefficient n

@[simp] theorem blockCumulant_zero (m : ℕ) : blockCumulant m 0 = 0 := by
  simp [blockCumulant]

/-- `κ_1^{(m)} = (2^m - 1)/2`. -/
theorem blockCumulant_one (m : ℕ) : blockCumulant m 1 = ((2 : ℚ) ^ m - 1) / 2 := by
  simp only [blockCumulant, bernoulliLogCoefficient, Nat.factorial_one, Nat.cast_one, one_mul,
    pow_one, one_ne_zero, if_false, bernoulli'_one]
  rw [← sum_mul, geom_sum_eq (by norm_num : (2 : ℚ) ≠ 1)]
  norm_num
  ring

/-- `κ_{2ℓ}^{(m)} = B_{2ℓ}/(2ℓ) · (4^{ℓm} - 1)/(4^ℓ - 1)` for `ℓ ≥ 1`. -/
theorem blockCumulant_even (m ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    blockCumulant m (2 * ℓ)
      = bernoulli (2 * ℓ) / (2 * ℓ) * (((4 : ℚ) ^ (ℓ * m) - 1) / ((4 : ℚ) ^ ℓ - 1)) := by
  have hne : (2 * ℓ : ℕ) ≠ 0 := by omega
  simp only [blockCumulant, bernoulliLogCoefficient, hne, if_false]
  rw [bernoulli_eq_bernoulli'_of_ne_one (by omega)]
  have hpow : ∀ j : ℕ, ((2 : ℚ) ^ j) ^ (2 * ℓ) = ((4 : ℚ) ^ ℓ) ^ j := by
    intro j
    rw [← pow_mul, show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
    ring_nf
  simp_rw [hpow]
  have h4' : (4 : ℚ) ^ ℓ ≠ 1 := by
    have : (1 : ℚ) < 4 ^ ℓ := one_lt_pow₀ (by norm_num) (by omega)
    exact ne_of_gt this
  rw [← sum_mul, geom_sum_eq h4' m, ← pow_mul]
  have hfac : ((2 * ℓ).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h4 : (4 : ℚ) ^ ℓ - 1 ≠ 0 := sub_ne_zero.mpr h4'
  have hl : (2 * ℓ : ℚ) ≠ 0 := by
    have : (0 : ℚ) < ℓ := by exact_mod_cast hℓ
    linarith
  push_cast
  field_simp
  ring

/-- `κ_{2ℓ+1}^{(m)} = 0` for `ℓ ≥ 1`. -/
theorem blockCumulant_odd (m ℓ : ℕ) (hℓ : 1 ≤ ℓ) : blockCumulant m (2 * ℓ + 1) = 0 := by
  simp only [blockCumulant, bernoulliLogCoefficient, Nat.succ_ne_zero, if_false]
  rw [bernoulli'_eq_zero_of_odd ⟨ℓ, rfl⟩ (by omega)]
  simp

/-! ## The Bell-polynomial moment formula -/

/-- The cofactor series `F_j = ∑_q (2^j)^{q+1} y^q/(q+1)!` is `2^j · G(2^j y)`. -/
theorem cofactor_eq_C_mul_massSeries (j : ℕ) :
    (mk fun q => ((2 : ℚ) ^ j) ^ (q + 1) / (q + 1).factorial : PowerSeries ℚ)
      = C ((2 : ℚ) ^ j) * massSeries (fun q => ((2 : ℚ) ^ j) ^ q * expm1DivCoefficient q) := by
  ext q
  rw [coeff_mk, coeff_C_mul, coeff_massSeries, expm1DivCoefficient, pow_succ]
  ring

/-- The block sum as a dyadic power sum over `range`. -/
theorem thueMorsePowerSum_eq_sum_range (m d : ℕ) :
    thueMorsePowerSum m d = ∑ n ∈ range (2 ^ m), (thueMorseSign n : ℚ) * (n : ℚ) ^ d := by
  unfold thueMorsePowerSum
  exact Fin.sum_univ_eq_sum_range (fun n => (thueMorseSign n : ℚ) * (n : ℚ) ^ d) (2 ^ m)

/-- **The Bell-polynomial moment formula** (`p1:eq:Bell-moments`): for every
`m` and `r`,

`M_{m,m+r} = (-1)^m · 2^{0+1+⋯+(m-1)} · (m+r)!/r! · B_r(κ^{(m)})`,

with `B_r` the complete exponential Bell polynomial of the block cumulants. -/
theorem thueMorsePowerSum_eq_completeBellPolynomial (m r : ℕ) :
    thueMorsePowerSum m (m + r)
      = (-1) ^ m * 2 ^ (∑ i ∈ range m, i) * ((m + r).factorial / r.factorial) *
          completeBellPolynomial (blockCumulant m) r := by
  -- the EGF of the block
  have hegf := coeff_sum_thueMorseSign_exp_pow m (m + r)
  rw [← prod_one_sub_pow_eq_sum_thueMorseSign (exp ℚ) m, prod_one_sub_exp_two_pow] at hegf
  simp_rw [cofactor_eq_C_mul_massSeries] at hegf
  rw [prod_mul_distrib, ← map_prod C, prod_pow_eq_pow_sum] at hegf
  -- the product of the rescaled `G`'s is the exponential of the summed logarithms
  set P : PowerSeries ℚ :=
    ∏ j ∈ range m, massSeries (fun q => ((2 : ℚ) ^ j) ^ q * expm1DivCoefficient q) with hP
  have hP0 : coeffFamily P 0 = 1 := by
    simp only [coeffFamily, hP, coeff_zero_eq_constantCoeff_apply, map_prod]
    refine prod_eq_one fun j _ => ?_
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_massSeries]
    simp
  have hlog : ∀ n, logCoeff (coeffFamily P) n
      = ∑ j ∈ range m, ((2 : ℚ) ^ j) ^ n * bernoulliLogCoefficient n := by
    intro n
    rw [hP, logCoeff_prod_range _ (fun j => by rw [coeff_massSeries]; simp)]
    refine sum_congr rfl fun j _ => ?_
    rw [coeffFamily_massSeries, logCoeff_rescale, expm1Div_logCoeff_eq_bernoulli]
  -- Bell polynomial of the block cumulants = `r!` times the `r`-th coefficient of `P`
  have hbell : completeBellPolynomial (blockCumulant m) r = (r.factorial : ℚ) * coeff r P := by
    have hnorm : factorialNormalize (blockCumulant m) = logCoeff (coeffFamily P) := by
      funext n
      rw [factorialNormalize, blockCumulant, hlog, smul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (by exact_mod_cast (Nat.factorial_pos n).ne'), one_mul]
    rw [completeBellPolynomial, hnorm, factorialDenormalize, expCoeff_logCoeff _ hP0,
      smul_eq_mul, coeffFamily]
  -- read off the coefficient
  rw [thueMorsePowerSum_eq_sum_range]
  set c : ℚ := 2 ^ (∑ i ∈ range m, i) with hc
  have hcoeff : ∀ c' : ℚ, coeff (m + r) ((-1 : PowerSeries ℚ) ^ m * X ^ m * (C c' * P))
      = (-1) ^ m * c' * coeff r P := by
    intro c'
    have hC : ((-1 : PowerSeries ℚ) ^ m * X ^ m * (C c' * P))
        = C ((-1) ^ m * c') * (X ^ m * P) := by
      rw [map_mul, map_pow, map_neg, map_one]
      ring
    rw [hC, coeff_C_mul, show m + r = r + m by ring, coeff_X_pow_mul]
  rw [← map_pow, hcoeff] at hegf
  have hfac : ((m + r).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hr : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hsum : ∑ n ∈ range (2 ^ m), (thueMorseSign n : ℚ) * (n : ℚ) ^ (m + r)
      = ((m + r).factorial : ℚ) * ((-1) ^ m * c * coeff r P) := by
    rw [eq_div_iff hfac] at hegf
    rw [← hegf]
    ring
  have hr' : (((m + r).factorial : ℚ) / r.factorial) * ((r.factorial : ℚ) * coeff r P)
      = ((m + r).factorial : ℚ) * coeff r P := by
    field_simp
  rw [hsum, hbell, mul_assoc ((-1 : ℚ) ^ m * c), hr']
  ring

/-- The `r = 0` case: `M_{m,m} = (-1)^m 2^{C(m,2)} m!`, recovering
`thueMorsePowerSum_self` with the Gauss-sum exponent. -/
theorem thueMorsePowerSum_self' (m : ℕ) :
    thueMorsePowerSum m m = (-1) ^ m * 2 ^ (∑ i ∈ range m, i) * m.factorial := by
  have h := thueMorsePowerSum_eq_completeBellPolynomial m 0
  rw [add_zero] at h
  rw [h, completeBellPolynomial, factorialDenormalize]
  simp

end Fabius
