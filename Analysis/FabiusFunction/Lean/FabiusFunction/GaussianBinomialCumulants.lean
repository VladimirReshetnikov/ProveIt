import FabiusFunction.QCatalan
import FabiusFunction.GaussianBinomialAtOne
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.LinearCombination

/-!
# Mean and variance of the Gaussian coefficient as a probability generating function

For `k ≤ n`, `[n,k]_q / C(n,k)` is the probability generating function of the inversion
number of a uniformly random binary word with `k` ones and `n-k` zeros (equivalently, of the
area of a random lattice path, or the size of a random partition in a `k × (n-k)` box).  Its mean
and variance are

`E X = k(n-k)/2`, `Var X = k(n-k)(n+1)/12`.

We define the mean and variance functionals of a polynomial `P` with `P(1) ≠ 0`,

`meanAtOne P = P'(1)/P(1)`, `varAtOne P = P''(1)/P(1) + P'(1)/P(1) - (P'(1)/P(1))^2`,

show that both are additive on products (they are the first two cumulants), compute them for the
`q`-integers `[m]_X = 1 + X + ⋯ + X^{m-1}` (the uniform distribution on `{0, …, m-1}`:
mean `(m-1)/2`, variance `(m^2-1)/12`), and use the factorization
`[n,k]_X ∏_{j<k} [j+1]_X = ∏_{j<k} [n-k+1+j]_X` to add up the cumulants.
The derivative formula `([n,k]_X)'(1) = k(n-k)/2 · C(n,k)` is the
division-free palindromicity mean
`two_mul_derivative_gaussianBinomial_eval_one` of
`GaussianBinomialPalindromic` halved.

## Main declarations

* `meanAtOne`, `varAtOne`, `meanAtOne_mul`, `varAtOne_mul`, `meanAtOne_prod`, `varAtOne_prod`.
* `meanAtOne_qInt_X`, `varAtOne_qInt_X`.
* `gaussianBinomial_X_mul_prod_qInt`: the factorization into `q`-integers.
* `meanAtOne_gaussianBinomial_X`, `varAtOne_gaussianBinomial_X`,
  `eval_one_derivative_gaussianBinomial_X`.
-/

set_option autoImplicit false

open Polynomial Finset

namespace Fabius

variable {K : Type*} [Field K]

/-- The mean `P'(1)/P(1)` of the distribution with probability generating function `P/P(1)`. -/
noncomputable def meanAtOne (P : K[X]) : K := (derivative P).eval 1 / P.eval 1

/-- The variance `P''(1)/P(1) + P'(1)/P(1) - (P'(1)/P(1))^2` of the distribution with
probability generating function `P/P(1)`. -/
noncomputable def varAtOne (P : K[X]) : K :=
  (derivative (derivative P)).eval 1 / P.eval 1 + meanAtOne P - meanAtOne P ^ 2

/-- The constant polynomial `1` is the generating function of the point mass at `0`, whose mean
is `0`.  This is the base case of `meanAtOne_prod`. -/
@[simp] theorem meanAtOne_one : meanAtOne (1 : K[X]) = 0 := by simp [meanAtOne]

/-- The point mass at `0`, with generating function `1`, has variance `0`.  This is the base case
of `varAtOne_prod`. -/
@[simp] theorem varAtOne_one : varAtOne (1 : K[X]) = 0 := by simp [varAtOne]

/-- The mean is additive on products (independent sums). -/
theorem meanAtOne_mul {A B : K[X]} (hA : A.eval 1 ≠ 0) (hB : B.eval 1 ≠ 0) :
    meanAtOne (A * B) = meanAtOne A + meanAtOne B := by
  simp only [meanAtOne, derivative_mul, eval_add, eval_mul]
  field_simp

/-- The variance is additive on products (independent sums). -/
theorem varAtOne_mul {A B : K[X]} (hA : A.eval 1 ≠ 0) (hB : B.eval 1 ≠ 0) :
    varAtOne (A * B) = varAtOne A + varAtOne B := by
  simp only [varAtOne, meanAtOne, derivative_mul, derivative_add, eval_add, eval_mul]
  field_simp
  ring

/-- The mean of a finite product is the sum of the means: a product of generating functions is the
generating function of a sum of independent variables, and the first cumulant is additive.  The
hypothesis `hf` keeps every factor — hence the whole product — nonvanishing at `1`. -/
theorem meanAtOne_prod {ι : Type*} (s : Finset ι) (f : ι → K[X])
    (hf : ∀ i ∈ s, (f i).eval 1 ≠ 0) :
    meanAtOne (∏ i ∈ s, f i) = ∑ i ∈ s, meanAtOne (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, (f i).eval 1 ≠ 0 := fun i hi => hf i (mem_insert_of_mem hi)
    rw [prod_insert ha, sum_insert ha, meanAtOne_mul (hf a (mem_insert_self a s)) ?_, ih hs]
    rw [eval_prod]
    exact prod_ne_zero_iff.mpr hs

/-- The variance of a finite product is the sum of the variances: the second cumulant is additive
over independent summands.  As in `meanAtOne_prod`, `hf` keeps each factor nonzero at `1`. -/
theorem varAtOne_prod {ι : Type*} (s : Finset ι) (f : ι → K[X])
    (hf : ∀ i ∈ s, (f i).eval 1 ≠ 0) :
    varAtOne (∏ i ∈ s, f i) = ∑ i ∈ s, varAtOne (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, (f i).eval 1 ≠ 0 := fun i hi => hf i (mem_insert_of_mem hi)
    rw [prod_insert ha, sum_insert ha, varAtOne_mul (hf a (mem_insert_self a s)) ?_, ih hs]
    rw [eval_prod]
    exact prod_ne_zero_iff.mpr hs

/-! ### The `q`-integers -/

/-- `(X^n)'(1) = n`: the contribution of the monomial `X^n` to the first moment of a generating
function, the summand used to build `eval_one_derivative_qInt_X` term by term. -/
theorem eval_one_derivative_X_pow (n : ℕ) :
    (derivative ((X : K[X]) ^ n)).eval 1 = n := by
  rw [derivative_X_pow]
  simp

/-- `(X^n)''(1) = n(n-1)`, the second falling factorial of `n`.  This is the summand behind
`eval_one_derivative_derivative_qInt_X`; the case `n = 0` is treated separately because
`derivative_X_pow` there produces the exponent `0 - 1` in `ℕ`. -/
theorem eval_one_derivative_derivative_X_pow (n : ℕ) :
    (derivative (derivative ((X : K[X]) ^ n))).eval 1 = (n : K) * ((n : K) - 1) := by
  rcases n with _ | k
  · simp
  · rw [derivative_X_pow, Nat.add_sub_cancel, derivative_mul, derivative_C, zero_mul, zero_add,
      derivative_X_pow]
    simp only [eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
    push_cast
    ring

/-- `[m]_X` evaluated at `X = 1` is `m`: the `q`-integer `1 + X + ⋯ + X^{m-1}` degenerates to the
ordinary integer `m`, so it is the total mass of the uniform distribution on `{0, …, m-1}`. -/
theorem eval_one_qInt_X (m : ℕ) : (qInt (X : K[X]) m).eval 1 = m := by
  simp [qInt, eval_finsetSum]

section CharZeroField

variable [CharZero K]

/-- `([m]_X)'(1) = 0 + 1 + ⋯ + (m-1) = m(m-1)/2`, the unnormalized first moment of the uniform
distribution on `{0, …, m-1}`. -/
theorem eval_one_derivative_qInt_X (m : ℕ) :
    (derivative (qInt (X : K[X]) m)).eval 1 = (m : K) * ((m : K) - 1) / 2 := by
  induction m with
  | zero => simp [qInt]
  | succ m ih =>
    rw [qInt_succ, derivative_add, eval_add, ih, eval_one_derivative_X_pow]
    push_cast
    ring

/-- `([m]_X)''(1) = ∑_{i<m} i(i-1) = m(m-1)(m-2)/3`, the unnormalized second factorial moment of
the uniform distribution on `{0, …, m-1}` (equal to `2·C(m,3)`). -/
theorem eval_one_derivative_derivative_qInt_X (m : ℕ) :
    (derivative (derivative (qInt (X : K[X]) m))).eval 1 =
      (m : K) * ((m : K) - 1) * ((m : K) - 2) / 3 := by
  induction m with
  | zero => simp [qInt]
  | succ m ih =>
    rw [qInt_succ, derivative_add, derivative_add, eval_add, ih,
      eval_one_derivative_derivative_X_pow]
    push_cast
    ring

/-- The `q`-integer `[m]_X` is the generating function of the uniform distribution on
`{0, …, m-1}`: its mean is `(m-1)/2`. -/
theorem meanAtOne_qInt_X {m : ℕ} (hm : 0 < m) :
    meanAtOne (qInt (X : K[X]) m) = ((m : K) - 1) / 2 := by
  rw [meanAtOne, eval_one_derivative_qInt_X, eval_one_qInt_X]
  have : (m : K) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

/-- The variance of the uniform distribution on `{0, …, m-1}` is `(m^2-1)/12`. -/
theorem varAtOne_qInt_X {m : ℕ} (hm : 0 < m) :
    varAtOne (qInt (X : K[X]) m) = ((m : K) ^ 2 - 1) / 12 := by
  rw [varAtOne, meanAtOne_qInt_X hm, eval_one_derivative_derivative_qInt_X, eval_one_qInt_X]
  have : (m : K) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
  ring

end CharZeroField

/-! ### The Gaussian coefficient -/

/-- `1 - X^{m+1} = (1 - X) [m+1]_X`: the telescoping identity that lets a factor `1 - X^{j+1}` of a
finite `q`-Pochhammer product be traded for the `q`-integer `[j+1]_X` times `1 - X`.  It is
`X_sub_one_mul_qInt` with both sides negated. -/
theorem one_sub_X_pow_succ_eq (m : ℕ) :
    (1 : K[X]) - X ^ (m + 1) = (1 - X) * qInt (X : K[X]) (m + 1) := by
  linear_combination X_sub_one_mul_qInt (R := K) m

/-- **Factorization into `q`-integers**: `[n,k]_X · ∏_{j<k} [j+1]_X = ∏_{j<k} [n-k+1+j]_X`. -/
theorem gaussianBinomial_X_mul_prod_qInt {n k : ℕ} (hk : k ≤ n) :
    gaussianBinomial (X : K[X]) n k * ∏ j ∈ range k, qInt (X : K[X]) (j + 1) =
      ∏ j ∈ range k, qInt (X : K[X]) (n - k + 1 + j) := by
  have h := finiteQPochhammerIn_self_mul_gaussianBinomial (X : K[X]) hk
  have h1 : finiteQPochhammerIn (X : K[X]) X k =
      (1 - X) ^ k * ∏ j ∈ range k, qInt (X : K[X]) (j + 1) := by
    rw [finiteQPochhammerIn, ← card_range k, ← prod_const, card_range, ← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    rw [← pow_succ', one_sub_X_pow_succ_eq]
  have h2 : finiteQPochhammerIn ((X : K[X]) ^ (n - k + 1)) X k =
      (1 - X) ^ k * ∏ j ∈ range k, qInt (X : K[X]) (n - k + 1 + j) := by
    rw [finiteQPochhammerIn, ← card_range k, ← prod_const, card_range, ← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    rw [← pow_add, show n - k + 1 + j = n - k + j + 1 by ring, one_sub_X_pow_succ_eq]
  rw [h1, h2, mul_assoc] at h
  have hne : ((1 : K[X]) - X) ^ k ≠ 0 := by
    refine pow_ne_zero _ fun h0 => ?_
    have := congrArg (eval 0) h0
    simp at this
  rw [mul_comm]
  exact mul_left_cancel₀ hne h

/-- The Gaussian coefficient specializes at `q = 1` to the ordinary binomial coefficient:
`[n,k]_X |_{X=1} = C(n,k)`.  This is the normalizing constant `P(1)` that turns `[n,k]_X` into the
probability generating function of the inversion number. -/
theorem eval_one_gaussianBinomial_X (n k : ℕ) :
    (gaussianBinomial (X : K[X]) n k).eval 1 = (n.choose k : K) := by
  have := map_gaussianBinomial (evalRingHom (1 : K)) (X : K[X]) n k
  rw [coe_evalRingHom, eval_X, gaussianBinomial_one_eq_natCast_choose] at this
  exact this

/-- Telescoping the means across the factorization `[n,k]_X ∏_{j<k} [j+1]_X = ∏_{j<k} [m+1+j]_X`
with `m = n - k`: the uniform means `(m+j)/2` on the right minus the uniform means `j/2` on the
left sum to `km/2`, which is `E X = k(n-k)/2`. -/
theorem sum_mean_diff (m k : ℕ) :
    ∑ j ∈ range k, (((m + 1 + j : ℕ) : K) - 1) / 2 -
      ∑ j ∈ range k, (((j + 1 : ℕ) : K) - 1) / 2 = (k : K) * m / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, sum_range_succ]
    push_cast at ih ⊢
    linear_combination ih

/-- The variance counterpart of `sum_mean_diff`: with `m = n - k`, the uniform variances
`((m+1+j)^2-1)/12` on the right of the `q`-integer factorization minus the variances
`((j+1)^2-1)/12` on the left sum to `km(k+m+1)/12`, which is `Var X = k(n-k)(n+1)/12`. -/
theorem sum_var_diff (m k : ℕ) :
    ∑ j ∈ range k, (((m + 1 + j : ℕ) : K) ^ 2 - 1) / 12 -
      ∑ j ∈ range k, (((j + 1 : ℕ) : K) ^ 2 - 1) / 12 =
      (k : K) * m * ((k : K) + m + 1) / 12 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, sum_range_succ]
    push_cast at ih ⊢
    linear_combination ih

section CharZeroField

variable [CharZero K]

/-- The cumulant skeleton shared by the mean and the variance.  Any
functional `F` that is additive on products of polynomials nonvanishing
at `1` — both for a pair and for a finite product — satisfies, along the
factorization `gaussianBinomial_X_mul_prod_qInt`,

`F [n,k]_X + ∑_{j<k} F [j+1]_X = ∑_{j<k} F [n-k+1+j]_X`.

The nonvanishing side conditions are discharged once and for all
here. -/
private theorem cumulant_gaussianBinomial_X (F : K[X] → K)
    (Fmul : ∀ {A B : K[X]}, A.eval 1 ≠ 0 → B.eval 1 ≠ 0 →
      F (A * B) = F A + F B)
    (Fprod : ∀ (s : Finset ℕ) (f : ℕ → K[X]),
      (∀ i ∈ s, (f i).eval 1 ≠ 0) → F (∏ i ∈ s, f i) = ∑ i ∈ s, F (f i))
    {n k : ℕ} (hk : k ≤ n) :
    F (gaussianBinomial (X : K[X]) n k) +
        ∑ j ∈ range k, F (qInt (X : K[X]) (j + 1)) =
      ∑ j ∈ range k, F (qInt (X : K[X]) (n - k + 1 + j)) := by
  have hG : (gaussianBinomial (X : K[X]) n k).eval 1 ≠ 0 := by
    rw [eval_one_gaussianBinomial_X]
    exact_mod_cast (Nat.choose_pos hk).ne'
  have hL : ∀ j ∈ range k, (qInt (X : K[X]) (j + 1)).eval 1 ≠ 0 :=
    fun j _ => by
      rw [eval_one_qInt_X]
      exact_mod_cast Nat.succ_ne_zero j
  have hR : ∀ j ∈ range k,
      (qInt (X : K[X]) (n - k + 1 + j)).eval 1 ≠ 0 :=
    fun j _ => by
      rw [eval_one_qInt_X]
      exact_mod_cast (by omega : n - k + 1 + j ≠ 0)
  have hPL : (∏ j ∈ range k, qInt (X : K[X]) (j + 1)).eval 1 ≠ 0 := by
    rw [eval_prod]
    exact prod_ne_zero_iff.mpr hL
  have key := congrArg F (gaussianBinomial_X_mul_prod_qInt (K := K) hk)
  rwa [Fmul hG hPL, Fprod _ _ hL, Fprod _ _ hR] at key

/-- **Mean of the inversion distribution**: `E X = k(n-k)/2`, i.e.
`([n,k]_X)'(1) / C(n,k) = k(n-k)/2`. -/
theorem meanAtOne_gaussianBinomial_X {n k : ℕ} (hk : k ≤ n) :
    meanAtOne (gaussianBinomial (X : K[X]) n k) = (k : K) * ((n : K) - k) / 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have key := cumulant_gaussianBinomial_X (meanAtOne : K[X] → K)
    (fun hA hB => meanAtOne_mul hA hB) (fun s f hf => meanAtOne_prod s f hf) hk
  rw [Nat.add_sub_cancel_left,
    sum_congr rfl fun j _ => meanAtOne_qInt_X (K := K) (Nat.succ_pos j),
    sum_congr rfl fun j _ =>
      meanAtOne_qInt_X (K := K) (by omega : 0 < m + 1 + j)] at key
  have hs := sum_mean_diff (K := K) m k
  push_cast at key hs ⊢
  linear_combination key + hs

/-- **Variance of the inversion distribution**: `Var X = k(n-k)(n+1)/12`. -/
theorem varAtOne_gaussianBinomial_X {n k : ℕ} (hk : k ≤ n) :
    varAtOne (gaussianBinomial (X : K[X]) n k) = (k : K) * ((n : K) - k) * ((n : K) + 1) / 12 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have key := cumulant_gaussianBinomial_X (varAtOne : K[X] → K)
    (fun hA hB => varAtOne_mul hA hB) (fun s f hf => varAtOne_prod s f hf) hk
  rw [Nat.add_sub_cancel_left,
    sum_congr rfl fun j _ => varAtOne_qInt_X (K := K) (Nat.succ_pos j),
    sum_congr rfl fun j _ =>
      varAtOne_qInt_X (K := K) (by omega : 0 < m + 1 + j)] at key
  have hs := sum_var_diff (K := K) m k
  push_cast at key hs ⊢
  linear_combination key + hs

/-- The derivative formula `d/dq [n,k]_q |_{q=1} = k(n-k)/2 · C(n,k)`: the
division-free palindromicity mean `2 · ([n,k]_X)'(1) = k(n-k) · C(n,k)`
(`two_mul_derivative_gaussianBinomial_eval_one`) halved. -/
theorem eval_one_derivative_gaussianBinomial_X {n k : ℕ} (hk : k ≤ n) :
    (derivative (gaussianBinomial (X : K[X]) n k)).eval 1 =
      (k : K) * ((n : K) - k) / 2 * (n.choose k : K) := by
  have h := two_mul_derivative_gaussianBinomial_eval_one (R := K) hk
  rw [Nat.cast_mul, Nat.cast_sub hk] at h
  rw [div_mul_eq_mul_div, eq_div_iff (two_ne_zero : (2 : K) ≠ 0)]
  linear_combination h

end CharZeroField

end Fabius
