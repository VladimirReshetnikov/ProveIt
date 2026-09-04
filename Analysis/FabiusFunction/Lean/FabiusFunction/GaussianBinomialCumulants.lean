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

## Main declarations

* `meanAtOne`, `varAtOne`, `meanAtOne_mul`, `varAtOne_mul`, `meanAtOne_prod`, `varAtOne_prod`.
* `meanAtOne_qInt_X`, `varAtOne_qInt_X`.
* `gaussianBinomial_X_mul_prod_qInt`: the factorization into `q`-integers.
* `meanAtOne_gaussianBinomial_X`, `varAtOne_gaussianBinomial_X`,
  `eval_one_derivative_gaussianBinomial_X`,
  `eval_one_derivative_derivative_gaussianBinomial_X`.
* `twelve_mul_secondMoment_gaussianBinomial_eval_one` and
  `twelve_mul_varianceNumerator_gaussianBinomial_eval_one`: division-free second-moment and
  variance-numerator identities.
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

/-- **Mean of the inversion distribution**: `E X = k(n-k)/2`, i.e.
`([n,k]_X)'(1) / C(n,k) = k(n-k)/2`. -/
theorem meanAtOne_gaussianBinomial_X {n k : ℕ} (hk : k ≤ n) :
    meanAtOne (gaussianBinomial (X : K[X]) n k) = (k : K) * ((n : K) - k) / 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hprod := gaussianBinomial_X_mul_prod_qInt (K := K) hk
  rw [Nat.add_sub_cancel_left] at hprod
  have hG : (gaussianBinomial (X : K[X]) (k + m) k).eval 1 ≠ 0 := by
    rw [eval_one_gaussianBinomial_X]; exact_mod_cast (Nat.choose_pos hk).ne'
  have hL : ∀ j ∈ range k, (qInt (X : K[X]) (j + 1)).eval 1 ≠ 0 := fun j _ => by
    rw [eval_one_qInt_X]; exact_mod_cast Nat.succ_ne_zero j
  have hR : ∀ j ∈ range k, (qInt (X : K[X]) (m + 1 + j)).eval 1 ≠ 0 := fun j _ => by
    rw [eval_one_qInt_X]; exact_mod_cast (by omega : m + 1 + j ≠ 0)
  have hPL : (∏ j ∈ range k, qInt (X : K[X]) (j + 1)).eval 1 ≠ 0 := by
    rw [eval_prod]; exact prod_ne_zero_iff.mpr hL
  have key := congrArg meanAtOne hprod
  rw [meanAtOne_mul hG hPL, meanAtOne_prod _ _ hL, meanAtOne_prod _ _ hR,
    sum_congr rfl fun j _ => meanAtOne_qInt_X (K := K) (Nat.succ_pos j),
    sum_congr rfl fun j _ => meanAtOne_qInt_X (K := K) (by omega : 0 < m + 1 + j)] at key
  have hs := sum_mean_diff (K := K) m k
  push_cast at key hs ⊢
  linear_combination key + hs

/-- **Variance of the inversion distribution**: `Var X = k(n-k)(n+1)/12`. -/
theorem varAtOne_gaussianBinomial_X {n k : ℕ} (hk : k ≤ n) :
    varAtOne (gaussianBinomial (X : K[X]) n k) = (k : K) * ((n : K) - k) * ((n : K) + 1) / 12 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hprod := gaussianBinomial_X_mul_prod_qInt (K := K) hk
  rw [Nat.add_sub_cancel_left] at hprod
  have hG : (gaussianBinomial (X : K[X]) (k + m) k).eval 1 ≠ 0 := by
    rw [eval_one_gaussianBinomial_X]; exact_mod_cast (Nat.choose_pos hk).ne'
  have hL : ∀ j ∈ range k, (qInt (X : K[X]) (j + 1)).eval 1 ≠ 0 := fun j _ => by
    rw [eval_one_qInt_X]; exact_mod_cast Nat.succ_ne_zero j
  have hR : ∀ j ∈ range k, (qInt (X : K[X]) (m + 1 + j)).eval 1 ≠ 0 := fun j _ => by
    rw [eval_one_qInt_X]; exact_mod_cast (by omega : m + 1 + j ≠ 0)
  have hPL : (∏ j ∈ range k, qInt (X : K[X]) (j + 1)).eval 1 ≠ 0 := by
    rw [eval_prod]; exact prod_ne_zero_iff.mpr hL
  have key := congrArg varAtOne hprod
  rw [varAtOne_mul hG hPL, varAtOne_prod _ _ hL, varAtOne_prod _ _ hR,
    sum_congr rfl fun j _ => varAtOne_qInt_X (K := K) (Nat.succ_pos j),
    sum_congr rfl fun j _ => varAtOne_qInt_X (K := K) (by omega : 0 < m + 1 + j)] at key
  have hs := sum_var_diff (K := K) m k
  push_cast at key hs ⊢
  linear_combination key + hs

/-- The derivative formula `d/dq [n,k]_q |_{q=1} = k(n-k)/2 · C(n,k)`. -/
theorem eval_one_derivative_gaussianBinomial_X {n k : ℕ} (hk : k ≤ n) :
    (derivative (gaussianBinomial (X : K[X]) n k)).eval 1 =
      (k : K) * ((n : K) - k) / 2 * (n.choose k : K) := by
  have h := meanAtOne_gaussianBinomial_X (K := K) hk
  rw [meanAtOne, eval_one_gaussianBinomial_X] at h
  have hc : (n.choose k : K) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  rw [div_eq_iff hc] at h
  exact h

/-- The second derivative of the universal Gaussian coefficient at one:
`[n,k]''_1 = C(n,k) k(n-k) (3k(n-k)+n-5) / 12`.

Equivalently, this is the unnormalized second falling-factorial moment of the inversion
distribution.  The division-free companion below remains valid in arbitrary characteristic. -/
theorem eval_one_derivative_derivative_gaussianBinomial_X {n k : ℕ} (hk : k ≤ n) :
    (derivative (derivative (gaussianBinomial (X : K[X]) n k))).eval 1 =
      (k : K) * ((n : K) - k) *
        (3 * ((k : K) * ((n : K) - k)) + (n : K) - 5) / 12 * (n.choose k : K) := by
  have h := varAtOne_gaussianBinomial_X (K := K) hk
  rw [varAtOne, meanAtOne_gaussianBinomial_X (K := K) hk,
    eval_one_gaussianBinomial_X] at h
  have hc : (n.choose k : K) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  field_simp [hc] at h ⊢
  linear_combination (1 / 4) * h

end CharZeroField

/-! ### Division-free second moments -/

private theorem map_eval_one_derivative_gaussianBinomial
    {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S) (n k : ℕ) :
    φ ((derivative (gaussianBinomial (X : R[X]) n k)).eval 1) =
      (derivative (gaussianBinomial (X : S[X]) n k)).eval 1 := by
  rw [← eval_map_apply, ← derivative_map]
  have hmap : (gaussianBinomial (X : R[X]) n k).map φ =
      gaussianBinomial (X : S[X]) n k := by
    simpa only [Polynomial.coe_mapRingHom, Polynomial.map_X] using
      map_gaussianBinomial (Polynomial.mapRingHom φ) (X : R[X]) n k
  rw [hmap, map_one]

private theorem map_eval_one_derivative_derivative_gaussianBinomial
    {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S) (n k : ℕ) :
    φ ((derivative (derivative (gaussianBinomial (X : R[X]) n k))).eval 1) =
      (derivative (derivative (gaussianBinomial (X : S[X]) n k))).eval 1 := by
  rw [← eval_map_apply, ← derivative_map, ← derivative_map]
  have hmap : (gaussianBinomial (X : R[X]) n k).map φ =
      gaussianBinomial (X : S[X]) n k := by
    simpa only [Polynomial.coe_mapRingHom, Polynomial.map_X] using
      map_gaussianBinomial (Polynomial.mapRingHom φ) (X : R[X]) n k
  rw [hmap, map_one]

private theorem twelve_mul_secondMoment_gaussianBinomial_eval_one_nat (n k : ℕ) :
    12 * ((derivative (derivative (gaussianBinomial (X : ℕ[X]) n k))).eval 1 +
      (derivative (gaussianBinomial (X : ℕ[X]) n k)).eval 1) =
      k * (n - k) * (3 * (k * (n - k)) + n + 1) * n.choose k := by
  by_cases hk : k ≤ n
  · apply Nat.cast_injective (R := ℚ)
    push_cast [hk]
    have h₂ :
        (((derivative (derivative (gaussianBinomial (X : ℕ[X]) n k))).eval 1 : ℕ) : ℚ) =
          (derivative (derivative (gaussianBinomial (X : ℚ[X]) n k))).eval 1 :=
      map_eval_one_derivative_derivative_gaussianBinomial (Nat.castRingHom ℚ) n k
    have h₁ : (((derivative (gaussianBinomial (X : ℕ[X]) n k)).eval 1 : ℕ) : ℚ) =
        (derivative (gaussianBinomial (X : ℚ[X]) n k)).eval 1 :=
      map_eval_one_derivative_gaussianBinomial (Nat.castRingHom ℚ) n k
    rw [h₂, h₁, eval_one_derivative_derivative_gaussianBinomial_X hk,
      eval_one_derivative_gaussianBinomial_X hk]
    ring
  · have hlt : n < k := Nat.lt_of_not_ge hk
    simp [gaussianBinomial_eq_zero_of_lt (X : ℕ[X]) hlt,
      Nat.choose_eq_zero_of_lt hlt]

/-- **Division-free raw second moment of a Gaussian row.**  If
`P = [n,k]_X`, `D = k(n-k)`, and `C = C(n,k)`, then
`12 (P''(1) + P'(1)) = D (3D+n+1) C`.

The left side is twelve times the unnormalized coefficient moment `∑ j² c_j`.  The theorem is
total in `n,k`: above the Gaussian row both sides vanish by zero extension.  It uses no division,
nonvanishing, or characteristic assumption. -/
theorem twelve_mul_secondMoment_gaussianBinomial_eval_one
    {R : Type*} [CommSemiring R] (n k : ℕ) :
    12 * ((derivative (derivative (gaussianBinomial (X : R[X]) n k))).eval 1 +
      (derivative (gaussianBinomial (X : R[X]) n k)).eval 1) =
      ((k * (n - k) : ℕ) : R) *
        (3 * ((k * (n - k) : ℕ) : R) + (n : R) + 1) * (n.choose k : R) := by
  have h := congrArg (Nat.castRingHom R)
    (twelve_mul_secondMoment_gaussianBinomial_eval_one_nat n k)
  push_cast at h
  have h₂ :
      (((derivative (derivative (gaussianBinomial (X : ℕ[X]) n k))).eval 1 : ℕ) : R) =
        (derivative (derivative (gaussianBinomial (X : R[X]) n k))).eval 1 :=
    map_eval_one_derivative_derivative_gaussianBinomial (Nat.castRingHom R) n k
  have h₁ : (((derivative (gaussianBinomial (X : ℕ[X]) n k)).eval 1 : ℕ) : R) =
      (derivative (gaussianBinomial (X : R[X]) n k)).eval 1 :=
    map_eval_one_derivative_gaussianBinomial (Nat.castRingHom R) n k
  rw [h₂, h₁] at h
  simpa only [Nat.cast_mul] using h

/-- **Division-free variance numerator of a Gaussian row.**  If
`P = [n,k]_X`, `D = k(n-k)`, and `C = C(n,k)`, then
`12 C (P''(1)+P'(1)) = 12 P'(1)^2 + D(n+1)C^2`.

Over a characteristic-zero field, for `k ≤ n`, division by `12 C²` makes this exactly
`Var(X) = D(n+1)/12`.  In the displayed cleared form it is total in `n,k`, includes the zero and
diagonal rows, and remains valid in arbitrary characteristic. -/
theorem twelve_mul_varianceNumerator_gaussianBinomial_eval_one
    {R : Type*} [CommSemiring R] (n k : ℕ) :
    12 * (n.choose k : R) *
        ((derivative (derivative (gaussianBinomial (X : R[X]) n k))).eval 1 +
          (derivative (gaussianBinomial (X : R[X]) n k)).eval 1) =
      12 * (derivative (gaussianBinomial (X : R[X]) n k)).eval 1 ^ 2 +
        ((k * (n - k) : ℕ) : R) * ((n : R) + 1) * (n.choose k : R) ^ 2 := by
  by_cases hk : k ≤ n
  · let P : R[X] := gaussianBinomial (X : R[X]) n k
    let d : R := ((k * (n - k) : ℕ) : R)
    let c : R := (n.choose k : R)
    let m₁ : R := (derivative P).eval 1
    let m₂ : R := (derivative (derivative P)).eval 1 + (derivative P).eval 1
    have hs : 12 * m₂ = d * (3 * d + (n : R) + 1) * c := by
      simpa [P, d, c, m₂] using
        twelve_mul_secondMoment_gaussianBinomial_eval_one (R := R) n k
    have hm : 2 * m₁ = d * c := by
      simpa [P, d, c, m₁] using
        two_mul_derivative_gaussianBinomial_eval_one (R := R) hk
    have hm_sq : 12 * m₁ ^ 2 = 3 * d ^ 2 * c ^ 2 := by
      calc
        12 * m₁ ^ 2 = 3 * (2 * m₁) ^ 2 := by ring
        _ = 3 * (d * c) ^ 2 := by rw [hm]
        _ = 3 * d ^ 2 * c ^ 2 := by ring
    change 12 * c * m₂ = 12 * m₁ ^ 2 + d * ((n : R) + 1) * c ^ 2
    calc
      12 * c * m₂ = c * (12 * m₂) := by ring
      _ = c * (d * (3 * d + (n : R) + 1) * c) := by rw [hs]
      _ = 3 * d ^ 2 * c ^ 2 + d * ((n : R) + 1) * c ^ 2 := by ring
      _ = 12 * m₁ ^ 2 + d * ((n : R) + 1) * c ^ 2 := by rw [hm_sq]
  · have hlt : n < k := Nat.lt_of_not_ge hk
    simp [gaussianBinomial_eq_zero_of_lt (X : R[X]) hlt,
      Nat.choose_eq_zero_of_lt hlt]

end Fabius
