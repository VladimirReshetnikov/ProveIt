import FabiusFunction.BellComposition
import FabiusFunction.StirlingFirstReverse

/-!
# The diamond power and the partial Bell polynomials

The source's diamond product of two sequences vanishing at `0`,

`(x ⋄ y)_n = ∑_{j=1}^{n-1} C(n,j) x_j y_{n-j}`,

is the binomial convolution `Bell.binomialConv` with its two extreme terms dropped; they
vanish anyway because `x_0 = y_0 = 0` (`binomialConv_eq_sum_Ico`).  So the diamond power is
the binomial-convolution power, and its terms are the partial Bell polynomials up to `k!`:

`(x^{k⋄})_n = k! B_{n,k}(x)`   (`diamondPow_apply`).

The source proves this by comparing exponential generating functions, and so does this
module: the exponential generating function of a binomial convolution is a product
(`Bell.egfA_mul`), hence the one of `x^{k⋄}` is `X(t)^k`, and the corpus already reads the
coefficients of `X(t)^k` off the partial Bell polynomials (`bellWeightSeries_pow`).

The base case is the unit sequence `δ_{n,0}` rather than `x` itself, which makes `k = 0` the
identity and gives `B_{n,0} = δ_{n,0}`; for `k ≥ 1` this agrees with the `k`-fold product in
the source, since `x^{1⋄} = x` (`diamondPow_one`).

## Main results

* `binomialConv_eq_sum_Ico`, the source's index range.
* `diamondPow`, `diamondPow_one`, `egfA_diamondPow`.
* `diamondPow_apply`, `partialBell_eq_diamondPow_div`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section Conv

variable {R : Type*} [CommSemiring R]

/-- **The source's index range:** for sequences vanishing at `0`, the binomial convolution
is the sum over `1 ≤ j ≤ n-1`, because the terms `j = 0` and `j = n` vanish. -/
theorem binomialConv_eq_sum_Ico (x y : ℕ → R) (hx : x 0 = 0) (hy : y 0 = 0) (n : ℕ) :
    Bell.binomialConv x y n = ∑ j ∈ Finset.Ico 1 n, (n.choose j : R) * (x j * y (n - j)) := by
  rw [Bell.binomialConv_eq_sum_range]
  cases n with
  | zero => simp [hx]
  | succ m =>
    rw [Finset.sum_range_succ, Nat.sub_self, hy, mul_zero, mul_zero, add_zero,
      Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1)
        (by omega : 1 ≤ m + 1), Nat.Ico_zero_eq_range, Finset.sum_range_one, hx,
      Nat.choose_zero_right, zero_mul, mul_zero, zero_add]

end Conv

section Power

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The `k`-fold diamond power, with the unit sequence `δ_{n,0}` as the empty product. -/
noncomputable def diamondPow (x : ℕ → A) : ℕ → (ℕ → A)
  | 0 => Bell.unitSeq A
  | k + 1 => Bell.binomialConv x (diamondPow x k)

@[simp] theorem diamondPow_zero (x : ℕ → A) : diamondPow A x 0 = Bell.unitSeq A := rfl

theorem diamondPow_succ (x : ℕ → A) (k : ℕ) :
    diamondPow A x (k + 1) = Bell.binomialConv x (diamondPow A x k) := rfl

/-- `x^{1⋄} = x`, so for `k ≥ 1` this is the source's `k`-fold product. -/
@[simp] theorem diamondPow_one (x : ℕ → A) : diamondPow A x 1 = x := by
  funext n
  rw [diamondPow_succ, diamondPow_zero, Bell.binomialConv_eq_sum_range,
    Finset.sum_eq_single_of_mem n (Finset.self_mem_range_succ n)]
  · rw [Nat.sub_self, Bell.unitSeq_zero, mul_one, Nat.choose_self, Nat.cast_one, one_mul]
  · intro b hb hbn
    obtain ⟨c, hc⟩ : ∃ c, n - b = c + 1 := ⟨n - b - 1, by
      have := Finset.mem_range.mp hb
      omega⟩
    rw [hc, Bell.unitSeq_succ, mul_zero, mul_zero]

/-- The exponential generating function of the unit sequence is `1`. -/
theorem egfA_unitSeq : egfA A (Bell.unitSeq A) = 1 := by
  refine PowerSeries.ext fun n => ?_
  cases n with
  | zero =>
    rw [coeff_egfA, Bell.unitSeq_zero, coeff_zero_eq_constantCoeff, map_one, mul_one,
      Nat.factorial_zero, Nat.cast_one, div_one, map_one]
  | succ m =>
    rw [coeff_egfA, Bell.unitSeq_succ, mul_zero, coeff_one, if_neg (Nat.succ_ne_zero m)]

/-- Scalars pass through the exponential generating function. -/
theorem smul_egfA (c : A) (f : ℕ → A) : c • egfA A f = egfA A fun n => c * f n := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_smul, coeff_egfA, coeff_egfA, smul_eq_mul]
  ring

/-- **The generating function of the diamond power** is the `k`-th power of the
generating function. -/
theorem egfA_diamondPow (x : ℕ → A) (k : ℕ) : egfA A (diamondPow A x k) = egfA A x ^ k := by
  induction k with
  | zero => rw [diamondPow_zero, egfA_unitSeq, pow_zero]
  | succ k ih => rw [diamondPow_succ, ← egfA_mul, ih, pow_succ, mul_comm]

/-- For a sequence vanishing at `0` the exponential generating function is the Bell weight
series. -/
theorem egfA_eq_bellWeightSeries (x : ℕ → A) (hx : x 0 = 0) :
    egfA A x = bellWeightSeries A x := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_egfA, bellWeightSeries, coeff_egfA]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [if_pos rfl, hx]
  · rw [if_neg hn]

/-- **The diamond power is the partial Bell polynomial:** `(x^{k⋄})_n = k! B_{n,k}(x)`. -/
theorem diamondPow_apply (x : ℕ → A) (hx : x 0 = 0) (k n : ℕ) :
    diamondPow A x k n = (k.factorial : A) * partialBell x n k := by
  have h : egfA A (diamondPow A x k) = egfA A fun n => (k.factorial : A) * partialBell x n k := by
    rw [egfA_diamondPow, egfA_eq_bellWeightSeries A x hx, bellWeightSeries_pow, smul_egfA]
  exact congrFun (seq_eq_of_egfA_eq A h) n

/-- The source's form: `B_{n,k}(x) = (x^{k⋄})_n / k!`, stated as a product with the
inverse of `k!` in the `ℚ`-algebra. -/
theorem partialBell_eq_diamondPow_div (x : ℕ → A) (hx : x 0 = 0) (k n : ℕ) :
    partialBell x n k = algebraMap ℚ A (1 / k.factorial) * diamondPow A x k n := by
  have hk : ((k.factorial : ℚ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hinv : algebraMap ℚ A (1 / k.factorial) * (k.factorial : A) = 1 := by
    rw [← map_natCast (algebraMap ℚ A) k.factorial, ← map_mul, one_div,
      inv_mul_cancel₀ hk, map_one]
  calc partialBell x n k = 1 * partialBell x n k := (one_mul _).symm
    _ = algebraMap ℚ A (1 / k.factorial) * ((k.factorial : A) * partialBell x n k) := by
        rw [← hinv]; ring
    _ = algebraMap ℚ A (1 / k.factorial) * diamondPow A x k n := by rw [diamondPow_apply A x hx]

end Power

end Fabius
