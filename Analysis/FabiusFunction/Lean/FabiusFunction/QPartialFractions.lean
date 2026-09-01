import FabiusFunction.FiniteQBinomialCore
import FabiusFunction.QPochhammerElementaryIdentities
import Mathlib.LinearAlgebra.Lagrange

/-!
# The finite partial-fraction decomposition of `1/(z;q)_{n+1}`

Over a field, whenever `(q;q)_n ≠ 0`,

`1/(z;q)_{n+1} = ∑_{j=0}^{n} c_j / (1 - z q^j)`,
`c_j = (-1)^j q^{\binom{j+1}{2}} / ((q;q)_j (q;q)_{n-j})`.

The identity is first proved in its **division-free polynomial form**

`∑_{j=0}^{n} c_j ∏_{i ≠ j} (1 - X q^i) = 1` in `K[X]`,

by Lagrange interpolation: both sides have degree at most `n`, and at the
`n+1` distinct nodes `z = q^{-j}` only the `j`-th summand survives, where it
equals `c_j ∏_{i≠j}(1 - q^{i-j}) = 1`.  That last product is evaluated with
the base-reversal identity `(q^{-1};q^{-1})_j = (-1)^j q^{-\binom{j+1}{2}} (q;q)_j`.
The pointwise form follows by evaluating at `z` and dividing by `(z;q)_{n+1}`.

The hypothesis `(q;q)_n ≠ 0` (no `q^m = 1` for `1 ≤ m ≤ n`) is exactly what
makes the coefficients defined; for `q = 0` it holds automatically and the
sum collapses to its first term.

## Main declarations

* `partialFractionCoeff`: the coefficient `c_j`.
* `prod_erase_one_sub_inv_pow_mul_pow`: `∏_{i≠j, i≤n} (1 - q^{i-j})` in closed form.
* `sum_partialFractionCoeff_mul_prod_erase`: the polynomial identity.
* `one_div_finiteQPochhammerIn_eq_sum`: the partial-fraction decomposition.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Polynomial Finset

variable {K : Type*} [Field K] {q : K}

/-- The partial-fraction coefficient
`c_j = (-1)^j q^{\binom{j+1}{2}} / ((q;q)_j (q;q)_{n-j})` of `1/(z;q)_{n+1}`. -/
noncomputable def partialFractionCoeff (q : K) (n j : ℕ) : K :=
  (-1) ^ j * q ^ (j + 1).choose 2 /
    (finiteQPochhammerIn q q j * finiteQPochhammerIn q q (n - j))

/-- The product of `1 - q^{i-j}` over `0 ≤ i ≤ n`, `i ≠ j`, in closed form:
`(-1)^j q^{-\binom{j+1}{2}} (q;q)_j (q;q)_{n-j}`. -/
theorem prod_erase_one_sub_inv_pow_mul_pow (hq : q ≠ 0) {n j : ℕ} (hj : j ≤ n) :
    ∏ i ∈ (range (n + 1)).erase j, (1 - q⁻¹ ^ j * q ^ i) =
      (-1) ^ j * q⁻¹ ^ (j + 1).choose 2 * finiteQPochhammerIn q q j *
        finiteQPochhammerIn q q (n - j) := by
  have hsplit : (range (n + 1)).erase j = range j ∪ Ico (j + 1) (n + 1) := by
    ext i
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (range j) (Ico (j + 1) (n + 1)) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_range, Finset.mem_Ico] at hi hi'
    omega
  have hlow : ∏ i ∈ range j, (1 - q⁻¹ ^ j * q ^ i) = finiteQPochhammerIn q⁻¹ q⁻¹ j := by
    rw [finiteQPochhammerIn, ← Finset.prod_range_reflect]
    refine Finset.prod_congr rfl fun s hs => ?_
    have hs' : s < j := Finset.mem_range.mp hs
    rw [show q⁻¹ ^ j = q⁻¹ ^ (s + 1) * q⁻¹ ^ (j - 1 - s) by rw [← pow_add]; congr 1; omega,
      mul_assoc, ← mul_pow, inv_mul_cancel₀ hq, one_pow, mul_one, pow_succ']
  have hup : ∏ i ∈ Ico (j + 1) (n + 1), (1 - q⁻¹ ^ j * q ^ i) =
      finiteQPochhammerIn q q (n - j) := by
    rw [Finset.prod_Ico_eq_prod_range, show n + 1 - (j + 1) = n - j by omega, finiteQPochhammerIn]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [show j + 1 + k = j + (k + 1) by omega, pow_add, ← mul_assoc, ← mul_pow,
      inv_mul_cancel₀ hq, one_pow, one_mul, pow_succ']
  have hc : (j + 1).choose 2 = j + j.choose 2 := by
    rw [Nat.choose_succ_succ' j 1, Nat.choose_one_right]
  rw [hsplit, Finset.prod_union hdisj, hlow, hup,
    finiteQPochhammerIn_inv_base_reversal _ _ (inv_ne_zero hq) hq, inv_inv, hc, pow_add, neg_pow]
  ring

/-- The prefix `(q;q)_k` of a nonvanishing `(q;q)_n` is nonvanishing. -/
theorem finiteQPochhammerIn_self_ne_zero_of_le {n : ℕ} (hqn : finiteQPochhammerIn q q n ≠ 0)
    {k : ℕ} (hk : k ≤ n) : finiteQPochhammerIn q q k ≠ 0 := by
  have h := finiteQPochhammerIn_add q q k (n - k)
  rw [show k + (n - k) = n by omega] at h
  rw [h] at hqn
  exact left_ne_zero_of_mul hqn

/-- The diagonal term of the interpolation: `c_j` times the product it was
built to cancel is `1`. -/
theorem partialFractionCoeff_mul_prod_eq_one (hq : q ≠ 0) {n : ℕ}
    (hqn : finiteQPochhammerIn q q n ≠ 0) {k : ℕ} (hk : k ≤ n) :
    partialFractionCoeff q n k *
      ((-1) ^ k * q⁻¹ ^ (k + 1).choose 2 * finiteQPochhammerIn q q k *
        finiteQPochhammerIn q q (n - k)) = 1 := by
  have hA : finiteQPochhammerIn q q k ≠ 0 := finiteQPochhammerIn_self_ne_zero_of_le hqn hk
  have hB : finiteQPochhammerIn q q (n - k) ≠ 0 :=
    finiteQPochhammerIn_self_ne_zero_of_le hqn (Nat.sub_le n k)
  have h1 : ((-1 : K) ^ k) * (-1) ^ k = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have h2 : q ^ (k + 1).choose 2 * q⁻¹ ^ (k + 1).choose 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hq, one_pow]
  have h3 : finiteQPochhammerIn q q k * finiteQPochhammerIn q q (n - k) ≠ 0 := mul_ne_zero hA hB
  rw [partialFractionCoeff]
  calc (-1) ^ k * q ^ (k + 1).choose 2 /
          (finiteQPochhammerIn q q k * finiteQPochhammerIn q q (n - k)) *
        ((-1) ^ k * q⁻¹ ^ (k + 1).choose 2 * finiteQPochhammerIn q q k *
          finiteQPochhammerIn q q (n - k))
      = ((-1) ^ k * (-1) ^ k) * (q ^ (k + 1).choose 2 * q⁻¹ ^ (k + 1).choose 2) *
          ((finiteQPochhammerIn q q k * finiteQPochhammerIn q q (n - k)) /
            (finiteQPochhammerIn q q k * finiteQPochhammerIn q q (n - k))) := by ring
    _ = 1 := by rw [h1, h2, div_self h3, mul_one, mul_one]

/-- **The polynomial partial-fraction identity**: for `(q;q)_n ≠ 0`,
`∑_{j≤n} c_j ∏_{i≠j} (1 - X q^i) = 1` in `K[X]`. -/
theorem sum_partialFractionCoeff_mul_prod_erase {n : ℕ} (hqn : finiteQPochhammerIn q q n ≠ 0) :
    ∑ j ∈ range (n + 1), C (partialFractionCoeff q n j) *
      ∏ i ∈ (range (n + 1)).erase j, (1 - X * C (q ^ i)) = 1 := by
  classical
  rcases eq_or_ne q 0 with rfl | hq
  · rw [Finset.sum_eq_single 0]
    · have h1 : partialFractionCoeff (0 : K) n 0 = 1 := by
        simp [partialFractionCoeff, finiteQPochhammerIn]
      rw [h1, map_one, one_mul]
      refine Finset.prod_eq_one fun i hi => ?_
      rw [zero_pow (Finset.mem_erase.mp hi).1, map_zero, mul_zero, sub_zero]
    · intro j _ hj
      have h0 : partialFractionCoeff (0 : K) n j = 0 := by
        rw [partialFractionCoeff, zero_pow, mul_zero, zero_div]
        exact (Nat.choose_pos (by omega)).ne'
      rw [h0, map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h
  · have hpow : ∀ m, 1 ≤ m → m ≤ n → q ^ m ≠ 1 := by
      intro m hm1 hmn h
      apply hqn
      rw [finiteQPochhammerIn]
      refine Finset.prod_eq_zero (i := m - 1) (Finset.mem_range.mpr (by omega)) ?_
      rw [← pow_succ', show m - 1 + 1 = m by omega, h, sub_self]
    have hinj : Set.InjOn (fun i : ℕ => (q⁻¹ ^ i : K)) (range (n + 1)) := by
      intro i hi j hj hij
      have hi' : i < n + 1 := Finset.mem_range.mp (Finset.mem_coe.mp hi)
      have hj' : j < n + 1 := Finset.mem_range.mp (Finset.mem_coe.mp hj)
      have hij' : q ^ i = q ^ j := by
        have h := hij
        simp only [inv_pow, inv_inj] at h
        exact h
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · refine hpow (j - i) (by omega) (by omega) ?_
        have h2 : q ^ i * q ^ (j - i) = q ^ i * 1 := by
          rw [← pow_add, show i + (j - i) = j by omega, mul_one, hij']
        exact mul_left_cancel₀ (pow_ne_zero i hq) h2
      · refine hpow (i - j) (by omega) (by omega) ?_
        have h2 : q ^ j * q ^ (i - j) = q ^ j * 1 := by
          rw [← pow_add, show j + (i - j) = i by omega, mul_one, ← hij']
        exact mul_left_cancel₀ (pow_ne_zero j hq) h2
    have hcard : ((range (n + 1)).image (fun i : ℕ => (q⁻¹ ^ i : K))).card = n + 1 := by
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    have hdeg1 : ∀ i : ℕ, (1 - X * C (q ^ i) : K[X]).natDegree ≤ 1 := fun i => by
      rw [X_mul_C]
      exact (natDegree_sub_le _ _).trans
        (max_le (natDegree_one.le.trans zero_le_one)
          ((natDegree_C_mul_le _ _).trans natDegree_X_le))
    have hdegP : ∀ j ∈ range (n + 1),
        (∏ i ∈ (range (n + 1)).erase j, (1 - X * C (q ^ i) : K[X])).natDegree ≤ n := by
      intro j hj
      refine le_trans (natDegree_prod_le _ _) ?_
      calc ∑ i ∈ (range (n + 1)).erase j, (1 - X * C (q ^ i) : K[X]).natDegree
          ≤ ∑ i ∈ (range (n + 1)).erase j, 1 := Finset.sum_le_sum fun i _ => hdeg1 i
        _ = n := by
          rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem hj,
            Finset.card_range, Nat.add_sub_cancel]
    refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq
      ((range (n + 1)).image (fun i : ℕ => (q⁻¹ ^ i : K))) ?_ ?_ ?_
    · rw [hcard]
      refine lt_of_le_of_lt (degree_le_of_natDegree_le
        (natDegree_sum_le_of_forall_le _ _ fun j hj => ?_)) (by exact_mod_cast Nat.lt_succ_self n)
      exact (natDegree_C_mul_le _ _).trans (hdegP j hj)
    · rw [hcard, degree_one]
      exact_mod_cast Nat.succ_pos n
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      simp only [eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_one, eval_X]
      rw [Finset.sum_eq_single k]
      · rw [prod_erase_one_sub_inv_pow_mul_pow hq hkn]
        exact partialFractionCoeff_mul_prod_eq_one hq hqn hkn
      · intro j _ hjk
        refine mul_eq_zero_of_right _
          (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hjk.symm, hk⟩) ?_)
        rw [← mul_pow, inv_mul_cancel₀ hq, one_pow, sub_self]
      · intro h
        exact absurd hk h

/-- **The finite partial-fraction decomposition**: for `(q;q)_n ≠ 0` and `z` away
from the poles,
`1/(z;q)_{n+1} = ∑_{j=0}^{n} (-1)^j q^{\binom{j+1}{2}} / ((q;q)_j (q;q)_{n-j}) · 1/(1 - z q^j)`. -/
theorem one_div_finiteQPochhammerIn_eq_sum {n : ℕ} (hqn : finiteQPochhammerIn q q n ≠ 0)
    {z : K} (hz : ∀ j ∈ range (n + 1), 1 - z * q ^ j ≠ 0) :
    1 / finiteQPochhammerIn z q (n + 1) =
      ∑ j ∈ range (n + 1), partialFractionCoeff q n j / (1 - z * q ^ j) := by
  have hpoly := congrArg (Polynomial.eval z) (sum_partialFractionCoeff_mul_prod_erase hqn)
  simp only [eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_one, eval_X] at hpoly
  have hP : ∀ j ∈ range (n + 1), partialFractionCoeff q n j / (1 - z * q ^ j) =
      partialFractionCoeff q n j * (∏ i ∈ (range (n + 1)).erase j, (1 - z * q ^ i)) /
        finiteQPochhammerIn z q (n + 1) := by
    intro j hj
    have hne : ∏ i ∈ (range (n + 1)).erase j, (1 - z * q ^ i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi => hz i (Finset.mem_of_mem_erase hi)
    rw [finiteQPochhammerIn, ← Finset.mul_prod_erase _ _ hj, mul_div_mul_right _ _ hne]
  rw [Finset.sum_congr rfl hP]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, hpoly, one_mul]

end Fabius
