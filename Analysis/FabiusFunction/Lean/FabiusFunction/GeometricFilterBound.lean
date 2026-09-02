import FabiusFunction.GeometricQBinomialLagrange
import FabiusFunction.GaussianBinomialBounds
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# A quantitative bound for the geometric Lagrange filter

Let `0 < q < 1` and let `λ_{n,k} = λ_{n,k}^{(q)}` be the geometric Lagrange weights at `0` on the
nodes `1, q, …, q^n`.  Their moments are `∑_k λ_{n,k} (q^k)^d = (-1)^n q^{n(n+1)/2} [d-1,n]_q`
for `d ≥ 1` (and `1` for `d = 0`), so for `f(w) = ∑_m a_m w^m` with `‖a_m‖ ≤ M R^{-m}` and
`‖z‖ < R`,

`∑_k λ_{n,k} f(q^k z) - a_0 = (-1)^n q^{n(n+1)/2} ∑_{m ≥ n+1} a_m z^m [m-1,n]_q`,

the terms with `1 ≤ m ≤ n` vanishing.  Since `0 ≤ [m-1,n]_q ≤ 1/(q;q)_n`, this gives

`‖∑_k λ_{n,k} f(q^k z) - a_0‖ ≤ M q^{n(n+1)/2}/(q;q)_n · (‖z‖/R)^{n+1}/(1 - ‖z‖/R)`.

## Main declarations

* `gaussianBinomial_le_inv_finiteQPochhammerIn`: `[m,n]_q ≤ 1/(q;q)_n` for all `m`.
* `hasSum_geometricFilter`: the filter applied to a power series is the moment-weighted series.
* `norm_geometricFilter_sub_le`: the quantitative bound.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset

variable {q : ℝ}

/-- `[m,n]_q ≤ 1/(q;q)_n` for `0 ≤ q < 1` and all `m`. -/
theorem gaussianBinomial_le_inv_finiteQPochhammerIn (hq0 : 0 ≤ q) (hq1 : q < 1) (m n : ℕ) :
    gaussianBinomial q m n ≤ (finiteQPochhammerIn q q n)⁻¹ := by
  have hn0 : 0 < finiteQPochhammerIn q q n := finiteQPochhammerIn_self_pos hq0 hq1 n
  rcases lt_or_ge m n with h | h
  · rw [gaussianBinomial_eq_zero_of_lt q h]
    exact inv_nonneg.mpr hn0.le
  · rw [gaussianBinomial_eq_finiteQPochhammerIn_div h hn0.ne', div_le_iff₀ hn0,
      inv_mul_cancel₀ hn0.ne']
    exact finiteQPochhammerIn_pow_le_one hq0 hq1.le _ n

/-- The complex Gaussian coefficient of a real base is real. -/
theorem ofReal_gaussianBinomial (q : ℝ) (m n : ℕ) :
    ((gaussianBinomial q m n : ℝ) : ℂ) = gaussianBinomial (q : ℂ) m n := by
  have h := map_gaussianBinomial Complex.ofRealHom q m n
  simpa only [Complex.ofRealHom_eq_coe] using h

/-- The geometric nodes `1, q, …, q^n` in `ℂ` are distinct for `0 < q < 1`. -/
theorem injOn_pow_ofReal (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    Set.InjOn (fun j : ℕ => (q : ℂ) ^ j) (range (n + 1)) := by
  intro i _ j _ hij
  beta_reduce at hij
  have h : q ^ i = q ^ j := by exact_mod_cast hij
  exact pow_right_injective₀ hq0 hq1.ne h

/-- The `m`-th moment of the geometric filter: `1` for `m = 0`, and
`(-1)^n q^{n(n+1)/2} [m-1,n]_q` for `m ≥ 1`. -/
theorem sum_geometricLagrangeWeight_mul_pow_eq (hq0 : 0 < q) (hq1 : q < 1) (n m : ℕ) :
    ∑ k ∈ range (n + 1), geometricLagrangeWeight (q : ℂ) n k * ((q : ℂ) ^ k) ^ m =
      if m = 0 then 1 else (-1) ^ n * (q : ℂ) ^ (n * (n + 1) / 2) *
        gaussianBinomial (q : ℂ) (m - 1) n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [pow_zero, mul_one, if_true]
    exact sum_geometricLagrangeWeight (q : ℂ) n (injOn_pow_ofReal hq0 hq1 n)
  · rw [if_neg hm.ne']
    exact sum_geometricLagrangeWeight_mul_pow_eq_gaussianBinomial (q : ℂ) n m
      (injOn_pow_ofReal hq0 hq1 n) hm

/-- **The geometric filter of a power series** is the moment-weighted series:
`∑_k λ_{n,k} ∑_m a_m (q^k z)^m = ∑_m a_m z^m c_m` with `c_m` the `m`-th moment. -/
theorem hasSum_geometricFilter (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) {a : ℕ → ℂ} {M R : ℝ}
    (hR : 0 < R) (ha : ∀ m, ‖a m‖ ≤ M * R⁻¹ ^ m) {z : ℂ} (hz : ‖z‖ < R) :
    HasSum (fun m : ℕ => a m * z ^ m *
        ∑ k ∈ range (n + 1), geometricLagrangeWeight (q : ℂ) n k * ((q : ℂ) ^ k) ^ m)
      (∑ k ∈ range (n + 1), geometricLagrangeWeight (q : ℂ) n k *
        ∑' m : ℕ, a m * ((q : ℂ) ^ k * z) ^ m) := by
  have hqc : ‖(q : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hq0.le]
    exact hq1.le
  have ht0 : 0 ≤ ‖z‖ / R := div_nonneg (norm_nonneg z) hR.le
  have ht1 : ‖z‖ / R < 1 := (div_lt_one hR).mpr hz
  have hgeom : Summable fun m : ℕ => M * (‖z‖ / R) ^ m :=
    (summable_geometric_of_lt_one ht0 ht1).mul_left M
  have hsum : ∀ k : ℕ, Summable fun m : ℕ => a m * ((q : ℂ) ^ k * z) ^ m := fun k => by
    refine Summable.of_norm_bounded hgeom fun m => ?_
    rw [norm_mul, norm_pow, norm_mul, norm_pow, div_pow]
    have hqk : ‖(q : ℂ)‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hqc
    calc ‖a m‖ * (‖(q : ℂ)‖ ^ k * ‖z‖) ^ m ≤ M * R⁻¹ ^ m * ‖z‖ ^ m := by
          refine mul_le_mul (ha m) ?_ (by positivity) ?_
          · exact pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_left (norm_nonneg z) hqk) m
          · exact (norm_nonneg _).trans (ha m)
      _ = M * (‖z‖ ^ m / R ^ m) := by rw [inv_pow]; ring
  have h := hasSum_sum (s := range (n + 1)) fun k _ =>
    ((hsum k).hasSum.mul_left (geometricLagrangeWeight (q : ℂ) n k))
  have hfun : (fun m : ℕ => ∑ k ∈ range (n + 1),
      geometricLagrangeWeight (q : ℂ) n k * (a m * ((q : ℂ) ^ k * z) ^ m)) =
      fun m : ℕ => a m * z ^ m * ∑ k ∈ range (n + 1),
        geometricLagrangeWeight (q : ℂ) n k * ((q : ℂ) ^ k) ^ m := by
    funext m
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_pow]
    ring
  rw [hfun] at h
  exact h

/-- **A quantitative analytic bound for the geometric filter**:
`‖∑_k λ_{n,k} f(q^k z) - a_0‖ ≤ M q^{n(n+1)/2}/(q;q)_n · (‖z‖/R)^{n+1}/(1 - ‖z‖/R)`. -/
theorem norm_geometricFilter_sub_le (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) {a : ℕ → ℂ} {M R : ℝ}
    (hR : 0 < R) (ha : ∀ m, ‖a m‖ ≤ M * R⁻¹ ^ m) {z : ℂ} (hz : ‖z‖ < R) :
    ‖(∑ k ∈ range (n + 1), geometricLagrangeWeight (q : ℂ) n k *
        ∑' m : ℕ, a m * ((q : ℂ) ^ k * z) ^ m) - a 0‖ ≤
      M * q ^ (n * (n + 1) / 2) / finiteQPochhammerIn q q n *
        ((‖z‖ / R) ^ (n + 1) / (1 - ‖z‖ / R)) := by
  set t := ‖z‖ / R with ht_def
  have ht0 : 0 ≤ t := div_nonneg (norm_nonneg z) hR.le
  have ht1 : t < 1 := (div_lt_one hR).mpr hz
  have hM : 0 ≤ M := (norm_nonneg (a 0)).trans (by simpa using ha 0)
  have hqn : 0 < finiteQPochhammerIn q q n := finiteQPochhammerIn_self_pos hq0.le hq1 n
  set C : ℝ := M * q ^ (n * (n + 1) / 2) / finiteQPochhammerIn q q n with hC_def
  have hC0 : 0 ≤ C := by positivity
  -- the moment-weighted series
  set g : ℕ → ℂ := fun m => a m * z ^ m *
    (if m = 0 then 1 else (-1) ^ n * (q : ℂ) ^ (n * (n + 1) / 2) *
      gaussianBinomial (q : ℂ) (m - 1) n) with hg_def
  have hS : HasSum g (∑ k ∈ range (n + 1), geometricLagrangeWeight (q : ℂ) n k *
      ∑' m : ℕ, a m * ((q : ℂ) ^ k * z) ^ m) := by
    have h := hasSum_geometricFilter hq0 hq1 n hR ha hz
    simp_rw [sum_geometricLagrangeWeight_mul_pow_eq hq0 hq1 n] at h
    exact h
  -- the head `m ≤ n` contributes exactly `a 0`
  have hhead : ∑ i ∈ range (n + 1), g i = a 0 := by
    rw [sum_range_succ', Finset.sum_eq_zero, zero_add]
    · simp [hg_def]
    · intro i hi
      have hi' : i < n := mem_range.mp hi
      simp [hg_def, gaussianBinomial_eq_zero_of_lt (q : ℂ) hi']
  have hsplit := hS.summable.sum_add_tsum_nat_add (n + 1)
  rw [hhead, hS.tsum_eq] at hsplit
  have htail : (∑ k ∈ range (n + 1), geometricLagrangeWeight (q : ℂ) n k *
      ∑' m : ℕ, a m * ((q : ℂ) ^ k * z) ^ m) - a 0 = ∑' j : ℕ, g (j + (n + 1)) := by
    rw [← hsplit, add_sub_cancel_left]
  -- termwise bound on the tail
  have hbound : ∀ j : ℕ, ‖g (j + (n + 1))‖ ≤ C * t ^ (j + (n + 1)) := by
    intro j
    have hj : j + (n + 1) ≠ 0 := by omega
    have hga : 0 ≤ gaussianBinomial q (j + n) n := gaussianBinomial_nonneg hq0.le _ _
    have hgb : gaussianBinomial q (j + n) n ≤ (finiteQPochhammerIn q q n)⁻¹ :=
      gaussianBinomial_le_inv_finiteQPochhammerIn hq0.le hq1 _ _
    have hnorm : ‖gaussianBinomial (q : ℂ) (j + (n + 1) - 1) n‖ =
        gaussianBinomial q (j + n) n := by
      rw [show j + (n + 1) - 1 = j + n by omega, ← ofReal_gaussianBinomial, Complex.norm_real,
        Real.norm_of_nonneg hga]
    have hqpow : ‖(q : ℂ) ^ (n * (n + 1) / 2)‖ = q ^ (n * (n + 1) / 2) := by
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hq0.le]
    have hzpow : ‖a (j + (n + 1)) * z ^ (j + (n + 1))‖ ≤ M * t ^ (j + (n + 1)) := by
      rw [norm_mul, norm_pow, ht_def, div_pow]
      calc ‖a (j + (n + 1))‖ * ‖z‖ ^ (j + (n + 1))
          ≤ M * R⁻¹ ^ (j + (n + 1)) * ‖z‖ ^ (j + (n + 1)) :=
            mul_le_mul_of_nonneg_right (ha _) (by positivity)
        _ = M * (‖z‖ ^ (j + (n + 1)) / R ^ (j + (n + 1))) := by rw [inv_pow]; ring
    have hnegpow : ‖((-1 : ℂ) ^ n)‖ = 1 := by rw [norm_pow, norm_neg, norm_one, one_pow]
    simp only [hg_def, if_neg hj]
    rw [show a (j + (n + 1)) * z ^ (j + (n + 1)) * ((-1) ^ n * (q : ℂ) ^ (n * (n + 1) / 2) *
        gaussianBinomial (q : ℂ) (j + (n + 1) - 1) n) =
        (a (j + (n + 1)) * z ^ (j + (n + 1))) * (-1) ^ n * (q : ℂ) ^ (n * (n + 1) / 2) *
          gaussianBinomial (q : ℂ) (j + (n + 1) - 1) n by ring,
      norm_mul, norm_mul, norm_mul, hnegpow, mul_one, hqpow, hnorm, hC_def]
    calc ‖a (j + (n + 1)) * z ^ (j + (n + 1))‖ * q ^ (n * (n + 1) / 2) *
          gaussianBinomial q (j + n) n
        ≤ M * t ^ (j + (n + 1)) * q ^ (n * (n + 1) / 2) * (finiteQPochhammerIn q q n)⁻¹ := by
          gcongr
      _ = M * q ^ (n * (n + 1) / 2) / finiteQPochhammerIn q q n * t ^ (j + (n + 1)) := by
          rw [div_eq_mul_inv]
          ring
  -- summing the geometric majorant
  have hmaj : Summable fun j : ℕ => C * t ^ (j + (n + 1)) :=
    (summable_nat_add_iff (f := fun j : ℕ => C * t ^ j) (n + 1)).mpr
      ((summable_geometric_of_lt_one ht0 ht1).mul_left C)
  have hmaj_sum : ∑' j : ℕ, C * t ^ (j + (n + 1)) = C * (t ^ (n + 1) / (1 - t)) := by
    have hsplit : ∀ j : ℕ, C * t ^ (j + (n + 1)) = (C * t ^ (n + 1)) * t ^ j := fun j => by
      rw [pow_add]; ring
    simp_rw [hsplit]
    rw [tsum_mul_left, tsum_geometric_of_lt_one ht0 ht1]
    ring
  have hnormsum : Summable fun j : ℕ => ‖g (j + (n + 1))‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hbound hmaj
  rw [htail]
  calc ‖∑' j : ℕ, g (j + (n + 1))‖ ≤ ∑' j : ℕ, ‖g (j + (n + 1))‖ :=
        norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' j : ℕ, C * t ^ (j + (n + 1)) := hnormsum.tsum_le_tsum hbound hmaj
    _ = C * (t ^ (n + 1) / (1 - t)) := hmaj_sum

end Fabius
