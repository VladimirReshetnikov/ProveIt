import FabiusFunction.BilateralSeriesConvergence
import FabiusFunction.QBinomialTheoremInfinite
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Ramanujan's `₁ψ₁` summation

For `‖q‖ < 1`, `q ≠ 0`, `a ≠ 0` with `(q/a;q)_∞ ≠ 0`, and `‖b/a‖ < ‖z‖ < 1` with `(b;q)_∞ ≠ 0`,

`∑_{n ∈ ℤ} (a;q)_n/(b;q)_n z^n = (q, b/a, az, q/(az); q)_∞ / (b, q/a, z, b/(az); q)_∞`.

The proof (Ismail's) is by the identity theorem in the parameter `b`.  We work with the
**cleared series** `∑_{n ∈ ℤ} (a;q)_n z^n (bq^n;q)_∞`, which is `(b;q)_∞ · ₁ψ₁` when the
denominators are nonzero and whose terms are entire functions of `b`:

* at `b = q^{m+1}` the terms with `n ≤ -(m+1)` vanish, and after the shift `n = k - m` the
  series is the infinite `q`-binomial theorem for `(aq^{-m}z;q)_∞/(z;q)_∞`
  (`hasSum_onePsiOneCleared_pow`), while the product side reduces to the same value by
  the reversal `(xq^{-m};q)_m = (-x)^m q^{-\binom{m+1}{2}} (q/x;q)_m`
  (`onePsiOneProduct_pow`);
* on every disc `‖b‖ < r < ‖az‖` the cleared series is dominated by a geometric series in
  `max ‖z‖ (r/‖az‖)` uniformly in `b`, hence holomorphic (`differentiableOn_onePsiOneCleared`);
* the points `q^{m+1}` accumulate at `0`, so the identity theorem gives the cleared identity on
  the disc, and dividing by `(b;q)_∞` gives Ramanujan's sum (`hasSum_onePsiOne`).

Over `ℂ`, where the identity theorem is available; the convergence statements are in
`BilateralSeriesConvergence` for every complete normed field.
-/

set_option autoImplicit false

open Filter Topology Set
open scoped BigOperators

namespace Fabius

section Field

variable {K : Type*} [Field K] {a q : K}

/-- **Concatenation with a negative index**: `(a;q)_{k-m} = (a;q)_{-m} (aq^{-m};q)_k` for
`k, m ∈ ℕ`, assuming only `(a;q)_{-m} ≠ 0`. -/
theorem finiteQPochhammerZ_natCast_sub (hq : q ≠ 0) {m : ℕ}
    (hm : finiteQPochhammerZ a q (-m) ≠ 0) (k : ℕ) :
    finiteQPochhammerZ a q (k - m) =
      finiteQPochhammerZ a q (-m) * finiteQPochhammerIn (a * q ^ (-(m : ℤ))) q k := by
  have hI : qIntervalProd a q (-m) (-m + k) = finiteQPochhammerIn (a * q ^ (-(m : ℤ))) q k := by
    rw [qIntervalProd_add_eq hq, finiteQPochhammerZ_natCast]
  have hm' : qIntervalProd a q (-m) 0 ≠ 0 := by
    rw [finiteQPochhammerZ, qIntervalProd_symm] at hm
    exact fun h => hm (by rw [h, inv_zero])
  rw [← hI, show ((k : ℤ) - m) = -m + k by ring]
  rcases le_or_gt m k with hmk | hmk
  · have h := qIntervalProd_trans_of_le (a := a) (q := q) (by omega : -(m : ℤ) ≤ 0)
      (by omega : (0 : ℤ) ≤ -m + k)
    have hm0 : qIntervalProd a q 0 (-m) ≠ 0 := hm
    rw [finiteQPochhammerZ, finiteQPochhammerZ, h, qIntervalProd_symm (0 : ℤ) (-m),
      mul_inv_cancel_left₀ hm0]
  · have h := qIntervalProd_trans_of_le (a := a) (q := q) (by omega : -(m : ℤ) ≤ -m + k)
      (by omega : -(m : ℤ) + k ≤ 0)
    have hX : qIntervalProd a q (-m) (-m + k) ≠ 0 := by
      rw [h] at hm'
      exact left_ne_zero_of_mul hm'
    rw [finiteQPochhammerZ, finiteQPochhammerZ, qIntervalProd_symm (-(m : ℤ)) 0,
      qIntervalProd_symm (-(m : ℤ) + k) 0, h, mul_inv,
      mul_comm (qIntervalProd a q (-(m : ℤ)) (-(m : ℤ) + k))⁻¹, mul_assoc,
      inv_mul_cancel₀ hX, mul_one]

/-- `(xq^{-m};q)_m` is the reciprocal of `(x;q)_{-m}`. -/
theorem finiteQPochhammerIn_mul_zpow_neg (hq : q ≠ 0) (x : K) (m : ℕ) :
    finiteQPochhammerIn (x * q ^ (-(m : ℤ))) q m = (finiteQPochhammerZ x q (-m))⁻¹ := by
  rw [finiteQPochhammerZ_neg_natCast, inv_inv, finiteQPochhammerIn]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [zpow_add₀ hq, zpow_natCast, mul_assoc]

/-- **Reversal as a polynomial identity**:
`(xq^{-m};q)_m · q^{\binom{m+1}{2}} = ∏_{i<m} (q^{i+1} - x)`. -/
theorem finiteQPochhammerIn_mul_zpow_neg_mul_pow (hq : q ≠ 0) (x : K) (m : ℕ) :
    finiteQPochhammerIn (x * q ^ (-(m : ℤ))) q m * q ^ (m + 1).choose 2 =
      ∏ i ∈ Finset.range m, (q ^ (i + 1) - x) := by
  induction m with
  | zero => simp [finiteQPochhammerIn]
  | succ k ih =>
    have hstep : x * q ^ (-((k + 1 : ℕ) : ℤ)) * q = x * q ^ (-(k : ℤ)) := by
      rw [mul_assoc, ← zpow_add_one₀ hq]
      congr 2
      push_cast
      ring
    have hch : (k + 2).choose 2 = (k + 1).choose 2 + (k + 1) := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
    have hfac : (1 - x * q ^ (-((k + 1 : ℕ) : ℤ))) * q ^ (k + 1) = q ^ (k + 1) - x := by
      rw [sub_mul, one_mul, mul_assoc, ← zpow_natCast q (k + 1), ← zpow_add₀ hq,
        neg_add_cancel, zpow_zero, mul_one]
    rw [finiteQPochhammerIn_succ_shift, hstep, hch, pow_add, Finset.prod_range_succ, ← ih]
    calc (1 - x * q ^ (-((k + 1 : ℕ) : ℤ))) * finiteQPochhammerIn (x * q ^ (-(k : ℤ))) q k *
          (q ^ (k + 1).choose 2 * q ^ (k + 1))
        = finiteQPochhammerIn (x * q ^ (-(k : ℤ))) q k * q ^ (k + 1).choose 2 *
          ((1 - x * q ^ (-((k + 1 : ℕ) : ℤ))) * q ^ (k + 1)) := by ring
      _ = _ := by rw [hfac]

/-- `∏_{i<m} (q^{i+1} - a) = (-a)^m (q/a;q)_m` for `a ≠ 0`. -/
theorem prod_pow_succ_sub_eq (ha : a ≠ 0) (m : ℕ) :
    ∏ i ∈ Finset.range m, (q ^ (i + 1) - a) = (-a) ^ m * finiteQPochhammerIn (q / a) q m := by
  rw [finiteQPochhammerIn, Finset.pow_eq_prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  field_simp
  ring

/-- The quotient `(bq^{-m};q)_m/(aq^{-m};q)_m` as a quotient of the reversed polynomials. -/
theorem finiteQPochhammerIn_mul_zpow_neg_div (hq : q ≠ 0) (x y : K) (m : ℕ) :
    finiteQPochhammerIn (x * q ^ (-(m : ℤ))) q m / finiteQPochhammerIn (y * q ^ (-(m : ℤ))) q m =
      (∏ i ∈ Finset.range m, (q ^ (i + 1) - x)) / ∏ i ∈ Finset.range m, (q ^ (i + 1) - y) := by
  rw [← finiteQPochhammerIn_mul_zpow_neg_mul_pow hq x, ← finiteQPochhammerIn_mul_zpow_neg_mul_pow hq y,
    mul_div_mul_right _ _ (pow_ne_zero _ hq)]

/-- **The reversal identity behind Ramanujan's sum**:
`z^{-m} (a;q)_{-m} (aq^{-m}z;q)_m = (q/(az);q)_m / (q/a;q)_m` for `a, z, q ≠ 0`. -/
theorem zpow_neg_mul_finiteQPochhammerZ_neg_mul (hq : q ≠ 0) (ha : a ≠ 0) {z : K} (hz : z ≠ 0)
    (m : ℕ) :
    z ^ (-(m : ℤ)) * finiteQPochhammerZ a q (-m) *
        finiteQPochhammerIn (a * q ^ (-(m : ℤ)) * z) q m =
      finiteQPochhammerIn (q / (a * z)) q m / finiteQPochhammerIn (q / a) q m := by
  rw [show a * q ^ (-(m : ℤ)) * z = a * z * q ^ (-(m : ℤ)) by ring,
    finiteQPochhammerIn_mul_zpow_neg hq, finiteQPochhammerZ_neg_natCast_eq ha hq,
    finiteQPochhammerZ_neg_natCast_eq (mul_ne_zero ha hz) hq, zpow_neg, zpow_natCast]
  simp only [inv_pow]
  have hzm : z ^ m ≠ 0 := pow_ne_zero _ hz
  have ham : a ^ m ≠ 0 := pow_ne_zero _ ha
  have hazm : (a * z) ^ m ≠ 0 := pow_ne_zero _ (mul_ne_zero ha hz)
  rcases eq_or_ne (finiteQPochhammerIn (q / (a * z)) q m) 0 with h0 | h0
  · simp [h0]
  rcases eq_or_ne (finiteQPochhammerIn (q / a) q m) 0 with h1 | h1
  · simp [h1]
  have hs : ((-1 : K) ^ m) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hc : q ^ (m + 1).choose 2 ≠ 0 := pow_ne_zero _ hq
  field_simp
  ring

end Field

section Cleared

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- The `n`-th term of the **cleared bilateral series** `(a;q)_n z^n (bq^n;q)_∞`, `n ∈ ℤ`; it
equals `(b;q)_∞ · (a;q)_n/(b;q)_n · z^n` whenever `(b;q)_n ≠ 0`. -/
noncomputable def onePsiOneCleared (a b q z : 𝕜) (n : ℤ) : 𝕜 :=
  finiteQPochhammerZ a q n * z ^ n * qPochhammerInfIn (b * q ^ n) q

/-- The product side of Ramanujan's sum, cleared of `(b;q)_∞`:
`(q, b/a, az, q/(az); q)_∞ / (q/a, z, b/(az); q)_∞`. -/
noncomputable def onePsiOneProduct (a b q z : 𝕜) : 𝕜 :=
  qPochhammerInfIn q q * qPochhammerInfIn (b / a) q * qPochhammerInfIn (a * z) q *
      qPochhammerInfIn (q / (a * z)) q /
    (qPochhammerInfIn (q / a) q * qPochhammerInfIn z q * qPochhammerInfIn (b / (a * z)) q)

variable {a b q z : 𝕜}

/-- The cleared term is `(b;q)_∞` times the `₁ψ₁` term, for `n ≥ 0`. -/
theorem onePsiOneCleared_natCast (hq : ‖q‖ < 1) (hb : qPochhammerInfIn b q ≠ 0) (n : ℕ) :
    onePsiOneCleared a b q z n = qPochhammerInfIn b q * onePsiOneTerm a b q z n := by
  have h0 : finiteQPochhammerIn b q n ≠ 0 :=
    finiteQPochhammerIn_ne_zero_of_qPochhammerInfIn_ne_zero b hq hb n
  rw [onePsiOneCleared, onePsiOneTerm]
  simp only [finiteQPochhammerZ_natCast, zpow_natCast]
  rw [qPochhammerInfIn_eq_finite_mul_shift b hq n]
  field_simp

/-- The cleared term is `(b;q)_∞` times the `₁ψ₁` term, for `n = -m < 0`. -/
theorem onePsiOneCleared_neg_natCast (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (m : ℕ) :
    onePsiOneCleared a b q z (-m) = qPochhammerInfIn b q * onePsiOneTerm a b q z (-m) := by
  rw [onePsiOneCleared, onePsiOneTerm, qPochhammerInfIn_eq_finite_mul_shift (b * q ^ (-(m : ℤ))) hq m,
    show b * q ^ (-(m : ℤ)) * q ^ m = b by
      rw [mul_assoc, ← zpow_natCast q m, ← zpow_add₀ hq0, neg_add_cancel, zpow_zero, mul_one],
    finiteQPochhammerIn_mul_zpow_neg hq0]
  rcases eq_or_ne (finiteQPochhammerZ b q (-m)) 0 with h0 | h0
  · rw [h0]
    simp
  field_simp

/-- The cleared term is `(b;q)_∞` times the `₁ψ₁` term, for every `n ∈ ℤ`. -/
theorem onePsiOneCleared_eq (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hb : qPochhammerInfIn b q ≠ 0)
    (n : ℤ) :
    onePsiOneCleared a b q z n = qPochhammerInfIn b q * onePsiOneTerm a b q z n := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · exact onePsiOneCleared_natCast hq hb k
  · exact onePsiOneCleared_neg_natCast hq hq0 k

/-- At `b = q^{m+1}` the cleared terms with `n < -m` vanish. -/
theorem onePsiOneCleared_pow_eq_zero (hq : ‖q‖ < 1) (hq0 : q ≠ 0) {m : ℕ} {n : ℤ}
    (hn : n < -m) : onePsiOneCleared a (q ^ (m + 1)) q z n = 0 := by
  have h0 : qPochhammerInfIn (q ^ (m + 1) * q ^ n) q = 0 := by
    rw [qPochhammerInfIn_eq_zero_iff _ hq]
    refine ⟨(-((m : ℤ) + 1 + n)).toNat, ?_⟩
    rw [← zpow_natCast q (m + 1), ← zpow_natCast q _, ← zpow_add₀ hq0, ← zpow_add₀ hq0,
      Int.toNat_of_nonneg (by omega), show (((m + 1 : ℕ) : ℤ) + n + -((m : ℤ) + 1 + n)) = 0 by
        push_cast; ring, zpow_zero]
  simp [onePsiOneCleared, h0]

/-- At `b = q^{m+1}`, after the shift `n = k - m`, the cleared term is a constant times the
`k`-th term of the `q`-binomial series with parameter `aq^{-m}`. -/
theorem onePsiOneCleared_pow_natCast_sub (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hz0 : z ≠ 0) {m : ℕ}
    (hm : finiteQPochhammerZ a q (-m) ≠ 0) (k : ℕ) :
    onePsiOneCleared a (q ^ (m + 1)) q z (k - m) =
      qPochhammerInfIn q q * z ^ (-(m : ℤ)) * finiteQPochhammerZ a q (-m) *
        (finiteQPochhammerIn (a * q ^ (-(m : ℤ))) q k / finiteQPochhammerIn q q k * z ^ k) := by
  have hqk : finiteQPochhammerIn q q k ≠ 0 :=
    finiteQPochhammerIn_ne_zero_of_qPochhammerInfIn_ne_zero q hq
      (qPochhammerInfIn_ne_zero_of_norm_lt_one hq hq) k
  have hpow : q ^ (m + 1) * q ^ ((k : ℤ) - m) = q * q ^ k := by
    rw [← zpow_natCast q (m + 1), ← zpow_add₀ hq0,
      show (((m + 1 : ℕ) : ℤ) + ((k : ℤ) - m)) = ((k + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, pow_succ']
  have hz' : z ^ ((k : ℤ) - m) = z ^ (-(m : ℤ)) * z ^ k := by
    rw [sub_eq_neg_add, zpow_add₀ hz0, zpow_natCast]
  have hshift := qPochhammerInfIn_eq_finite_mul_shift q hq k
  rw [onePsiOneCleared, finiteQPochhammerZ_natCast_sub hq0 hm k, hpow, hz', hshift]
  field_simp

/-- **The specialization `b = q^{m+1}`** of the cleared series is the `q`-binomial theorem:
`∑_{n ∈ ℤ} (a;q)_n z^n (q^{m+1+n};q)_∞ = (q;q)_∞ z^{-m} (a;q)_{-m} (aq^{-m}z;q)_∞/(z;q)_∞`. -/
theorem hasSum_onePsiOneCleared_pow (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    {m : ℕ} (hm : finiteQPochhammerZ a q (-m) ≠ 0) :
    HasSum (onePsiOneCleared a (q ^ (m + 1)) q z)
      (qPochhammerInfIn q q * z ^ (-(m : ℤ)) * finiteQPochhammerZ a q (-m) *
        (qPochhammerInfIn (a * q ^ (-(m : ℤ)) * z) q / qPochhammerInfIn z q)) := by
  have hinj : Function.Injective fun k : ℕ => (k : ℤ) - m := fun k₁ k₂ h => by
    have h' : (k₁ : ℤ) = k₂ := by simpa using h
    exact_mod_cast h'
  rw [← hinj.hasSum_iff]
  · have h := (hasSum_qBinomial_theorem hq (a * q ^ (-(m : ℤ))) hz).mul_left
      (qPochhammerInfIn q q * z ^ (-(m : ℤ)) * finiteQPochhammerZ a q (-m))
    refine h.congr_fun fun k => ?_
    exact onePsiOneCleared_pow_natCast_sub hq hq0 hz0 hm k
  · intro n hn
    refine onePsiOneCleared_pow_eq_zero hq hq0 ?_
    by_contra h
    exact hn ⟨(n + m).toNat, by
      show (((n + m).toNat : ℕ) : ℤ) - m = n
      rw [Int.toNat_of_nonneg (by omega)]
      ring⟩

/-- **The product side at `b = q^{m+1}`** equals the value of the specialized cleared series,
whenever `‖q^{m+1}/(az)‖ < 1`. -/
theorem onePsiOneProduct_pow (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (ha0 : a ≠ 0) (hz : ‖z‖ < 1)
    (hz0 : z ≠ 0) (haq : qPochhammerInfIn (q / a) q ≠ 0) {m : ℕ}
    (hmz : ‖q ^ (m + 1) / (a * z)‖ < 1) :
    onePsiOneProduct a (q ^ (m + 1)) q z =
      qPochhammerInfIn q q * z ^ (-(m : ℤ)) * finiteQPochhammerZ a q (-m) *
        (qPochhammerInfIn (a * q ^ (-(m : ℤ)) * z) q / qPochhammerInfIn z q) := by
  have h1 : qPochhammerInfIn (q / a) q =
      finiteQPochhammerIn (q / a) q m * qPochhammerInfIn (q ^ (m + 1) / a) q := by
    rw [qPochhammerInfIn_eq_finite_mul_shift _ hq m]
    congr 2
    ring
  have h2 : qPochhammerInfIn (q / (a * z)) q =
      finiteQPochhammerIn (q / (a * z)) q m * qPochhammerInfIn (q ^ (m + 1) / (a * z)) q := by
    rw [qPochhammerInfIn_eq_finite_mul_shift _ hq m]
    congr 2
    ring
  have h3 : qPochhammerInfIn (a * q ^ (-(m : ℤ)) * z) q =
      finiteQPochhammerIn (a * q ^ (-(m : ℤ)) * z) q m * qPochhammerInfIn (a * z) q := by
    rw [qPochhammerInfIn_eq_finite_mul_shift _ hq m]
    congr 2
    rw [mul_assoc, mul_comm z, ← mul_assoc, mul_assoc a, ← zpow_natCast q m, ← zpow_add₀ hq0,
      neg_add_cancel, zpow_zero, mul_one]
  have hqa_m : finiteQPochhammerIn (q / a) q m ≠ 0 :=
    finiteQPochhammerIn_ne_zero_of_qPochhammerInfIn_ne_zero _ hq haq m
  have hqa' : qPochhammerInfIn (q ^ (m + 1) / a) q ≠ 0 := by
    rw [h1] at haq
    exact right_ne_zero_of_mul haq
  have hqz' : qPochhammerInfIn (q ^ (m + 1) / (a * z)) q ≠ 0 :=
    qPochhammerInfIn_ne_zero_of_norm_lt_one hq hmz
  have hzinf : qPochhammerInfIn z q ≠ 0 := qPochhammerInfIn_ne_zero_of_norm_lt_one hq hz
  have key := zpow_neg_mul_finiteQPochhammerZ_neg_mul hq0 ha0 hz0 (q := q) m
  rw [onePsiOneProduct, h3, h1, h2,
    show qPochhammerInfIn q q * z ^ (-(m : ℤ)) * finiteQPochhammerZ a q (-m) *
        (finiteQPochhammerIn (a * q ^ (-(m : ℤ)) * z) q m * qPochhammerInfIn (a * z) q /
          qPochhammerInfIn z q) =
      qPochhammerInfIn q q * (z ^ (-(m : ℤ)) * finiteQPochhammerZ a q (-m) *
        finiteQPochhammerIn (a * q ^ (-(m : ℤ)) * z) q m) *
        (qPochhammerInfIn (a * z) q / qPochhammerInfIn z q) by ring,
    key]
  field_simp

end Cleared

section Complex

variable {a b q z : ℂ}

/-- Each cleared term is an entire function of `b`. -/
theorem differentiable_onePsiOneCleared (hq : ‖q‖ < 1) (n : ℤ) :
    Differentiable ℂ fun b : ℂ => onePsiOneCleared a b q z n := by
  have h : Differentiable ℂ fun b : ℂ => qPochhammerInfIn (b * q ^ n) q :=
    (differentiable_qPochhammerInfIn hq).comp (differentiable_id.mul_const _)
  exact h.const_mul _

/-- Uniform bound on the positive tail: `‖(a;q)_k z^k (bq^k;q)_∞‖ ≤ A · M_r · ‖z‖^k` for
`‖b‖ ≤ r`. -/
theorem norm_onePsiOneCleared_natCast_le (hq : ‖q‖ < 1) {r : ℝ} (hb : ‖b‖ ≤ r) (k : ℕ) :
    ‖onePsiOneCleared a b q z k‖ ≤
      qPochhammerInfIn (-‖a‖) ‖q‖ * qPochhammerInfIn (-r) ‖q‖ * ‖z‖ ^ k := by
  rw [onePsiOneCleared, finiteQPochhammerZ_natCast, zpow_natCast, norm_mul, norm_mul, norm_pow]
  have h1 := norm_finiteQPochhammerIn_le a hq k
  have h2 : ‖qPochhammerInfIn (b * q ^ k) q‖ ≤ qPochhammerInfIn (-r) ‖q‖ := by
    refine (norm_qPochhammerInfIn_le _ hq).trans
      (qPochhammerInfIn_neg_le_neg (norm_nonneg _) ?_ (norm_nonneg q) hq)
    rw [norm_mul, norm_pow]
    exact (mul_le_of_le_one_right (norm_nonneg b) (pow_le_one₀ (norm_nonneg q) hq.le)).trans hb
  calc ‖finiteQPochhammerIn a q k‖ * ‖z‖ ^ k * ‖qPochhammerInfIn (b * q ^ k) q‖
      ≤ qPochhammerInfIn (-‖a‖) ‖q‖ * ‖z‖ ^ k * qPochhammerInfIn (-r) ‖q‖ :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 (pow_nonneg (norm_nonneg z) k)) h2
          (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans h1) (pow_nonneg (norm_nonneg z) k))
    _ = _ := by ring

/-- Uniform bound on the negative tail: for `‖b‖ ≤ r`,
`‖(a;q)_{-k} z^{-k} (bq^{-k};q)_∞‖ ≤ M' · K_a · M_r · (r/(‖a‖‖z‖))^k`. -/
theorem norm_onePsiOneCleared_neg_natCast_le (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (ha0 : a ≠ 0)
    (hz0 : z ≠ 0) (haq : qPochhammerInfIn (q / a) q ≠ 0) {r : ℝ} (hr : 0 < r) (hb : ‖b‖ ≤ r)
    (k : ℕ) :
    ‖onePsiOneCleared a b q z (-k)‖ ≤
      qPochhammerInfIn (-(‖q‖ / r)) ‖q‖ *
          (qPochhammerInfIn (-‖q / a‖) ‖q‖ / ‖qPochhammerInfIn (q / a) q‖) *
        qPochhammerInfIn (-r) ‖q‖ * (r / (‖a‖ * ‖z‖)) ^ k := by
  have hterm : onePsiOneCleared a b q z (-k) =
      (∏ i ∈ Finset.range k, (q ^ (i + 1) - b)) /
          ((-a) ^ k * finiteQPochhammerIn (q / a) q k) * (z ^ k)⁻¹ * qPochhammerInfIn b q := by
    have hbq : b * q ^ (-(k : ℤ)) * q ^ k = b := by
      rw [mul_assoc, ← zpow_natCast q k, ← zpow_add₀ hq0, neg_add_cancel, zpow_zero, mul_one]
    have hA : finiteQPochhammerZ a q (-k) = (finiteQPochhammerIn (a * q ^ (-(k : ℤ))) q k)⁻¹ := by
      rw [finiteQPochhammerIn_mul_zpow_neg hq0, inv_inv]
    have hdiv := finiteQPochhammerIn_mul_zpow_neg_div hq0 b a k
    rw [prod_pow_succ_sub_eq ha0] at hdiv
    rw [onePsiOneCleared, qPochhammerInfIn_eq_finite_mul_shift (b * q ^ (-(k : ℤ))) hq k, hbq, hA,
      zpow_neg z, zpow_natCast z, ← hdiv]
    ring
  have hnorm : ‖onePsiOneCleared a b q z (-k)‖ =
      (∏ i ∈ Finset.range k, ‖q ^ (i + 1) - b‖) /
          (‖a‖ ^ k * ‖finiteQPochhammerIn (q / a) q k‖) * (‖z‖ ^ k)⁻¹ *
        ‖qPochhammerInfIn b q‖ := by
    rw [hterm]
    simp only [norm_mul, norm_div, norm_inv, norm_pow, norm_neg, norm_prod]
  rw [hnorm]
  have hPb : ∏ i ∈ Finset.range k, ‖q ^ (i + 1) - b‖ ≤
      r ^ k * qPochhammerInfIn (-(‖q‖ / r)) ‖q‖ := by
    calc ∏ i ∈ Finset.range k, ‖q ^ (i + 1) - b‖
        ≤ ∏ i ∈ Finset.range k, (r * (1 - (-(‖q‖ / r)) * ‖q‖ ^ i)) := by
          refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
          calc ‖q ^ (i + 1) - b‖ ≤ ‖q ^ (i + 1)‖ + ‖b‖ := norm_sub_le _ _
            _ ≤ ‖q‖ ^ (i + 1) + r := by rw [norm_pow]; exact add_le_add le_rfl hb
            _ = r * (1 - (-(‖q‖ / r)) * ‖q‖ ^ i) := by field_simp; ring
      _ = r ^ k * finiteQPochhammerIn (-(‖q‖ / r)) ‖q‖ k := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, finiteQPochhammerIn]
      _ ≤ r ^ k * qPochhammerInfIn (-(‖q‖ / r)) ‖q‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hr.le k)
          exact finiteQPochhammerIn_neg_le_qPochhammerInfIn (div_nonneg (norm_nonneg q) hr.le)
            (norm_nonneg q) hq k
  have hKa : ‖finiteQPochhammerIn (q / a) q k‖⁻¹ ≤
      qPochhammerInfIn (-‖q / a‖) ‖q‖ / ‖qPochhammerInfIn (q / a) q‖ :=
    inv_norm_finiteQPochhammerIn_le (q / a) hq haq k
  have hMr : ‖qPochhammerInfIn b q‖ ≤ qPochhammerInfIn (-r) ‖q‖ :=
    (norm_qPochhammerInfIn_le _ hq).trans
      (qPochhammerInfIn_neg_le_neg (norm_nonneg _) hb (norm_nonneg q) hq)
  have hM'0 : 0 ≤ r ^ k * qPochhammerInfIn (-(‖q‖ / r)) ‖q‖ :=
    (Finset.prod_nonneg fun i _ => norm_nonneg _).trans hPb
  have hKa0 : 0 ≤ qPochhammerInfIn (-‖q / a‖) ‖q‖ / ‖qPochhammerInfIn (q / a) q‖ :=
    (inv_nonneg.mpr (norm_nonneg _)).trans hKa
  calc (∏ i ∈ Finset.range k, ‖q ^ (i + 1) - b‖) /
          (‖a‖ ^ k * ‖finiteQPochhammerIn (q / a) q k‖) * (‖z‖ ^ k)⁻¹ * ‖qPochhammerInfIn b q‖
      = (∏ i ∈ Finset.range k, ‖q ^ (i + 1) - b‖) * ‖finiteQPochhammerIn (q / a) q k‖⁻¹ *
          ‖qPochhammerInfIn b q‖ * ((‖a‖ ^ k)⁻¹ * (‖z‖ ^ k)⁻¹) := by ring
    _ ≤ (r ^ k * qPochhammerInfIn (-(‖q‖ / r)) ‖q‖) *
          (qPochhammerInfIn (-‖q / a‖) ‖q‖ / ‖qPochhammerInfIn (q / a) q‖) *
          qPochhammerInfIn (-r) ‖q‖ * ((‖a‖ ^ k)⁻¹ * (‖z‖ ^ k)⁻¹) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul (mul_le_mul hPb hKa (inv_nonneg.mpr (norm_nonneg _)) hM'0) hMr
          (norm_nonneg _) (mul_nonneg hM'0 hKa0)
    _ = _ := by rw [div_pow, mul_pow]; ring

/-- A summable majorant of the cleared series, uniform on the disc `‖b‖ ≤ r`, for
`0 < r < ‖a‖‖z‖`. -/
theorem exists_summable_majorant_onePsiOneCleared (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (ha0 : a ≠ 0)
    (hz : ‖z‖ < 1) (hz0 : z ≠ 0) (haq : qPochhammerInfIn (q / a) q ≠ 0) {r : ℝ} (hr : 0 < r)
    (hraz : r < ‖a‖ * ‖z‖) :
    ∃ u : ℤ → ℝ, Summable u ∧ ∀ (n : ℤ) (c : ℂ), ‖c‖ ≤ r → ‖onePsiOneCleared a c q z n‖ ≤ u n := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  set ρ : ℝ := max ‖z‖ (r / (‖a‖ * ‖z‖)) with hρ
  have hρ0 : 0 ≤ ρ := le_max_of_le_left (norm_nonneg z)
  have hρ1 : ρ < 1 := max_lt hz ((div_lt_one (mul_pos hapos hzpos)).mpr hraz)
  set K₁ : ℝ := qPochhammerInfIn (-‖a‖) ‖q‖ * qPochhammerInfIn (-r) ‖q‖ with hK₁def
  set K₂ : ℝ := qPochhammerInfIn (-(‖q‖ / r)) ‖q‖ *
    (qPochhammerInfIn (-‖q / a‖) ‖q‖ / ‖qPochhammerInfIn (q / a) q‖) *
    qPochhammerInfIn (-r) ‖q‖ with hK₂def
  have hA0 : 0 ≤ qPochhammerInfIn (-‖a‖) ‖q‖ :=
    zero_le_one.trans (one_le_qPochhammerInfIn_neg (norm_nonneg a) (norm_nonneg q) hq)
  have hMr0 : 0 ≤ qPochhammerInfIn (-r) ‖q‖ :=
    zero_le_one.trans (one_le_qPochhammerInfIn_neg hr.le (norm_nonneg q) hq)
  have hM'0 : 0 ≤ qPochhammerInfIn (-(‖q‖ / r)) ‖q‖ :=
    zero_le_one.trans
      (one_le_qPochhammerInfIn_neg (div_nonneg (norm_nonneg q) hr.le) (norm_nonneg q) hq)
  have hKa0 : 0 ≤ qPochhammerInfIn (-‖q / a‖) ‖q‖ / ‖qPochhammerInfIn (q / a) q‖ :=
    div_nonneg (zero_le_one.trans (one_le_qPochhammerInfIn_neg (norm_nonneg _) (norm_nonneg q) hq))
      (norm_nonneg _)
  have hK₁ : 0 ≤ K₁ := mul_nonneg hA0 hMr0
  have hK₂ : 0 ≤ K₂ := mul_nonneg (mul_nonneg hM'0 hKa0) hMr0
  refine ⟨fun n : ℤ => (K₁ + K₂) * ρ ^ n.natAbs, ?_, ?_⟩
  · refine Summable.of_nat_of_neg ?_ ?_
    · simpa [Int.natAbs_natCast] using (summable_geometric_of_lt_one hρ0 hρ1).mul_left (K₁ + K₂)
    · simpa [Int.natAbs_neg, Int.natAbs_natCast] using
        (summable_geometric_of_lt_one hρ0 hρ1).mul_left (K₁ + K₂)
  · intro n c hc
    rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
    · dsimp only
      rw [Int.natAbs_natCast]
      calc ‖onePsiOneCleared a c q z k‖ ≤ K₁ * ‖z‖ ^ k :=
            norm_onePsiOneCleared_natCast_le hq hc k
        _ ≤ (K₁ + K₂) * ρ ^ k :=
            mul_le_mul (le_add_of_nonneg_right hK₂)
              (pow_le_pow_left₀ (norm_nonneg z) (le_max_left _ _) k)
              (pow_nonneg (norm_nonneg z) k) (add_nonneg hK₁ hK₂)
    · dsimp only
      rw [Int.natAbs_neg, Int.natAbs_natCast]
      calc ‖onePsiOneCleared a c q z (-k)‖ ≤ K₂ * (r / (‖a‖ * ‖z‖)) ^ k :=
            norm_onePsiOneCleared_neg_natCast_le hq hq0 ha0 hz0 haq hr hc k
        _ ≤ (K₁ + K₂) * ρ ^ k :=
            mul_le_mul (le_add_of_nonneg_left hK₁)
              (pow_le_pow_left₀ (by positivity) (le_max_right _ _) k)
              (pow_nonneg (by positivity) k) (add_nonneg hK₁ hK₂)

/-- **Ramanujan's `₁ψ₁` summation, cleared form.**  For `‖q‖ < 1`, `q ≠ 0`, `a ≠ 0` with
`(q/a;q)_∞ ≠ 0`, `‖z‖ < 1` and `‖b‖ < ‖az‖`,
`∑_{n ∈ ℤ} (a;q)_n z^n (bq^n;q)_∞ = (q, b/a, az, q/(az); q)_∞ / (q/a, z, b/(az); q)_∞`.
No nonvanishing of `(b;q)_∞` is needed. -/
theorem hasSum_onePsiOneCleared (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (ha0 : a ≠ 0)
    (haq : qPochhammerInfIn (q / a) q ≠ 0) (hz : ‖z‖ < 1) (hb : ‖b‖ < ‖a * z‖) :
    HasSum (onePsiOneCleared a b q z) (onePsiOneProduct a b q z) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [mul_zero, norm_zero] at hb
    exact absurd hb (not_lt.mpr (norm_nonneg b))
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rw [norm_mul] at hb
  set r : ℝ := (‖b‖ + ‖a‖ * ‖z‖) / 2 with hr_def
  have hr : 0 < r := by positivity
  have hbr : ‖b‖ < r := by rw [hr_def]; linarith
  have hraz : r < ‖a‖ * ‖z‖ := by rw [hr_def]; linarith
  obtain ⟨u, hu, hbound⟩ :=
    exists_summable_majorant_onePsiOneCleared hq hq0 ha0 hz hz0 haq hr hraz
  have hF : DifferentiableOn ℂ (fun c : ℂ => ∑' n : ℤ, onePsiOneCleared a c q z n)
      (Metric.ball 0 r) := by
    refine Complex.differentiableOn_tsum_of_summable_norm hu
      (fun n => (differentiable_onePsiOneCleared hq n).differentiableOn) Metric.isOpen_ball
      fun n c hc => hbound n c ?_
    rw [Metric.mem_ball, dist_zero_right] at hc
    exact hc.le
  have hG : DifferentiableOn ℂ (fun c : ℂ => onePsiOneProduct a c q z) (Metric.ball 0 r) := by
    have hnum : Differentiable ℂ fun c : ℂ => qPochhammerInfIn q q * qPochhammerInfIn (c / a) q *
        qPochhammerInfIn (a * z) q * qPochhammerInfIn (q / (a * z)) q := by
      have h : Differentiable ℂ fun c : ℂ => qPochhammerInfIn (c / a) q :=
        (differentiable_qPochhammerInfIn hq).comp (differentiable_id.div_const a)
      exact ((h.const_mul _).mul_const _).mul_const _
    have hden : Differentiable ℂ fun c : ℂ => qPochhammerInfIn (q / a) q * qPochhammerInfIn z q *
        qPochhammerInfIn (c / (a * z)) q := by
      have h : Differentiable ℂ fun c : ℂ => qPochhammerInfIn (c / (a * z)) q :=
        (differentiable_qPochhammerInfIn hq).comp (differentiable_id.div_const (a * z))
      exact h.const_mul _
    refine hnum.differentiableOn.div hden.differentiableOn fun c hc => ?_
    rw [Metric.mem_ball, dist_zero_right] at hc
    refine mul_ne_zero (mul_ne_zero haq (qPochhammerInfIn_ne_zero_of_norm_lt_one hq hz))
      (qPochhammerInfIn_ne_zero_of_norm_lt_one hq ?_)
    rw [norm_div, norm_mul, div_lt_one (mul_pos hapos hzpos)]
    exact hc.trans hraz
  have hFa := hF.analyticOnNhd Metric.isOpen_ball
  have hGa := hG.analyticOnNhd Metric.isOpen_ball
  have hconn : IsPreconnected (Metric.ball (0 : ℂ) r) := (convex_ball (0 : ℂ) r).isPreconnected
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := Metric.mem_ball_self hr
  have hfreq : ∃ᶠ c in 𝓝[≠] (0 : ℂ),
      (∑' n : ℤ, onePsiOneCleared a c q z n) = onePsiOneProduct a c q z := by
    have ht : Tendsto (fun m : ℕ => q ^ (m + 1)) atTop (𝓝[≠] (0 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨(tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).comp (tendsto_add_atTop_nat 1),
        Eventually.of_forall fun m => by simp [hq0]⟩
    refine ht.frequently (Eventually.frequently ?_)
    have hlim : Tendsto (fun m : ℕ => ‖q ^ (m + 1) / (a * z)‖) atTop (𝓝 0) := by
      have h1 : Tendsto (fun m : ℕ => q ^ (m + 1) / (a * z)) atTop (𝓝 0) := by
        have := ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).comp
          (tendsto_add_atTop_nat 1)).div_const (a * z)
        rwa [zero_div] at this
      simpa using h1.norm
    filter_upwards [hlim.eventually (Iio_mem_nhds one_pos)] with m hm
    have hm' : finiteQPochhammerZ a q (-m) ≠ 0 := by
      rw [finiteQPochhammerZ_neg_natCast_eq ha0 hq0]
      exact div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
        (pow_ne_zero _ (inv_ne_zero ha0))) (pow_ne_zero _ hq0))
        (finiteQPochhammerIn_ne_zero_of_qPochhammerInfIn_ne_zero _ hq haq m)
    show (∑' n : ℤ, onePsiOneCleared a (q ^ (m + 1)) q z n) = onePsiOneProduct a (q ^ (m + 1)) q z
    rw [(hasSum_onePsiOneCleared_pow hq hq0 hz hz0 hm').tsum_eq,
      onePsiOneProduct_pow hq hq0 ha0 hz hz0 haq hm]
  have hEq := hFa.eqOn_of_preconnected_of_frequently_eq hGa hconn h0 hfreq
  have hbmem : b ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hbr
  have hsum : Summable (onePsiOneCleared a b q z) :=
    Summable.of_norm_bounded hu fun n => hbound n b hbr.le
  have h : (∑' n : ℤ, onePsiOneCleared a b q z n) = onePsiOneProduct a b q z := hEq hbmem
  rw [← h]
  exact hsum.hasSum

/-- **Ramanujan's `₁ψ₁` summation** (thm:1psi1).  For `‖q‖ < 1`, `q ≠ 0`, `a ≠ 0` with
`(q/a;q)_∞ ≠ 0`, `‖b/a‖ < ‖z‖ < 1` and `(b;q)_∞ ≠ 0`,
`∑_{n ∈ ℤ} (a;q)_n/(b;q)_n · z^n = (q, b/a, az, q/(az); q)_∞ / (b, q/a, z, b/(az); q)_∞`. -/
theorem hasSum_onePsiOne (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (ha0 : a ≠ 0)
    (haq : qPochhammerInfIn (q / a) q ≠ 0) (hb : qPochhammerInfIn b q ≠ 0)
    (hbz : ‖b / a‖ < ‖z‖) (hz : ‖z‖ < 1) :
    HasSum (onePsiOneTerm a b q z)
      (qPochhammerInfIn q q * qPochhammerInfIn (b / a) q * qPochhammerInfIn (a * z) q *
          qPochhammerInfIn (q / (a * z)) q /
        (qPochhammerInfIn b q * qPochhammerInfIn (q / a) q * qPochhammerInfIn z q *
          qPochhammerInfIn (b / (a * z)) q)) := by
  have hb' : ‖b‖ < ‖a * z‖ := by
    rw [norm_div, div_lt_iff₀ (norm_pos_iff.mpr ha0)] at hbz
    rw [norm_mul, mul_comm]
    exact hbz
  have h := hasSum_onePsiOneCleared hq hq0 ha0 haq hz hb'
  have hfun : onePsiOneCleared a b q z = fun n => qPochhammerInfIn b q * onePsiOneTerm a b q z n :=
    funext fun n => onePsiOneCleared_eq hq hq0 hb n
  rw [hfun] at h
  have h2 := h.mul_left (qPochhammerInfIn b q)⁻¹
  have hfun2 : (fun n => (qPochhammerInfIn b q)⁻¹ * (qPochhammerInfIn b q * onePsiOneTerm a b q z n)) =
      onePsiOneTerm a b q z := funext fun n => inv_mul_cancel_left₀ hb _
  rw [hfun2] at h2
  have hval : (qPochhammerInfIn b q)⁻¹ * onePsiOneProduct a b q z =
      qPochhammerInfIn q q * qPochhammerInfIn (b / a) q * qPochhammerInfIn (a * z) q *
          qPochhammerInfIn (q / (a * z)) q /
        (qPochhammerInfIn b q * qPochhammerInfIn (q / a) q * qPochhammerInfIn z q *
          qPochhammerInfIn (b / (a * z)) q) := by
    rw [onePsiOneProduct]
    ring
  rw [← hval]
  exact h2

/-- The value of `₁ψ₁` as a `tsum`. -/
theorem onePsiOne_eq (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (ha0 : a ≠ 0)
    (haq : qPochhammerInfIn (q / a) q ≠ 0) (hb : qPochhammerInfIn b q ≠ 0)
    (hbz : ‖b / a‖ < ‖z‖) (hz : ‖z‖ < 1) :
    onePsiOne a b q z =
      qPochhammerInfIn q q * qPochhammerInfIn (b / a) q * qPochhammerInfIn (a * z) q *
          qPochhammerInfIn (q / (a * z)) q /
        (qPochhammerInfIn b q * qPochhammerInfIn (q / a) q * qPochhammerInfIn z q *
          qPochhammerInfIn (b / (a * z)) q) :=
  (hasSum_onePsiOne hq hq0 ha0 haq hb hbz hz).tsum_eq

end Complex

end Fabius
