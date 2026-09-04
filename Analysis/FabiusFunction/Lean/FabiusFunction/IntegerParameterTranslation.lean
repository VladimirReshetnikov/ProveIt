import FabiusFunction.QPochhammerElementaryIdentities
import FabiusFunction.QPfaffSaalschutz

/-!
# Integer-parameter translation rules

The three rules that convert shifted factorials with integer parameters into Gaussian
coefficients and `q`-factorial blocks:

* `(q^{a+1};q)_n / (q;q)_n = [a+n, n]_q`,
* `(q^{-m};q)_k / (q;q)_k = (-1)^k q^{-mk + C(k,2)} [m, k]_q` for `k ≤ m`,
* `(q^{a+1};q)_n = (q;q)_{a+n} / (q;q)_a`,

in any field, under the displayed nonvanishing hypotheses.  They are the mechanical content of
the certified integral-parameter translation of the monograph.

## Main declarations

* `finiteQPochhammerIn_pow_succ_div_self`, `finiteQPochhammerIn_inv_pow_div_self`,
  `finiteQPochhammerIn_pow_succ_eq_div`.
-/

set_option autoImplicit false

namespace Fabius

variable {K : Type*} [Field K] {q : K}

/-- `(q^{a+1};q)_n / (q;q)_n = [a+n, n]_q`. -/
theorem finiteQPochhammerIn_pow_succ_div_self (a : ℕ) {n : ℕ}
    (hqn : finiteQPochhammerIn q q n ≠ 0) :
    finiteQPochhammerIn (q ^ (a + 1)) q n / finiteQPochhammerIn q q n =
      gaussianBinomial q (a + n) n := by
  have h := finiteQPochhammerIn_self_mul_gaussianBinomial q (n := a + n) (k := n) (by omega)
  rw [Nat.add_sub_cancel] at h
  rw [← h, mul_div_cancel_left₀ _ hqn]

/-- `(q^{-m};q)_k / (q;q)_k = (-1)^k q^{-mk} q^{C(k,2)} [m, k]_q` for `k ≤ m`, with
`q^{-m} = (q^m)⁻¹` and `q^{-mk} = (q^{mk})⁻¹`. -/
theorem finiteQPochhammerIn_inv_pow_div_self (hq0 : q ≠ 0) {m k : ℕ} (hk : k ≤ m)
    (hqk : finiteQPochhammerIn q q k ≠ 0) :
    finiteQPochhammerIn (q ^ m)⁻¹ q k / finiteQPochhammerIn q q k =
      (-1) ^ k * (q ^ (m * k))⁻¹ * q ^ k.choose 2 * gaussianBinomial q m k := by
  have h1 := pow_mul_finiteQPochhammerIn_inv_pow_eq q hq0 hk
  have h2 := finiteQPochhammerIn_self_mul_gaussianBinomial q hk
  have hqm : q ^ (m * k) ≠ 0 := pow_ne_zero _ hq0
  rw [div_eq_iff hqk]
  have hsym : finiteQPochhammerIn (q ^ m)⁻¹ q k =
      (-1) ^ k * q ^ k.choose 2 * finiteQPochhammerIn (q ^ (m - k + 1)) q k / q ^ (m * k) := by
    rw [← h1, mul_div_cancel_left₀ _ hqm]
  rw [hsym, ← h2, div_eq_mul_inv]
  ring

/-- `(q^{a+1};q)_n = (q;q)_{a+n} / (q;q)_a`. -/
theorem finiteQPochhammerIn_pow_succ_eq_div (a n : ℕ) (hqa : finiteQPochhammerIn q q a ≠ 0) :
    finiteQPochhammerIn (q ^ (a + 1)) q n =
      finiteQPochhammerIn q q (a + n) / finiteQPochhammerIn q q a := by
  rw [finiteQPochhammerIn_add q q a n, ← pow_succ', mul_div_cancel_left₀ _ hqa]

end Fabius
