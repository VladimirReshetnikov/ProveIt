import FabiusFunction.FabiusQBinomialFormula
import FabiusFunction.ThueMorseBinomialLog

/-!
# A raw-coordinate q-binomial formula for inverse dyadic Fabius values

This module proves, for every `q : ℚ` and `n : ℕ`, the Wolfram Language
identity whose inner sum contains `(r + q)^(n+k)` and whose normalization
contains `(-2)^(n^2)`.

The proof reflects each dyadic Thue--Morse block.  Under
`r ↦ 2^k - 1 - r`, the sign gains `(-1)^k`, while the centered coordinate
with translation `1-q` becomes `-(r+q)`.  In degree `n+k` the combined sign
is therefore `(-1)^n`, independently of `k`.  This is exactly canceled by
the sign in `(-2)^(n^2)`, since `n^2` and `n` have the same parity.

Lean's natural-power convention includes `0 ^ 0 = 1`.  The theorem
`qBinomialThueMorseRawTranslatedFormula_zero` records the resulting `n = 0`
value explicitly, including the case `q = 0`.

The raw/centered numerator sign is also recorded in both orientations.  This
makes the involutive `(-1)^n` normalization reusable by scalar transports
without repeating the parity calculation.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

noncomputable section

/-- The Wolfram sign `(-1)^ThueMorse[r]` agrees with the repository's signed
Thue--Morse convention.

This is the `ℚ` instance of `neg_one_pow_thueMorseBit_ring`
(`ThueMorseBinomialLog`), which holds over an arbitrary `[Ring R]`.  The
statement and name are unchanged, so all existing callers are unaffected;
new call sites over a general ring, a field, or `ℂ` should use the ring-level
form directly. -/
theorem neg_one_pow_thueMorseBit (r : ℕ) :
    (-1 : ℚ) ^ thueMorseBit r = (thueMorseSign r : ℚ) :=
  neg_one_pow_thueMorseBit_ring (R := ℚ) r

/-- The raw-coordinate inner power sum
`sum_{r < 2^k} (-1)^ThueMorse[r] (r+q)^d`. -/
def thueMorseRawTranslatedPowerSum (q : ℚ) (k d : ℕ) : ℚ :=
  ∑ r ∈ Finset.range (2 ^ k),
    (thueMorseSign r : ℚ) * ((r : ℚ) + q) ^ d

/-- At block size one, the raw sum is just `q^d`; in particular its value at
`q = d = 0` is `0^0 = 1`. -/
@[simp] theorem thueMorseRawTranslatedPowerSum_zero
    (q : ℚ) (d : ℕ) :
    thueMorseRawTranslatedPowerSum q 0 d = q ^ d := by
  simp [thueMorseRawTranslatedPowerSum, thueMorseSign, binaryWeight]

/-- Dyadic reflection converts centered translation `1-q` into the raw
coordinate `r+q`. -/
theorem thueMorseTranslatedPowerSum_one_sub_eq_raw
    (q : ℚ) (k d : ℕ) :
    thueMorseTranslatedPowerSum (1 - q) k d =
      (-1 : ℚ) ^ (k + d) * thueMorseRawTranslatedPowerSum q k d := by
  rw [thueMorseTranslatedPowerSum_eq_sum_range,
    ← Finset.sum_range_reflect
      (fun r => (thueMorseSign r : ℚ) *
        ((r : ℚ) - (2 : ℚ) ^ k + (1 - q)) ^ d) (2 ^ k)]
  rw [thueMorseRawTranslatedPowerSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrlt : r < 2 ^ k := Finset.mem_range.mp hr
  rw [thueMorseSign_dyadic_complement k r hrlt]
  push_cast
  have hpow : 0 < 2 ^ k := by positivity
  have hbase :
      (((2 ^ k - 1 - r : ℕ) : ℚ) - (2 : ℚ) ^ k + (1 - q)) =
        -((r : ℚ) + q) := by
    rw [Nat.cast_sub (by omega : r ≤ 2 ^ k - 1),
      Nat.cast_sub (by omega : 1 ≤ 2 ^ k)]
    push_cast
    ring
  rw [hbase, neg_pow ((r : ℚ) + q) d, pow_add]
  ring

/-- In the diagonal degree `n+k`, the reflection sign is independent of
`k`. -/
theorem thueMorseTranslatedPowerSum_one_sub_eq_raw_diagonal
    (q : ℚ) (n k : ℕ) :
    thueMorseTranslatedPowerSum (1 - q) k (n + k) =
      (-1 : ℚ) ^ n * thueMorseRawTranslatedPowerSum q k (n + k) := by
  rw [thueMorseTranslatedPowerSum_one_sub_eq_raw]
  have heven : Even (2 * k) := even_two_mul k
  rw [show k + (n + k) = n + 2 * k by omega, pow_add,
    heven.neg_one_pow, mul_one]

/-- The outer numerator formed from the raw-coordinate power sums. -/
noncomputable def qBinomialThueMorseRawTranslatedNumerator
    (q : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    qBinomial n k (1 / 2) /
        ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) *
      thueMorseRawTranslatedPowerSum q k (n + k)

/-- The centered numerator is `(-1)^n` times the raw-coordinate numerator. -/
theorem qBinomialThueMorseNumerator_eq_neg_one_pow_mul_raw
    (q : ℚ) (n : ℕ) :
    qBinomialThueMorseNumerator n =
      (-1 : ℚ) ^ n * qBinomialThueMorseRawTranslatedNumerator q n := by
  rw [← qBinomialThueMorseTranslatedNumerator_eq_centered (1 - q) n]
  rw [qBinomialThueMorseTranslatedNumerator,
    qBinomialThueMorseRawTranslatedNumerator, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [thueMorseTranslatedPowerSum_one_sub_eq_raw_diagonal]
  ring

/-- Reverse orientation of the raw/centered numerator normalization.  Since
`(-1)^n` is its own inverse, the same sign converts centered coordinates back
to raw coordinates. -/
theorem qBinomialThueMorseRawTranslatedNumerator_eq_neg_one_pow_mul_centered
    (q : ℚ) (n : ℕ) :
    qBinomialThueMorseRawTranslatedNumerator q n =
      (-1 : ℚ) ^ n * qBinomialThueMorseNumerator n := by
  have h := qBinomialThueMorseNumerator_eq_neg_one_pow_mul_raw q n
  have hsquare : ((-1 : ℚ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
  calc
    qBinomialThueMorseRawTranslatedNumerator q n =
        1 * qBinomialThueMorseRawTranslatedNumerator q n := by ring
    _ = ((-1 : ℚ) ^ n) ^ 2 *
        qBinomialThueMorseRawTranslatedNumerator q n := by rw [hsquare]
    _ = (-1 : ℚ) ^ n * qBinomialThueMorseNumerator n := by rw [h]; ring

/-- The rational right-hand side with raw powers `(r+q)^(n+k)` and
denominator `(-2)^(n^2)`. -/
noncomputable def qBinomialThueMorseRawTranslatedFormula
    (q : ℚ) (n : ℕ) : ℚ :=
  (1 / ((-2 : ℚ) ^ (n ^ 2) * qPochhammer (1 / 2) (1 / 2) n)) *
    qBinomialThueMorseRawTranslatedNumerator q n

private theorem neg_one_pow_nat_sq (n : ℕ) :
    (-1 : ℚ) ^ (n ^ 2) = (-1 : ℚ) ^ n := by
  rw [pow_two]
  rcases Nat.even_or_odd n with heven | hodd
  · rw [heven.neg_one_pow, (heven.mul_right n).neg_one_pow]
  · rw [hodd.neg_one_pow, (hodd.mul hodd).neg_one_pow]

/-- Exact sign normalization for the displayed `(-2)^(n^2)` denominator. -/
theorem neg_two_pow_nat_sq (n : ℕ) :
    (-2 : ℚ) ^ (n ^ 2) =
      (-1 : ℚ) ^ n * (2 : ℚ) ^ (n ^ 2) := by
  rw [show (-2 : ℚ) = (-1 : ℚ) * 2 by norm_num,
    mul_pow, neg_one_pow_nat_sq]

/-- The raw-coordinate expression equals the previously established centered
q-binomial formula. -/
theorem qBinomialThueMorseRawTranslatedFormula_eq_centered
    (q : ℚ) (n : ℕ) :
    qBinomialThueMorseRawTranslatedFormula q n =
      qBinomialThueMorseFormula n := by
  rw [qBinomialThueMorseRawTranslatedFormula,
    qBinomialThueMorseFormula,
    qBinomialThueMorseNumerator_eq_neg_one_pow_mul_raw q n,
    neg_two_pow_nat_sq]
  field_simp
  have hsquare : ((-1 : ℚ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
  rw [hsquare, one_mul]

/-- Exact rational form of the arbitrary-`q` raw-coordinate identity. -/
theorem fabiusAtInverseTwoPow_eq_qBinomialThueMorseRawTranslatedFormula
    (q : ℚ) (n : ℕ) :
    fabiusAtInverseTwoPow n =
      qBinomialThueMorseRawTranslatedFormula q n := by
  rw [qBinomialThueMorseRawTranslatedFormula_eq_centered,
    fabiusAtInverseTwoPow_eq_qBinomialThueMorseFormula]

/-- Real-valued form for any bounded function satisfying the Fabius
characterization. -/
theorem fabiusFunction_inverse_two_pow_eq_qBinomialThueMorseRawTranslatedFormula
    (F : BoundedFabius) (hF : IsFabius F) (q : ℚ) (n : ℕ) :
    fabiusReal F (((2 : ℝ) ^ n)⁻¹) =
      (qBinomialThueMorseRawTranslatedFormula q n : ℝ) := by
  rw [qBinomialThueMorseRawTranslatedFormula_eq_centered,
    fabiusFunction_inverse_two_pow_eq_qBinomialThueMorseFormula F hF]

/-- Canonical real-valued form of the arbitrary-`q` identity. -/
theorem fabius_inverse_two_pow_eq_qBinomialThueMorseRawTranslatedFormula
    (q : ℚ) (n : ℕ) :
    fabiusReal fabius (((2 : ℝ) ^ n)⁻¹) =
      (qBinomialThueMorseRawTranslatedFormula q n : ℝ) :=
  fabiusFunction_inverse_two_pow_eq_qBinomialThueMorseRawTranslatedFormula
    fabius fabius_spec q n

/-- At `n = 0`, the formula is `1` for every `q`; at `q = 0` its sole inner
power is literally `0^0`, evaluated as `1`. -/
@[simp] theorem qBinomialThueMorseRawTranslatedFormula_zero (q : ℚ) :
    qBinomialThueMorseRawTranslatedFormula q 0 = 1 := by
  norm_num [qBinomialThueMorseRawTranslatedFormula,
    qBinomialThueMorseRawTranslatedNumerator,
    thueMorseRawTranslatedPowerSum, qBinomial, qPochhammer,
    finiteQPochhammer, thueMorseSign, binaryWeight]

/-- Literal nested-sum theorem using the signed Thue--Morse convention. -/
theorem fabiusAtInverseTwoPow_eq_qBinomialThueMorse_rawTranslated_sum
    (q : ℚ) (n : ℕ) :
    fabiusAtInverseTwoPow n =
      (1 / ((-2 : ℚ) ^ (n ^ 2) *
          qPochhammer (1 / 2) (1 / 2) n)) *
        ∑ k ∈ Finset.range (n + 1),
          qBinomial n k (1 / 2) /
              ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) *
            ∑ r ∈ Finset.range (2 ^ k),
              (thueMorseSign r : ℚ) *
                ((r : ℚ) + q) ^ (n + k) := by
  rw [fabiusAtInverseTwoPow_eq_qBinomialThueMorseRawTranslatedFormula]
  rfl

/-- The fully literal Wolfram-style theorem for every `q : ℚ` and `n : ℕ`.
The exponent `thueMorseBit r` is the zero-one value `ThueMorse[r]`. -/
theorem fabiusAtInverseTwoPow_eq_qBinomialThueMorse_add_sum
    (q : ℚ) (n : ℕ) :
    fabiusAtInverseTwoPow n =
      (1 / ((-2 : ℚ) ^ (n ^ 2) *
          qPochhammer (1 / 2) (1 / 2) n)) *
        ∑ k ∈ Finset.range (n + 1),
          qBinomial n k (1 / 2) /
              ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) *
            ∑ r ∈ Finset.range (2 ^ k),
              (-1 : ℚ) ^ thueMorseBit r *
                ((r : ℚ) + q) ^ (n + k) := by
  simpa only [neg_one_pow_thueMorseBit] using
    fabiusAtInverseTwoPow_eq_qBinomialThueMorse_rawTranslated_sum q n

/-- Canonical real-valued theorem with both finite sums displayed literally. -/
theorem fabius_inverse_two_pow_eq_qBinomialThueMorse_add_sum
    (q : ℚ) (n : ℕ) :
    fabiusReal fabius (((2 : ℝ) ^ n)⁻¹) =
      (((1 / ((-2 : ℚ) ^ (n ^ 2) *
          qPochhammer (1 / 2) (1 / 2) n)) *
        ∑ k ∈ Finset.range (n + 1),
          qBinomial n k (1 / 2) /
              ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) *
            ∑ r ∈ Finset.range (2 ^ k),
              (-1 : ℚ) ^ thueMorseBit r *
                ((r : ℚ) + q) ^ (n + k) : ℚ) : ℝ) := by
  rw [fabius_inverse_two_pow_eq_qBinomialThueMorseRawTranslatedFormula]
  exact congrArg (fun x : ℚ => (x : ℝ))
    ((fabiusAtInverseTwoPow_eq_qBinomialThueMorseRawTranslatedFormula q n).symm.trans
      (fabiusAtInverseTwoPow_eq_qBinomialThueMorse_add_sum q n))

/-- The original `q = 0` formula, with the inner power `r^(n+k)`. -/
theorem fabiusAtInverseTwoPow_eq_qBinomialThueMorse_uncentered_sum
    (n : ℕ) :
    fabiusAtInverseTwoPow n =
      (1 / ((-2 : ℚ) ^ (n ^ 2) *
          qPochhammer (1 / 2) (1 / 2) n)) *
        ∑ k ∈ Finset.range (n + 1),
          qBinomial n k (1 / 2) /
              ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) *
            ∑ r ∈ Finset.range (2 ^ k),
              (-1 : ℚ) ^ thueMorseBit r *
                (r : ℚ) ^ (n + k) := by
  simpa only [add_zero] using
    fabiusAtInverseTwoPow_eq_qBinomialThueMorse_add_sum 0 n

/-- Canonical real-valued `q = 0` specialization. -/
theorem fabius_inverse_two_pow_eq_qBinomialThueMorse_uncentered_sum
    (n : ℕ) :
    fabiusReal fabius (((2 : ℝ) ^ n)⁻¹) =
      (((1 / ((-2 : ℚ) ^ (n ^ 2) *
          qPochhammer (1 / 2) (1 / 2) n)) *
        ∑ k ∈ Finset.range (n + 1),
          qBinomial n k (1 / 2) /
              ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) *
            ∑ r ∈ Finset.range (2 ^ k),
              (-1 : ℚ) ^ thueMorseBit r *
                (r : ℚ) ^ (n + k) : ℚ) : ℝ) := by
  simpa only [add_zero] using
    fabius_inverse_two_pow_eq_qBinomialThueMorse_add_sum 0 n

end

end Fabius
