import FabiusFunction.FabiusRawQBinomialFormula
import FabiusFunction.TaylorReduction
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Roots

/-!
# q-binomial coefficients in the Fabius Taylor reduction

This module identifies the finite q-binomial--Thue--Morse polynomial in the
global Fabius expansion with the Taylor polynomial `fabiusReductionSum`.

The common translation is first treated as an indeterminate in
`Polynomial ℚ`.  Its rational evaluations are constant by the previously
proved translation theorem, hence the polynomial itself is constant.  It can
therefore be evaluated at an arbitrary element of any field over `ℚ` (and
hence of characteristic zero), in particular at any real or complex `q`.

The individual translated Thue--Morse block has a sharper polynomial
structure.  Its coefficient of translation degree `j` is `d.choose j` times
the centered moment of complementary degree `d - j`.  Consequently the block
is zero for `d < k`, while for `k ≤ d` it has translation degree exactly
`d - k`.  These blocks satisfy a finite Appell calculus: translation obeys the
binomial addition law, and the `j`-th Hasse derivative is `d.choose j` times
the block of degree `d - j`, without a side condition on `j`.  The boundary
cases are made explicit: `k = 0` gives `(X - 1) ^ d`, `d < k` gives the zero
polynomial (whose `natDegree` is zero), and `d = k` gives the nonzero sharp
Prouhet constant.

For each `n`, the normalized numerator is

`2^n * halfMoment n / n!`.

After reversing `n` in the finite sum and matching the triangular exponents
of two, the fully scaled q-binomial polynomial is exactly
`fabiusReductionSum m y`.  The `m = 0` theorem is explicit; as throughout
Lean, natural powers satisfy `0 ^ 0 = 1`.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

noncomputable section

/-- The translated inner Thue--Morse sum, as a polynomial in the translation. -/
def thueMorseTranslatedPowerSumPolynomial (k d : ℕ) : Polynomial ℚ :=
  ∑ r ∈ Finset.range (2 ^ k),
    Polynomial.C (thueMorseSign r : ℚ) *
      (Polynomial.X + Polynomial.C ((r : ℚ) - (2 : ℚ) ^ k)) ^ d

/-- The complete q-binomial numerator, as a polynomial in the common translation. -/
def qBinomialThueMorseTranslatedNumeratorPolynomial (n : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C
      (qBinomial n k (1 / 2) /
        ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ))) *
      thueMorseTranslatedPowerSumPolynomial k (n + k)

/-- Rational evaluation of the inner block polynomial recovers the translated
Thue--Morse power sum. -/
@[simp] theorem thueMorseTranslatedPowerSumPolynomial_eval
    (q : ℚ) (k d : ℕ) :
    (thueMorseTranslatedPowerSumPolynomial k d).eval q =
      thueMorseTranslatedPowerSum q k d := by
  rw [thueMorseTranslatedPowerSumPolynomial,
    thueMorseTranslatedPowerSum_eq_sum_range]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro r _hr
  congr 1
  ring

/-- The coefficient of translation degree `j` is the corresponding binomial
coefficient times the centered Thue--Morse moment of complementary degree. -/
@[simp] theorem coeff_thueMorseTranslatedPowerSumPolynomial
    (k d j : ℕ) :
    (thueMorseTranslatedPowerSumPolynomial k d).coeff j =
      (d.choose j : ℚ) * thueMorseCenteredPowerSum k (d - j) := by
  rw [thueMorseTranslatedPowerSumPolynomial,
    Polynomial.finsetSum_coeff,
    thueMorseCenteredPowerSum_eq_sum_range]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  ring

/-- Translation of a translated Thue--Morse block satisfies the finite Appell
addition law. -/
theorem thueMorseTranslatedPowerSumPolynomial_comp_X_add_C
    (c : ℚ) (k d : ℕ) :
    (thueMorseTranslatedPowerSumPolynomial k d).comp
        (Polynomial.X + Polynomial.C c) =
      ∑ j ∈ Finset.range (d + 1),
        Polynomial.C ((d.choose j : ℚ) * c ^ j) *
          thueMorseTranslatedPowerSumPolynomial k (d - j) := by
  apply Polynomial.funext
  intro q
  simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    thueMorseTranslatedPowerSumPolynomial_eval]
  simp_rw [thueMorseTranslatedPowerSum_eq_sum_range]
  calc
    _ = ∑ r ∈ Finset.range (2 ^ k),
        (thueMorseSign r : ℚ) *
          (c + ((r : ℚ) - (2 : ℚ) ^ k + q)) ^ d := by
          apply Finset.sum_congr rfl
          intro r _hr
          congr 1
          ring
    _ = ∑ r ∈ Finset.range (2 ^ k),
        (thueMorseSign r : ℚ) *
          (∑ j ∈ Finset.range (d + 1),
            c ^ j *
              ((r : ℚ) - (2 : ℚ) ^ k + q) ^ (d - j) *
                (d.choose j : ℚ)) := by
          apply Finset.sum_congr rfl
          intro r _hr
          rw [add_pow]
    _ = ∑ r ∈ Finset.range (2 ^ k),
        ∑ j ∈ Finset.range (d + 1),
          (thueMorseSign r : ℚ) *
            (c ^ j *
              ((r : ℚ) - (2 : ℚ) ^ k + q) ^ (d - j) *
                (d.choose j : ℚ)) := by
          apply Finset.sum_congr rfl
          intro r _hr
          rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.range (d + 1),
        ∑ r ∈ Finset.range (2 ^ k),
          (thueMorseSign r : ℚ) *
            (c ^ j *
              ((r : ℚ) - (2 : ℚ) ^ k + q) ^ (d - j) *
                (d.choose j : ℚ)) := by
          rw [Finset.sum_comm]
    _ = _ := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _hr
          ring

/-- The translated Thue--Morse blocks satisfy the Appell Hasse-derivative law.
The statement is total in `j`; when `d < j`, both sides vanish. -/
theorem thueMorseTranslatedPowerSumPolynomial_hasseDeriv
    (k d j : ℕ) :
    Polynomial.hasseDeriv j
        (thueMorseTranslatedPowerSumPolynomial k d) =
      Polynomial.C (d.choose j : ℚ) *
        thueMorseTranslatedPowerSumPolynomial k (d - j) := by
  ext m
  simp only [Polynomial.hasseDeriv_coeff,
    Polynomial.coeff_C_mul,
    coeff_thueMorseTranslatedPowerSumPolynomial]
  have hsub : d - (m + j) = d - j - m := by
    omega
  rw [hsub]
  have hchoose :
      (d.choose (m + j) : ℚ) * ((m + j).choose j : ℚ) =
        (d.choose j : ℚ) * ((d - j).choose m : ℚ) := by
    norm_cast
    simpa using
      (Nat.choose_mul (n := d) (k := m + j) (s := j) (by omega))
  calc
    _ =
        ((d.choose (m + j) : ℚ) * ((m + j).choose j : ℚ)) *
          thueMorseCenteredPowerSum k (d - j - m) := by
            ring
    _ =
        ((d.choose j : ℚ) * ((d - j).choose m : ℚ)) *
          thueMorseCenteredPowerSum k (d - j - m) := by
            rw [hchoose]
    _ = _ := by
          ring

/-- Ordinary differentiation lowers the exponent by one and multiplies by
the old exponent.  The `d = 0` case is included. -/
theorem thueMorseTranslatedPowerSumPolynomial_derivative
    (k d : ℕ) :
    (thueMorseTranslatedPowerSumPolynomial k d).derivative =
      Polynomial.C (d : ℚ) *
        thueMorseTranslatedPowerSumPolynomial k (d - 1) := by
  simpa only [Polynomial.hasseDeriv_one', Nat.choose_one_right] using
    thueMorseTranslatedPowerSumPolynomial_hasseDeriv k d 1

/-- Successor-indexed form of
`thueMorseTranslatedPowerSumPolynomial_derivative`. -/
theorem thueMorseTranslatedPowerSumPolynomial_derivative_succ
    (k d : ℕ) :
    (thueMorseTranslatedPowerSumPolynomial k (d + 1)).derivative =
      Polynomial.C ((d + 1 : ℕ) : ℚ) *
        thueMorseTranslatedPowerSumPolynomial k d := by
  simpa using
    thueMorseTranslatedPowerSumPolynomial_derivative k (d + 1)

private theorem coeff_thueMorseTranslatedPowerSumPolynomial_natSub
    (k d : ℕ) (hkd : k ≤ d) :
    (thueMorseTranslatedPowerSumPolynomial k d).coeff (d - k) =
      (d.choose k : ℚ) *
        ((-1 : ℚ) ^ k * (2 : ℚ) ^ k.choose 2 * (k.factorial : ℚ)) := by
  rw [coeff_thueMorseTranslatedPowerSumPolynomial,
    Nat.sub_sub_self hkd, Nat.choose_symm hkd,
    thueMorseCenteredPowerSum_self]

private theorem coeff_thueMorseTranslatedPowerSumPolynomial_natSub_ne_zero
    (k d : ℕ) (hkd : k ≤ d) :
    (thueMorseTranslatedPowerSumPolynomial k d).coeff (d - k) ≠ 0 := by
  rw [coeff_thueMorseTranslatedPowerSumPolynomial_natSub k d hkd]
  exact mul_ne_zero
    (Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hkd))
    (mul_ne_zero
      (mul_ne_zero (pow_ne_zero _ (by norm_num))
        (pow_ne_zero _ (by norm_num)))
      (Nat.cast_ne_zero.mpr k.factorial_ne_zero))

/-- At block exponent zero, the translated polynomial is the single term
`(X - 1) ^ d`. -/
@[simp] theorem thueMorseTranslatedPowerSumPolynomial_zero (d : ℕ) :
    thueMorseTranslatedPowerSumPolynomial 0 d =
      (Polynomial.X - 1) ^ d := by
  apply Polynomial.funext
  intro q
  rw [thueMorseTranslatedPowerSumPolynomial_eval,
    thueMorseTranslatedPowerSum_zero]
  simp

/-- At the sharp Prouhet degree, the translated polynomial is the nonzero
constant sharp moment. -/
@[simp] theorem thueMorseTranslatedPowerSumPolynomial_self (k : ℕ) :
    thueMorseTranslatedPowerSumPolynomial k k =
      Polynomial.C
        ((-1 : ℚ) ^ k * (2 : ℚ) ^ k.choose 2 * (k.factorial : ℚ)) := by
  apply Polynomial.funext
  intro q
  rw [thueMorseTranslatedPowerSumPolynomial_eval,
    thueMorseTranslatedPowerSum_self]
  simp

/-- The translated polynomial vanishes exactly below the sharp Prouhet
degree. -/
@[simp] theorem thueMorseTranslatedPowerSumPolynomial_eq_zero_iff
    (k d : ℕ) :
    thueMorseTranslatedPowerSumPolynomial k d = 0 ↔ d < k := by
  constructor
  · intro hp
    by_contra hdk
    have hkd : k ≤ d := Nat.le_of_not_gt hdk
    have hcoeff :
        (thueMorseTranslatedPowerSumPolynomial k d).coeff (d - k) = 0 := by
      simpa only [Polynomial.coeff_zero] using
        congrArg (fun p : Polynomial ℚ => p.coeff (d - k)) hp
    exact
      (coeff_thueMorseTranslatedPowerSumPolynomial_natSub_ne_zero k d hkd)
        hcoeff
  · intro hdk
    apply Polynomial.funext
    intro q
    rw [thueMorseTranslatedPowerSumPolynomial_eval,
      thueMorseTranslatedPowerSum_eq_zero_of_lt q k d hdk,
      Polynomial.eval_zero]

/-- Prouhet cancellation lowers the natural degree by exactly `k`.  This
includes the zero-polynomial convention `natDegree 0 = 0` when `d < k`. -/
@[simp] theorem thueMorseTranslatedPowerSumPolynomial_natDegree
    (k d : ℕ) :
    (thueMorseTranslatedPowerSumPolynomial k d).natDegree = d - k := by
  by_cases hdk : d < k
  · rw [(thueMorseTranslatedPowerSumPolynomial_eq_zero_iff k d).2 hdk]
    simp [Nat.sub_eq_zero_of_le hdk.le]
  · have hkd : k ≤ d := Nat.le_of_not_gt hdk
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro j hj
      rw [coeff_thueMorseTranslatedPowerSumPolynomial]
      by_cases hjd : j ≤ d
      · have hlt : d - j < k := by omega
        rw [thueMorseCenteredPowerSum_eq_zero_of_lt k (d - j) hlt,
          mul_zero]
      · have hdj : d < j := Nat.lt_of_not_ge hjd
        simp [Nat.choose_eq_zero_of_lt hdj]
    · exact
        coeff_thueMorseTranslatedPowerSumPolynomial_natSub_ne_zero k d hkd

/-- Exact leading coefficient, including the zero-polynomial branch. -/
@[simp] theorem thueMorseTranslatedPowerSumPolynomial_leadingCoeff
    (k d : ℕ) :
    (thueMorseTranslatedPowerSumPolynomial k d).leadingCoeff =
      if k ≤ d then
        (d.choose k : ℚ) *
          ((-1 : ℚ) ^ k * (2 : ℚ) ^ k.choose 2 * (k.factorial : ℚ))
      else 0 := by
  by_cases hkd : k ≤ d
  · rw [if_pos hkd, ← Polynomial.coeff_natDegree,
      thueMorseTranslatedPowerSumPolynomial_natDegree,
      coeff_thueMorseTranslatedPowerSumPolynomial_natSub k d hkd]
  · have hdk : d < k := Nat.lt_of_not_ge hkd
    rw [if_neg hkd,
      (thueMorseTranslatedPowerSumPolynomial_eq_zero_iff k d).2 hdk]
    simp

/-- Exact degree, retaining the distinction between a nonzero constant and
the zero polynomial. -/
theorem thueMorseTranslatedPowerSumPolynomial_degree
    (k d : ℕ) :
    (thueMorseTranslatedPowerSumPolynomial k d).degree =
      if k ≤ d then ((d - k : ℕ) : WithBot ℕ) else ⊥ := by
  by_cases hkd : k ≤ d
  · rw [if_pos hkd]
    have hp : thueMorseTranslatedPowerSumPolynomial k d ≠ 0 :=
      (not_congr
        (thueMorseTranslatedPowerSumPolynomial_eq_zero_iff k d)).2
          (Nat.not_lt.mpr hkd)
    rw [Polynomial.degree_eq_natDegree hp,
      thueMorseTranslatedPowerSumPolynomial_natDegree]
  · have hdk : d < k := Nat.lt_of_not_ge hkd
    rw [if_neg hkd,
      (thueMorseTranslatedPowerSumPolynomial_eq_zero_iff k d).2 hdk,
      Polynomial.degree_zero]

/-- Rational evaluation of the assembled numerator polynomial recovers the
translated q-binomial numerator. -/
@[simp] theorem qBinomialThueMorseTranslatedNumeratorPolynomial_eval
    (q : ℚ) (n : ℕ) :
    (qBinomialThueMorseTranslatedNumeratorPolynomial n).eval q =
      qBinomialThueMorseTranslatedNumerator q n := by
  rw [qBinomialThueMorseTranslatedNumeratorPolynomial,
    qBinomialThueMorseTranslatedNumerator]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    thueMorseTranslatedPowerSumPolynomial_eval]

/-- Translation invariance as a polynomial identity. -/
theorem qBinomialThueMorseTranslatedNumeratorPolynomial_eq_const (n : ℕ) :
    qBinomialThueMorseTranslatedNumeratorPolynomial n =
      Polynomial.C (qBinomialThueMorseNumerator n) := by
  apply Polynomial.funext
  intro q
  rw [qBinomialThueMorseTranslatedNumeratorPolynomial_eval,
    qBinomialThueMorseTranslatedNumerator_eq_centered,
    Polynomial.eval_C]

/-- Evaluation of the translated numerator in any field over `ℚ`. -/
def qBinomialThueMorseTranslatedNumeratorIn
    {K : Type*} [Field K] [Algebra ℚ K] (q : K) (n : ℕ) : K :=
  Polynomial.eval₂ (algebraMap ℚ K) q
    (qBinomialThueMorseTranslatedNumeratorPolynomial n)

/-- The scalar-valued translated numerator is independent of its translation. -/
theorem qBinomialThueMorseTranslatedNumeratorIn_eq_centered
    {K : Type*} [Field K] [Algebra ℚ K] (q : K) (n : ℕ) :
    qBinomialThueMorseTranslatedNumeratorIn q n =
      algebraMap ℚ K (qBinomialThueMorseNumerator n) := by
  rw [qBinomialThueMorseTranslatedNumeratorIn,
    qBinomialThueMorseTranslatedNumeratorPolynomial_eq_const,
    Polynomial.eval₂_C]

/-- Evaluation at a rational cast agrees with the original rational numerator. -/
theorem qBinomialThueMorseTranslatedNumeratorIn_ratCast
    {K : Type*} [Field K] [Algebra ℚ K] (q : ℚ) (n : ℕ) :
    qBinomialThueMorseTranslatedNumeratorIn (algebraMap ℚ K q) n =
      algebraMap ℚ K (qBinomialThueMorseTranslatedNumerator q n) := by
  rw [qBinomialThueMorseTranslatedNumeratorIn_eq_centered,
    qBinomialThueMorseTranslatedNumerator_eq_centered]

/-- Literal nested-sum expansion of the scalar-valued translated numerator. -/
theorem qBinomialThueMorseTranslatedNumeratorIn_eq_sum
    {K : Type*} [Field K] [Algebra ℚ K] (q : K) (n : ℕ) :
    qBinomialThueMorseTranslatedNumeratorIn q n =
      ∑ k ∈ Finset.range (n + 1),
        algebraMap ℚ K
          (qBinomial n k (1 / 2) /
            ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ))) *
          ∑ r ∈ Finset.range (2 ^ k),
            algebraMap ℚ K (thueMorseSign r : ℚ) *
              (q + algebraMap ℚ K ((r : ℚ) - (2 : ℚ) ^ k)) ^ (n + k) := by
  rw [qBinomialThueMorseTranslatedNumeratorIn,
    qBinomialThueMorseTranslatedNumeratorPolynomial]
  simp only [thueMorseTranslatedPowerSumPolynomial,
    Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_X]

/-- Wolfram-style expansion, with sign `(-1)^ThueMorse[r]` and translated
power `(r - 2^k + q)^(n+k)`. -/
theorem qBinomialThueMorseTranslatedNumeratorIn_eq_wolfram_sum
    {K : Type*} [Field K] [Algebra ℚ K] (q : K) (n : ℕ) :
    qBinomialThueMorseTranslatedNumeratorIn q n =
      ∑ k ∈ Finset.range (n + 1),
        algebraMap ℚ K
          (qBinomial n k (1 / 2) /
            ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ))) *
          ∑ r ∈ Finset.range (2 ^ k),
            (-1 : K) ^ thueMorseBit r *
              ((r : K) - (2 : K) ^ k + q) ^ (n + k) := by
  rw [qBinomialThueMorseTranslatedNumeratorIn_eq_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  congr 1
  apply Finset.sum_congr rfl
  intro r _hr
  rw [← neg_one_pow_thueMorseBit]
  simp only [map_pow, map_neg, map_one, map_sub, map_natCast, map_ofNat]
  congr 1
  ring

/-- The rational q-binomial numerator has the Taylor-coefficient normalization. -/
theorem qBinomialThueMorseTranslatedNumerator_div_eq_halfMoment
    (q : ℚ) (n : ℕ) :
    qBinomialThueMorseTranslatedNumerator q n /
        ((2 : ℚ) ^ n.choose 2 * qPochhammer (1 / 2) (1 / 2) n) =
      (2 : ℚ) ^ n * halfMoment n / (n.factorial : ℚ) := by
  have h := (qBinomialThueMorseTranslatedFormula_eq_centered q n).trans
    (qBinomialThueMorseFormula_eq_recurrenceSequence n)
  rw [qBinomialThueMorseTranslatedFormula, fabiusRecurrenceSequence,
    qPochhammer_half_eq] at h
  rw [qPochhammer_half_eq]
  have hp : halfQPochhammer n ≠ 0 := halfQPochhammer_ne_zero n
  have hpow : n ^ 2 = n.choose 2 + (n.choose 2 + n) := by
    have hs := two_mul_choose_two_add n
    omega
  rw [hpow, pow_add, pow_add] at h
  field_simp at h ⊢
  linear_combination h

/-- Equivalent normalization in terms of the exact inverse-dyadic value. -/
theorem qBinomialThueMorseTranslatedNumerator_div_eq_fabiusAtInverseTwoPow
    (q : ℚ) (n : ℕ) :
    qBinomialThueMorseTranslatedNumerator q n /
        ((2 : ℚ) ^ n.choose 2 * qPochhammer (1 / 2) (1 / 2) n) =
      (2 : ℚ) ^ (n + 1).choose 2 * fabiusAtInverseTwoPow n := by
  rw [qBinomialThueMorseTranslatedNumerator_div_eq_halfMoment,
    fabiusAtInverseTwoPow_eq_halfMoment, halfMomentFabiusValue]
  have hchoose : (n + 1).choose 2 = n.choose 2 + n := by
    rw [show n + 1 = n + 1 by rfl, show 2 = 1 + 1 by omega,
      Nat.choose_succ_succ]
    simp [Nat.choose_one_right, Nat.add_comm]
  rw [hchoose, pow_add]
  field_simp

/-- The normalization after evaluation in an arbitrary field over `ℚ`. -/
theorem qBinomialThueMorseTranslatedNumeratorIn_div_eq_halfMoment
    {K : Type*} [Field K] [Algebra ℚ K] (q : K) (n : ℕ) :
    qBinomialThueMorseTranslatedNumeratorIn q n /
        algebraMap ℚ K
          ((2 : ℚ) ^ n.choose 2 * qPochhammer (1 / 2) (1 / 2) n) =
      algebraMap ℚ K
        ((2 : ℚ) ^ n * halfMoment n / (n.factorial : ℚ)) := by
  rw [qBinomialThueMorseTranslatedNumeratorIn_eq_centered]
  have h := congrArg (algebraMap ℚ K)
    (qBinomialThueMorseTranslatedNumerator_div_eq_halfMoment 0 n)
  rw [qBinomialThueMorseTranslatedNumerator_eq_centered] at h
  rw [← map_div₀ (algebraMap ℚ K)]
  exact h

/-- The generic normalization in terms of the exact inverse-dyadic value. -/
theorem qBinomialThueMorseTranslatedNumeratorIn_div_eq_fabiusAtInverseTwoPow
    {K : Type*} [Field K] [Algebra ℚ K] (q : K) (n : ℕ) :
    qBinomialThueMorseTranslatedNumeratorIn q n /
        algebraMap ℚ K
          ((2 : ℚ) ^ n.choose 2 * qPochhammer (1 / 2) (1 / 2) n) =
      algebraMap ℚ K
        ((2 : ℚ) ^ (n + 1).choose 2 * fabiusAtInverseTwoPow n) := by
  rw [qBinomialThueMorseTranslatedNumeratorIn_div_eq_halfMoment]
  apply congrArg (algebraMap ℚ K)
  exact
    (qBinomialThueMorseTranslatedNumerator_div_eq_halfMoment 0 n).symm.trans
      (qBinomialThueMorseTranslatedNumerator_div_eq_fabiusAtInverseTwoPow 0 n)

private theorem taylor_choose_identity {m k : ℕ} (hk : k ≤ m) :
    (m + 1) * k + (m - k) + (m - k).choose 2 =
      (k + 1).choose 2 + (m + 1).choose 2 := by
  have hsub : m - k + k = m := Nat.sub_add_cancel hk
  have hkchoose := two_mul_choose_succ_two k
  have hmchoose := two_mul_choose_succ_two m
  have hdchoose := two_mul_choose_two_add (m - k)
  nlinarith

/-- The q-binomial finite polynomial replacing the Taylor reduction sum. -/
def qBinomialFabiusReductionPolynomial
    {K : Type*} [Field K] [Algebra ℚ K]
    (q : K) (m : ℕ) (y : K) : K :=
  (∑ n ∈ Finset.range (m + 1),
      (((2 : K) ^ (m + 1) * y) ^ (m - n) /
          ((m - n).factorial : K)) *
        (qBinomialThueMorseTranslatedNumeratorIn q n /
          algebraMap ℚ K
            ((2 : ℚ) ^ n.choose 2 * qPochhammer (1 / 2) (1 / 2) n))) /
    (2 : K) ^ (m + 1).choose 2

/-- Literal nested-sum expansion of the fully scaled finite polynomial. -/
theorem qBinomialFabiusReductionPolynomial_eq_sum
    {K : Type*} [Field K] [Algebra ℚ K]
    (q : K) (m : ℕ) (y : K) :
    qBinomialFabiusReductionPolynomial q m y =
      (∑ n ∈ Finset.range (m + 1),
          (((2 : K) ^ (m + 1) * y) ^ (m - n) /
              ((m - n).factorial : K)) *
            ((∑ k ∈ Finset.range (n + 1),
                algebraMap ℚ K
                  (qBinomial n k (1 / 2) /
                    ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ))) *
                  ∑ r ∈ Finset.range (2 ^ k),
                    (-1 : K) ^ thueMorseBit r *
                      ((r : K) - (2 : K) ^ k + q) ^ (n + k)) /
              algebraMap ℚ K
                ((2 : ℚ) ^ n.choose 2 *
                  qPochhammer (1 / 2) (1 / 2) n))) /
        (2 : K) ^ (m + 1).choose 2 := by
  rw [qBinomialFabiusReductionPolynomial]
  simp_rw [qBinomialThueMorseTranslatedNumeratorIn_eq_wolfram_sum]

/-- The Taylor reduction polynomial over an arbitrary field over `ℚ`. -/
def fabiusReductionSumIn
    {K : Type*} [Field K] [Algebra ℚ K] (m : ℕ) (y : K) : K :=
  ∑ k ∈ Finset.range (m + 1),
    (2 : K) ^ ((Nat.choose (k + 1) 2 : ℤ) - Nat.choose (m - k) 2) *
      algebraMap ℚ K (halfMoment (m - k)) /
        ((m - k).factorial : K) * y ^ k / (k.factorial : K)

/-- The fully scaled finite q-binomial sum is the Taylor reduction polynomial. -/
theorem qBinomialFabiusReductionPolynomial_eq_reductionSumIn
    {K : Type*} [Field K] [Algebra ℚ K]
    (q : K) (m : ℕ) (y : K) :
    qBinomialFabiusReductionPolynomial q m y =
      fabiusReductionSumIn m y := by
  haveI : CharZero K := algebraRat.charZero K
  have hbridge (n : ℕ) :
      qBinomialThueMorseTranslatedNumeratorIn q n /
          algebraMap ℚ K
            ((2 : ℚ) ^ n.choose 2 * qPochhammer (1 / 2) (1 / 2) n) =
        (2 : K) ^ n * algebraMap ℚ K (halfMoment n) /
          (n.factorial : K) := by
    rw [qBinomialThueMorseTranslatedNumeratorIn_div_eq_halfMoment]
    rw [map_div₀ (algebraMap ℚ K), map_mul, map_pow]
    norm_num
  rw [qBinomialFabiusReductionPolynomial]
  simp_rw [hbridge]
  rw [Finset.sum_div]
  rw [← Finset.sum_range_reflect
    (fun n =>
      ((((2 : K) ^ (m + 1) * y) ^ (m - n) /
          ((m - n).factorial : K)) *
        ((2 : K) ^ n * algebraMap ℚ K (halfMoment n) /
          (n.factorial : K))) /
        (2 : K) ^ (m + 1).choose 2) (m + 1)]
  rw [fabiusReductionSumIn]
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : k ≤ m := by simpa using Finset.mem_range.mp hk
  have hsub : m - (m + 1 - 1 - k) = k := by omega
  have hindex : m + 1 - 1 - k = m - k := by omega
  rw [hsub, hindex, mul_pow]
  rw [zpow_sub₀ (by norm_num : (2 : K) ≠ 0),
    zpow_natCast, zpow_natCast]
  have hexp := taylor_choose_identity hkm
  have htwo :
      ((2 : K) ^ (m + 1)) ^ k * (2 : K) ^ (m - k) *
          (2 : K) ^ (m - k).choose 2 =
        (2 : K) ^ (m + 1).choose 2 * (2 : K) ^ (k + 1).choose 2 := by
    rw [← pow_mul, ← pow_add, ← pow_add, hexp, pow_add]
    ring
  field_simp [Nat.cast_ne_zero]
  congr 1
  calc
    ((2 : K) ^ (m + 1)) ^ k * y ^ k * (2 : K) ^ (m - k) *
          algebraMap ℚ K (halfMoment (m - k)) * (2 : K) ^ (m - k).choose 2 =
        y ^ k * algebraMap ℚ K (halfMoment (m - k)) *
          (((2 : K) ^ (m + 1)) ^ k * (2 : K) ^ (m - k) *
            (2 : K) ^ (m - k).choose 2) := by ring
    _ = y ^ k * algebraMap ℚ K (halfMoment (m - k)) *
          ((2 : K) ^ (m + 1).choose 2 * (2 : K) ^ (k + 1).choose 2) := by
      rw [htwo]
    _ = y ^ k * algebraMap ℚ K (halfMoment (m - k)) *
          (2 : K) ^ (m + 1).choose 2 * (2 : K) ^ (k + 1).choose 2 := by ring

/-- In degree zero the scaled q-binomial reduction is the constant one,
independently of its translation and evaluation point. -/
@[simp] theorem qBinomialFabiusReductionPolynomial_zero
    {K : Type*} [Field K] [Algebra ℚ K] (q y : K) :
    qBinomialFabiusReductionPolynomial q 0 y = 1 := by
  rw [qBinomialFabiusReductionPolynomial_eq_reductionSumIn]
  simp [fabiusReductionSumIn]

/-- Over the reals, the scalar-generic Taylor reduction is the original
real-valued reduction sum. -/
theorem fabiusReductionSumIn_real (m : ℕ) (y : ℝ) :
    fabiusReductionSumIn m y = fabiusReductionSum m y := by
  rw [fabiusReductionSumIn, fabiusReductionSum]
  apply Finset.sum_congr rfl
  intro k _hk
  norm_num

/-- The real q-binomial reduction polynomial is the original Taylor reduction
sum, independently of its common translation. -/
theorem qBinomialFabiusReductionPolynomial_eq_fabiusReductionSum
    (q : ℝ) (m : ℕ) (y : ℝ) :
    qBinomialFabiusReductionPolynomial q m y = fabiusReductionSum m y := by
  rw [qBinomialFabiusReductionPolynomial_eq_reductionSumIn,
    fabiusReductionSumIn_real]

/-- Rational translations, cast to `ℝ`, give the same reduction polynomial. -/
theorem qBinomialFabiusReductionPolynomial_ratCast_eq_fabiusReductionSum
    (q : ℚ) (m : ℕ) (y : ℝ) :
    qBinomialFabiusReductionPolynomial (q : ℝ) m y =
      fabiusReductionSum m y :=
  qBinomialFabiusReductionPolynomial_eq_fabiusReductionSum (q : ℝ) m y

/-- The rational translated numerators, coefficientwise cast to `ℝ`, give
the Taylor reduction sum. -/
theorem qBinomialThueMorseTranslatedTaylorSum_eq_fabiusReductionSum
    (q : ℚ) (m : ℕ) (y : ℝ) :
    (∑ n ∈ Finset.range (m + 1),
        (((2 : ℝ) ^ (m + 1) * y) ^ (m - n) /
            ((m - n).factorial : ℝ)) *
          ((qBinomialThueMorseTranslatedNumerator q n : ℝ) /
            (((2 : ℚ) ^ n.choose 2 *
              qPochhammer (1 / 2) (1 / 2) n : ℚ) : ℝ))) /
      (2 : ℝ) ^ (m + 1).choose 2 =
        fabiusReductionSum m y := by
  rw [← qBinomialFabiusReductionPolynomial_ratCast_eq_fabiusReductionSum q m y]
  rw [qBinomialFabiusReductionPolynomial]
  apply congrArg (fun z : ℝ => z / (2 : ℝ) ^ (m + 1).choose 2)
  apply Finset.sum_congr rfl
  intro n _hn
  rw [qBinomialThueMorseTranslatedNumeratorIn_eq_centered,
    qBinomialThueMorseTranslatedNumerator_eq_centered]
  rfl

/-- Scalar-generic compatibility with the real Taylor reduction sum. -/
theorem fabiusReductionSumIn_rclike
    {K : Type*} [RCLike K] (m : ℕ) (y : ℝ) :
    fabiusReductionSumIn m (y : K) = (fabiusReductionSum m y : K) := by
  rw [fabiusReductionSumIn, fabiusReductionSum]
  push_cast
  rfl

/-- The q-binomial reduction identity simultaneously over `ℝ` and `ℂ`. -/
theorem qBinomialFabiusReductionPolynomial_rclike_eq_fabiusReductionSum
    {K : Type*} [RCLike K] (q : K) (m : ℕ) (y : ℝ) :
    qBinomialFabiusReductionPolynomial q m (y : K) =
      (fabiusReductionSum m y : K) := by
  rw [qBinomialFabiusReductionPolynomial_eq_reductionSumIn,
    fabiusReductionSumIn_rclike]

/-- The complex scalar reduction at a real argument is the cast of the real
Taylor reduction sum. -/
theorem fabiusReductionSumIn_complex_ofReal (m : ℕ) (y : ℝ) :
    fabiusReductionSumIn m (y : ℂ) = (fabiusReductionSum m y : ℂ) := by
  exact fabiusReductionSumIn_rclike m y

/-- The complex q-binomial reduction at a real argument is the cast of the
real Taylor reduction sum. -/
theorem qBinomialFabiusReductionPolynomial_complex_eq_fabiusReductionSum
    (q : ℂ) (m : ℕ) (y : ℝ) :
    qBinomialFabiusReductionPolynomial q m (y : ℂ) =
      (fabiusReductionSum m y : ℂ) := by
  exact qBinomialFabiusReductionPolynomial_rclike_eq_fabiusReductionSum q m y

end

end Fabius
