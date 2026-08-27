import FabiusFunction.MomentCumulantAlgebra
import FabiusFunction.MomentPowerSeries
import FabiusFunction.SaddleLogProductAlgebra
import Mathlib.NumberTheory.Bernoulli

/-!
# Centered Rvachev moments and formal cumulants

The ordinary exponential-generating-function transform now lives in
`MomentCumulantAlgebra`: `factorialNormalize`, `momentCumulant`, and
`completeBellPolynomial` provide the general Bell/moment/cumulant API.  This
module develops the genuinely different compressed-even normalization
`m_n / (2n)!`, then applies it to the executable centered Rvachev moments.

The formal moment equation

`momentPS(4X) = momentPS(X) * sinhDivPS(X)`

and the generic product algebra in `SaddleLogProductAlgebra` give the exact
coefficient identity

`(4^n - 1) L_n = [X^n] log(sinh(√X)/√X)`.

The final section records the Bernoulli--Mersenne coefficient predicted by the
spectral report and proves that its identification with the one-scale
hyperbolic-sine logarithm implies the report's alternative moment recurrence.
This is a conditional bridge with a sharply stated algebraic premise, not an
analytic or probabilistic shortcut: the remaining all-order obligation is

`logCoeff (fun n => 1 / (2*n+1)!) n
  = 2^(2*n-1) * B_(2*n) / (n * (2*n)!)`

at positive indices.  The first two coefficients are proved unconditionally,
fixing the normalization and signs independently of that frontier identity.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset PowerSeries

namespace Fabius

/-! ## Factorially normalized compressed-even moments -/

namespace EvenMomentCumulant

noncomputable section

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The coefficient of `X^n` in the compressed-even exponential generating
series `∑ n, μ_n X^n / (2n)!`. -/
def evenFactorialNormalize (μ : ℕ → R) (n : ℕ) : R :=
  (((2 * n).factorial : ℚ)⁻¹) • μ n

/-- The compressed-even cumulant indexed by half its ordinary order.  Thus
index `r` represents the ordinary cumulant of order `2r`. -/
def evenMomentCumulant (μ : ℕ → R) (r : ℕ) : R :=
  ((2 * r).factorial : ℚ) •
    SaddleExpansion.logCoeff (evenFactorialNormalize μ) r

/-- The ordinary moment sequence whose factorial normalization is the
compressed-even coefficient family.  It connects the `(2n)!` convention here
to the canonical Bell/moment/cumulant API. -/
def compressedEvenMomentSequence (μ : ℕ → R) : ℕ → R :=
  factorialDenormalize (evenFactorialNormalize μ)

/-- The canonical factorial normalization of `compressedEvenMomentSequence`
is exactly the compressed-even normalization. -/
@[simp] theorem factorialNormalize_compressedEvenMomentSequence (μ : ℕ → R) :
    factorialNormalize (compressedEvenMomentSequence μ) =
      evenFactorialNormalize μ := by
  exact factorialNormalize_factorialDenormalize _

/-- Canonical cumulants of `compressedEvenMomentSequence` are the `n!`-scaled
logarithmic coefficients of the compressed-even series. -/
theorem momentCumulant_compressedEvenMomentSequence (μ : ℕ → R) :
    momentCumulant (compressedEvenMomentSequence μ) =
      factorialDenormalize
        (SaddleExpansion.logCoeff (evenFactorialNormalize μ)) := by
  exact momentCumulant_factorialDenormalize _

/-- Cross-multiplied comparison between the canonical `n!` cumulant and the
ordinary-order `(2n)!` cumulant.  This form avoids division and remains valid
in rational algebras with zero divisors. -/
theorem factorial_smul_evenMomentCumulant_eq_evenFactorial_smul_momentCumulant
    (μ : ℕ → R) (n : ℕ) :
    (n.factorial : ℚ) • evenMomentCumulant μ n =
      ((2 * n).factorial : ℚ) •
        momentCumulant (compressedEvenMomentSequence μ) n := by
  rw [evenMomentCumulant,
    congrFun (momentCumulant_compressedEvenMomentSequence μ) n,
    factorialDenormalize]
  simp only [smul_smul]
  congr 1
  ring

/-- Compressed-even normalization does not change the zeroth coefficient. -/
@[simp] theorem evenFactorialNormalize_zero (μ : ℕ → R) :
    evenFactorialNormalize μ 0 = μ 0 := by
  simp [evenFactorialNormalize]

/-- The zeroth compressed-even cumulant is zero. -/
@[simp] theorem evenMomentCumulant_zero (μ : ℕ → R) :
    evenMomentCumulant μ 0 = 0 := by
  simp [evenMomentCumulant]

/-- Multiplying a compressed-even normalized coefficient by `(2n)!` recovers
the original coefficient. -/
theorem evenFactorialDenormalize_normalize (μ : ℕ → R) (n : ℕ) :
    ((2 * n).factorial : ℚ) • evenFactorialNormalize μ n = μ n := by
  have hfac : ((2 * n).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n)
  rw [evenFactorialNormalize, ← mul_smul,
    mul_inv_cancel₀ hfac, one_smul]

/-- The compressed-even moment--cumulant recurrence in successor form.  The
factor `(j+1)/(n+1)` comes from differentiating with respect to `X=t²`, while
the binomial coefficient restores the ordinary `(2n)!` normalization. -/
theorem evenMomentCumulant_succ_recurrence
    (μ : ℕ → R) (hμ0 : μ 0 = 1) (n : ℕ) :
    μ (n + 1) = ((n + 1 : ℚ)⁻¹) •
      (∑ j ∈ range (n + 1),
        (j + 1 : R) * (Nat.choose (2 * (n + 1)) (2 * (j + 1)) : R) *
          evenMomentCumulant μ (j + 1) * μ (n - j)) := by
  have hraw := SaddleExpansion.coefficient_succ_eq_logCoeff_sum
    (a := evenFactorialNormalize μ)
    (by simpa using hμ0) n
  have hterm (j : ℕ) (hj : j ∈ range (n + 1)) :
      ((2 * (n + 1)).factorial : ℚ) •
          ((j + 1 : R) *
            SaddleExpansion.logCoeff (evenFactorialNormalize μ) (j + 1) *
            evenFactorialNormalize μ (n - j)) =
        (j + 1 : R) *
          (Nat.choose (2 * (n + 1)) (2 * (j + 1)) : R) *
          evenMomentCumulant μ (j + 1) * μ (n - j) := by
    have hjle : 2 * (j + 1) ≤ 2 * (n + 1) := by
      have := mem_range.1 hj
      omega
    have hsub : 2 * (n + 1) - 2 * (j + 1) = 2 * (n - j) := by
      have := mem_range.1 hj
      omega
    let qleft : ℚ :=
      ((2 * (n + 1)).factorial : ℚ) * (j + 1 : ℚ) *
        (((2 * (n - j)).factorial : ℚ)⁻¹)
    let qright : ℚ :=
      (j + 1 : ℚ) *
        (Nat.choose (2 * (n + 1)) (2 * (j + 1)) : ℚ) *
        ((2 * (j + 1)).factorial : ℚ)
    have hq : qleft = qright := by
      dsimp [qleft, qright]
      rw [Nat.cast_choose ℚ hjle, hsub]
      field_simp <;> ring
    calc
      ((2 * (n + 1)).factorial : ℚ) •
            ((j + 1 : R) *
              SaddleExpansion.logCoeff (evenFactorialNormalize μ) (j + 1) *
              evenFactorialNormalize μ (n - j)) =
          algebraMap ℚ R qleft *
            (SaddleExpansion.logCoeff (evenFactorialNormalize μ) (j + 1) *
              μ (n - j)) := by
        simp [qleft, evenFactorialNormalize, Algebra.smul_def]
        ring
      _ = algebraMap ℚ R qright *
            (SaddleExpansion.logCoeff (evenFactorialNormalize μ) (j + 1) *
              μ (n - j)) := by rw [hq]
      _ = (j + 1 : R) *
            (Nat.choose (2 * (n + 1)) (2 * (j + 1)) : R) *
            evenMomentCumulant μ (j + 1) * μ (n - j) := by
        simp [qright, evenMomentCumulant, Algebra.smul_def]
        ring
  have hsum :
      ((2 * (n + 1)).factorial : ℚ) •
          (∑ j ∈ range (n + 1),
            (j + 1 : R) *
              SaddleExpansion.logCoeff (evenFactorialNormalize μ) (j + 1) *
              evenFactorialNormalize μ (n - j)) =
        ∑ j ∈ range (n + 1),
          (j + 1 : R) *
            (Nat.choose (2 * (n + 1)) (2 * (j + 1)) : R) *
            evenMomentCumulant μ (j + 1) * μ (n - j) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact hterm j hj
  calc
    μ (n + 1) = ((2 * (n + 1)).factorial : ℚ) •
        evenFactorialNormalize μ (n + 1) :=
      (evenFactorialDenormalize_normalize μ (n + 1)).symm
    _ = ((2 * (n + 1)).factorial : ℚ) •
        (((n + 1 : ℚ)⁻¹) •
          ∑ j ∈ range (n + 1),
            (j + 1 : R) *
              SaddleExpansion.logCoeff (evenFactorialNormalize μ) (j + 1) *
              evenFactorialNormalize μ (n - j)) := by rw [hraw]
    _ = ((n + 1 : ℚ)⁻¹) •
        (((2 * (n + 1)).factorial : ℚ) •
          ∑ j ∈ range (n + 1),
            (j + 1 : R) *
              SaddleExpansion.logCoeff (evenFactorialNormalize μ) (j + 1) *
              evenFactorialNormalize μ (n - j)) := by
      simp only [smul_smul]
      congr 1
      ring
    _ = ((n + 1 : ℚ)⁻¹) •
        (∑ j ∈ range (n + 1),
          (j + 1 : R) * (Nat.choose (2 * (n + 1)) (2 * (j + 1)) : R) *
            evenMomentCumulant μ (j + 1) * μ (n - j)) := by rw [hsum]

/-- The compressed-even recurrence indexed by the half-order `r`:
`mu_N = N⁻¹ • ∑ r in [1,N], r * choose(2N,2r) * kappa_(2r) * mu_(N-r)`. -/
theorem evenMomentCumulant_recurrence
    (μ : ℕ → R) (hμ0 : μ 0 = 1)
    (N : ℕ) (hN : 1 ≤ N) :
    μ N = ((N : ℚ)⁻¹) •
      (∑ r ∈ Icc 1 N,
        (r : R) * (Nat.choose (2 * N) (2 * r) : R) *
          evenMomentCumulant μ r * μ (N - r)) := by
  obtain ⟨n, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simpa [add_comm] using evenMomentCumulant_succ_recurrence μ hμ0 n

end

end EvenMomentCumulant

/-! ## The centered Rvachev moment series -/

noncomputable section

/-- The factorially normalized centered Rvachev moment coefficient
`c_n/(2n)!`, where `c_n = moment n`. -/
def centeredRvachevMomentCoefficient (n : ℕ) : ℚ :=
  EvenMomentCumulant.evenFactorialNormalize moment n

/-- The compressed logarithmic coefficient of the centered Rvachev moment
series. -/
def centeredRvachevLogCoefficient (n : ℕ) : ℚ :=
  SaddleExpansion.logCoeff centeredRvachevMomentCoefficient n

/-- The centered Rvachev cumulant of ordinary order `2n`, indexed by `n`. -/
def centeredRvachevEvenCumulant (n : ℕ) : ℚ :=
  EvenMomentCumulant.evenMomentCumulant moment n

/-- The one-scale coefficient `1/(2n+1)!` of `sinh(√X)/√X`. -/
def sinhDivCoefficient (n : ℕ) : ℚ :=
  1 / ((2 * n + 1).factorial : ℚ)

/-- The formal logarithmic coefficient of `sinh(√X)/√X`. -/
def sinhDivLogCoefficient (n : ℕ) : ℚ :=
  SaddleExpansion.logCoeff sinhDivCoefficient n

/-- A positive power of four is not one in `ℚ`. -/
theorem rat_four_pow_sub_one_ne_zero (n : ℕ) (hn : 1 ≤ n) :
    (4 : ℚ) ^ n - 1 ≠ 0 := by
  exact ne_of_gt (sub_pos.mpr
    (one_lt_pow₀ (a := (4 : ℚ)) (by norm_num) (by omega)))

/-- The centered Rvachev coefficient family has unit constant term. -/
@[simp] theorem centeredRvachevMomentCoefficient_zero :
    centeredRvachevMomentCoefficient 0 = 1 := by
  simp [centeredRvachevMomentCoefficient, moment]

/-- The centered Rvachev logarithm has zero constant coefficient. -/
@[simp] theorem centeredRvachevLogCoefficient_zero :
    centeredRvachevLogCoefficient 0 = 0 := by
  simp [centeredRvachevLogCoefficient]

/-- The zeroth centered Rvachev cumulant is zero. -/
@[simp] theorem centeredRvachevEvenCumulant_zero :
    centeredRvachevEvenCumulant 0 = 0 := by
  simp [centeredRvachevEvenCumulant]

/-- The one-scale hyperbolic-sine coefficient family has unit constant term. -/
@[simp] theorem sinhDivCoefficient_zero : sinhDivCoefficient 0 = 1 := by
  norm_num [sinhDivCoefficient]

/-- The one-scale logarithm has zero constant coefficient. -/
@[simp] theorem sinhDivLogCoefficient_zero : sinhDivLogCoefficient 0 = 0 := by
  simp [sinhDivLogCoefficient]

/-- `centeredRvachevMomentCoefficient` is exactly the coefficient family
packaged by `momentPS`. -/
@[simp] theorem coeff_momentPS_eq_centeredRvachevMomentCoefficient (n : ℕ) :
    PowerSeries.coeff n momentPS = centeredRvachevMomentCoefficient n := by
  simp [momentPS, centeredRvachevMomentCoefficient,
    EvenMomentCumulant.evenFactorialNormalize, Algebra.smul_def,
    div_eq_mul_inv, mul_comm]

/-- `sinhDivCoefficient` is exactly the coefficient family packaged by
`sinhDivPS`. -/
@[simp] theorem coeff_sinhDivPS_eq_sinhDivCoefficient (n : ℕ) :
    PowerSeries.coeff n sinhDivPS = sinhDivCoefficient n := by
  simp [sinhDivPS, sinhDivCoefficient]

/-- Coefficientwise form of the formal moment equation
`momentPS(4X) = momentPS(X) sinh(√X)/√X`. -/
theorem centeredRvachevMomentCoefficient_functional (n : ℕ) :
    (4 : ℚ) ^ n * centeredRvachevMomentCoefficient n =
      SaddleExpansion.coefficientConvolution centeredRvachevMomentCoefficient
        sinhDivCoefficient n := by
  have h := congrArg (PowerSeries.coeff n) momentPS_functional
  simpa only [PowerSeries.coeff_rescale, PowerSeries.coeff_mul,
    coeff_momentPS_eq_centeredRvachevMomentCoefficient,
    coeff_sinhDivPS_eq_sinhDivCoefficient,
    SaddleExpansion.coefficientConvolution] using h

/-- Exact logarithmic form of the centered moment functional equation:
`(4^n-1) L_n` is the `n`th coefficient of
`log(sinh(√X)/√X)`. -/
theorem centeredRvachevLogCoefficient_scale (n : ℕ) :
    ((4 : ℚ) ^ n - 1) * centeredRvachevLogCoefficient n =
      sinhDivLogCoefficient n := by
  exact SaddleExpansion.logCoeff_geometric_product
    (q := (4 : ℚ)) centeredRvachevMomentCoefficient sinhDivCoefficient
    centeredRvachevMomentCoefficient_zero sinhDivCoefficient_zero
    centeredRvachevMomentCoefficient_functional n

/-- At positive order the centered logarithmic coefficient is the one-scale
coefficient divided by the Mersenne-square factor `4^n-1`. -/
theorem centeredRvachevLogCoefficient_eq_sinhDiv (n : ℕ) (hn : 1 ≤ n) :
    centeredRvachevLogCoefficient n =
      sinhDivLogCoefficient n / ((4 : ℚ) ^ n - 1) := by
  apply (eq_div_iff (rat_four_pow_sub_one_ne_zero n hn)).2
  simpa [mul_comm] using centeredRvachevLogCoefficient_scale n

/-- The centered cumulant of order `2n` is the factorially denormalized
one-scale logarithmic coefficient divided by `4^n-1`. -/
theorem centeredRvachevEvenCumulant_eq_sinhDiv (n : ℕ) (hn : 1 ≤ n) :
    centeredRvachevEvenCumulant n =
      ((2 * n).factorial : ℚ) * sinhDivLogCoefficient n /
        ((4 : ℚ) ^ n - 1) := by
  rw [centeredRvachevEvenCumulant, EvenMomentCumulant.evenMomentCumulant,
    show SaddleExpansion.logCoeff
        (EvenMomentCumulant.evenFactorialNormalize moment) n =
      centeredRvachevLogCoefficient n by rfl,
    centeredRvachevLogCoefficient_eq_sinhDiv n hn]
  simp only [Algebra.smul_def]
  ring

/-- Exponentiating the centered Rvachev logarithmic coefficients reconstructs
the factorially normalized centered moment sequence. -/
theorem expCoeff_centeredRvachevLogCoefficient (n : ℕ) :
    SaddleExpansion.expCoeff centeredRvachevLogCoefficient n =
      centeredRvachevMomentCoefficient n := by
  exact SaddleExpansion.expCoeff_logCoeff centeredRvachevMomentCoefficient
    centeredRvachevMomentCoefficient_zero n

/-- Unconditional moment--cumulant recurrence for the executable centered
Rvachev moments.  The cumulant indexed by `r` has ordinary order `2r`. -/
theorem moment_centeredRvachevEvenCumulant_recurrence
    (N : ℕ) (hN : 1 ≤ N) :
    moment N =
      (∑ r ∈ Icc 1 N,
        (r : ℚ) * (Nat.choose (2 * N) (2 * r) : ℚ) *
          centeredRvachevEvenCumulant r * moment (N - r)) / (N : ℚ) := by
  simpa [centeredRvachevEvenCumulant, Algebra.smul_def,
    div_eq_mul_inv, mul_comm] using
    (EvenMomentCumulant.evenMomentCumulant_recurrence
      (R := ℚ) moment moment_zero N hN)

/-- The first one-scale logarithmic coefficient is `1/6`. -/
theorem sinhDivLogCoefficient_one : sinhDivLogCoefficient 1 = 1 / 6 := by
  rw [sinhDivLogCoefficient, SaddleExpansion.logCoeff_one]
  norm_num [sinhDivCoefficient]

/-- The second one-scale logarithmic coefficient is `-1/180`. -/
theorem sinhDivLogCoefficient_two : sinhDivLogCoefficient 2 = -1 / 180 := by
  rw [sinhDivLogCoefficient, SaddleExpansion.logCoeff_two]
  norm_num [sinhDivCoefficient]

/-- The variance cumulant of the centered Rvachev law is `1/9`. -/
theorem centeredRvachevEvenCumulant_one :
    centeredRvachevEvenCumulant 1 = 1 / 9 := by
  rw [centeredRvachevEvenCumulant_eq_sinhDiv 1 (by omega),
    sinhDivLogCoefficient_one]
  norm_num

/-- The fourth centered Rvachev cumulant is `-2/225`. -/
theorem centeredRvachevEvenCumulant_two :
    centeredRvachevEvenCumulant 2 = -2 / 225 := by
  rw [centeredRvachevEvenCumulant_eq_sinhDiv 2 (by omega),
    sinhDivLogCoefficient_two]
  norm_num

/-! ## The Bernoulli--Mersenne frontier bridge -/

/-- The Bernoulli formula predicted for the coefficient of
`log(sinh(√X)/√X)`.  The value at zero is fixed separately because the
positive-index closed form contains both `n` and `2*n-1`. -/
def bernoulliSinhDivLogCoefficient (n : ℕ) : ℚ :=
  if n = 0 then 0 else
    (2 : ℚ) ^ (2 * n - 1) * bernoulli (2 * n) /
      ((n : ℚ) * ((2 * n).factorial : ℚ))

/-- The Bernoulli--Mersenne candidate for the centered cumulant of order
`2n`. -/
def bernoulliMersenneEvenCumulant (n : ℕ) : ℚ :=
  if n = 0 then 0 else
    (2 : ℚ) ^ (2 * n - 1) * bernoulli (2 * n) /
      ((n : ℚ) * ((4 : ℚ) ^ n - 1))

/-- The Bernoulli one-scale candidate vanishes at index zero. -/
@[simp] theorem bernoulliSinhDivLogCoefficient_zero :
    bernoulliSinhDivLogCoefficient 0 = 0 := by
  simp [bernoulliSinhDivLogCoefficient]

/-- The Bernoulli--Mersenne cumulant candidate vanishes at index zero. -/
@[simp] theorem bernoulliMersenneEvenCumulant_zero :
    bernoulliMersenneEvenCumulant 0 = 0 := by
  simp [bernoulliMersenneEvenCumulant]

/-- The Bernoulli one-scale formula has the correct first coefficient. -/
theorem bernoulliSinhDivLogCoefficient_one :
    bernoulliSinhDivLogCoefficient 1 = 1 / 6 := by
  rw [bernoulliSinhDivLogCoefficient, if_neg (by omega), bernoulli_two]
  norm_num

/-- The Bernoulli one-scale formula has the correct second coefficient. -/
theorem bernoulliSinhDivLogCoefficient_two :
    bernoulliSinhDivLogCoefficient 2 = -1 / 180 := by
  rw [bernoulliSinhDivLogCoefficient, if_neg (by omega),
    bernoulli_eq_bernoulli'_of_ne_one (by omega), bernoulli'_four]
  norm_num

/-- Identifying one positive one-scale logarithmic coefficient with its
Bernoulli formula identifies the corresponding centered cumulant with the
Bernoulli--Mersenne expression. -/
theorem centeredRvachevEvenCumulant_eq_bernoulliMersenne_of_sinhDiv
    (n : ℕ) (hn : 1 ≤ n)
    (hlog : sinhDivLogCoefficient n = bernoulliSinhDivLogCoefficient n) :
    centeredRvachevEvenCumulant n = bernoulliMersenneEvenCumulant n := by
  have hn0 : n ≠ 0 := by omega
  have hnne : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  have hpow := rat_four_pow_sub_one_ne_zero n hn
  rw [centeredRvachevEvenCumulant_eq_sinhDiv n hn, hlog,
    bernoulliSinhDivLogCoefficient, bernoulliMersenneEvenCumulant,
    if_neg hn0, if_neg hn0]
  field_simp [hnne, hpow] <;> ring

/-- If the centered even cumulants through order `2N` have the
Bernoulli--Mersenne form, then the centered moments satisfy exactly the
spectral report's recurrence. -/
theorem moment_bernoulliMersenne_recurrence_of_evenCumulants
    (N : ℕ) (hN : 1 ≤ N)
    (hcumulant : ∀ r ∈ Icc 1 N,
      centeredRvachevEvenCumulant r = bernoulliMersenneEvenCumulant r) :
    moment N =
      (∑ r ∈ Icc 1 N,
        (Nat.choose (2 * N) (2 * r) : ℚ) *
          ((2 : ℚ) ^ (2 * r - 1) * bernoulli (2 * r) /
            ((4 : ℚ) ^ r - 1)) * moment (N - r)) / (N : ℚ) := by
  rw [moment_centeredRvachevEvenCumulant_recurrence N hN]
  apply congrArg (fun z : ℚ => z / (N : ℚ))
  apply Finset.sum_congr rfl
  intro r hr
  have hrpos : 1 ≤ r := (mem_Icc.1 hr).1
  have hr0 : r ≠ 0 := by omega
  have hrne : (r : ℚ) ≠ 0 := by exact_mod_cast hr0
  have hpow := rat_four_pow_sub_one_ne_zero r hrpos
  rw [hcumulant r hr, bernoulliMersenneEvenCumulant, if_neg hr0]
  field_simp [hrne, hpow] <;> ring

/-- A finite segment of the one-scale Bernoulli logarithm is sufficient for
the corresponding finite centered-moment recurrence.  This theorem isolates
the exact remaining formal-series obligation in the spectral report. -/
theorem moment_bernoulliMersenne_recurrence_of_sinhDivLog
    (N : ℕ) (hN : 1 ≤ N)
    (hlog : ∀ r ∈ Icc 1 N,
      sinhDivLogCoefficient r = bernoulliSinhDivLogCoefficient r) :
    moment N =
      (∑ r ∈ Icc 1 N,
        (Nat.choose (2 * N) (2 * r) : ℚ) *
          ((2 : ℚ) ^ (2 * r - 1) * bernoulli (2 * r) /
            ((4 : ℚ) ^ r - 1)) * moment (N - r)) / (N : ℚ) := by
  apply moment_bernoulliMersenne_recurrence_of_evenCumulants N hN
  intro r hr
  exact centeredRvachevEvenCumulant_eq_bernoulliMersenne_of_sinhDiv
    r (mem_Icc.1 hr).1 (hlog r hr)

/-- The Bernoulli--Mersenne recurrence is unconditional in degree one. -/
theorem moment_bernoulliMersenne_recurrence_one :
    moment 1 =
      (∑ r ∈ Icc 1 1,
        (Nat.choose 2 (2 * r) : ℚ) *
          ((2 : ℚ) ^ (2 * r - 1) * bernoulli (2 * r) /
            ((4 : ℚ) ^ r - 1)) * moment (1 - r)) := by
  have h := moment_bernoulliMersenne_recurrence_of_sinhDivLog 1 (by omega)
    (fun r hr => by
      have : r = 1 := by
        have := mem_Icc.1 hr
        omega
      subst r
      rw [sinhDivLogCoefficient_one,
        bernoulliSinhDivLogCoefficient_one])
  simpa using h

/-- The Bernoulli--Mersenne recurrence is unconditional in degree two. -/
theorem moment_bernoulliMersenne_recurrence_two :
    moment 2 =
      (∑ r ∈ Icc 1 2,
        (Nat.choose 4 (2 * r) : ℚ) *
          ((2 : ℚ) ^ (2 * r - 1) * bernoulli (2 * r) /
            ((4 : ℚ) ^ r - 1)) * moment (2 - r)) / 2 := by
  apply moment_bernoulliMersenne_recurrence_of_sinhDivLog 2 (by omega)
  intro r hr
  have hrbounds := mem_Icc.1 hr
  have hrange : r = 1 ∨ r = 2 := by omega
  rcases hrange with rfl | rfl
  · rw [sinhDivLogCoefficient_one,
      bernoulliSinhDivLogCoefficient_one]
  · rw [sinhDivLogCoefficient_two,
      bernoulliSinhDivLogCoefficient_two]

end

end Fabius
