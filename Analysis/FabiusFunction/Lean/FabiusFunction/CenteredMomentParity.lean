import FabiusFunction.CenteredMomentCumulants
import FabiusFunction.SaddleLogExpansionPowerSeries

/-!
# Parity of centered Rvachev cumulants

An even moment-generating series has an even formal logarithm.  The clean
proof is equivariance under the involution `X ↦ -X`: rescaling a coefficient
family by `(-1)^n` commutes with `SaddleExpansion.logCoeff`, while an even
family is fixed by that rescaling.  At an odd index the resulting identity is
`L_n = -L_n`; rational scalar multiplication then gives `L_n = 0` without any
integral-domain hypothesis.

The second half packages the existing compressed series `momentPS` as the
ordinary full exponential generating series in a variable `t`, by replacing
`X` with `t²`.  This supplies unambiguous full-order moment, logarithmic, and
cumulant coefficient families.  Their even moments, logarithmic coefficients,
and cumulants recover the corresponding compressed families, while every odd
moment, logarithmic coefficient, and cumulant vanishes.
-/

set_option autoImplicit false

open PowerSeries

namespace Fabius

noncomputable section

/-! ## A generic parity theorem for formal logarithms -/

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- If every odd coefficient of `a` vanishes, then every odd coefficient of
its recursive formal logarithm vanishes.  No hypothesis on `a 0` is needed:
`logCoeff` intentionally ignores the constant coefficient.  In particular,
when `a 0 = 1`, this is the parity theorem for the formal logarithm of the
unit-constant series with coefficient family `a`. -/
theorem SaddleExpansion.logCoeff_eq_zero_of_odd_coeff
    (a : ℕ → R) (ha : ∀ j, Odd j → a j = 0)
    {n : ℕ} (hn : Odd n) :
    SaddleExpansion.logCoeff a n = 0 := by
  have hrescale : (fun j ↦ (-1 : R) ^ j * a j) = a := by
    funext j
    rcases Nat.even_or_odd j with hj | hj
    · rw [hj.neg_one_pow, one_mul]
    · rw [hj.neg_one_pow, ha j hj, mul_zero]
  have hparity := SaddleExpansion.logCoeff_rescale (-1 : R) a n
  rw [hrescale, hn.neg_one_pow, neg_one_mul] at hparity
  have htwo : (2 : ℚ) • SaddleExpansion.logCoeff a n = 0 := by
    simpa only [two_smul] using
      (eq_neg_iff_add_eq_zero.mp hparity)
  have hinv := congrArg
    (fun z : R ↦ ((2 : ℚ)⁻¹) • z) htwo
  simpa [smul_smul] using hinv

/-- If all odd ordinary moments vanish, then all odd formal cumulants vanish.
This is the exponential-generating-function form of
`SaddleExpansion.logCoeff_eq_zero_of_odd_coeff`. -/
theorem momentCumulant_eq_zero_of_odd_moments
    (mu : ℕ → R) (hmu : ∀ j, Odd j → mu j = 0)
    {n : ℕ} (hn : Odd n) :
    momentCumulant mu n = 0 := by
  have hnormalize : ∀ j, Odd j → factorialNormalize mu j = 0 := by
    intro j hj
    simp [factorialNormalize, hmu j hj]
  rw [momentCumulant, factorialDenormalize,
    SaddleExpansion.logCoeff_eq_zero_of_odd_coeff
      (factorialNormalize mu) hnormalize hn,
    smul_zero]

/-! ## The full centered Rvachev series -/

/-- The ordinary full centered Rvachev moment series in the variable `t`.
It is obtained from the compressed even series `momentPS(X)` by the
substitution `X = t²`. -/
noncomputable def centeredRvachevFullMomentPowerSeries : PowerSeries ℚ :=
  PowerSeries.expand 2 (by omega) momentPS

/-- The coefficient of `t^n` in the full centered Rvachev moment series. -/
def centeredRvachevFullMomentCoefficient (n : ℕ) : ℚ :=
  PowerSeries.coeff n centeredRvachevFullMomentPowerSeries

/-- The even full-series coefficient of order `2n` is the previously defined
compressed coefficient `moment n / (2n)!`. -/
@[simp] theorem centeredRvachevFullMomentCoefficient_even (n : ℕ) :
    centeredRvachevFullMomentCoefficient (2 * n) =
      centeredRvachevMomentCoefficient n := by
  simp [centeredRvachevFullMomentCoefficient,
    centeredRvachevFullMomentPowerSeries]

/-- The full centered Rvachev moment series has unit constant coefficient. -/
@[simp] theorem centeredRvachevFullMomentCoefficient_zero :
    centeredRvachevFullMomentCoefficient 0 = 1 := by
  simpa using centeredRvachevFullMomentCoefficient_even 0

/-- Every odd coefficient of the full centered Rvachev moment series
vanishes. -/
@[simp] theorem centeredRvachevFullMomentCoefficient_odd (n : ℕ) :
    centeredRvachevFullMomentCoefficient (2 * n + 1) = 0 := by
  rw [centeredRvachevFullMomentCoefficient,
    centeredRvachevFullMomentPowerSeries]
  apply PowerSeries.coeff_expand_of_not_dvd
  exact Nat.not_two_dvd_bit1 n

/-- Odd-index form of `centeredRvachevFullMomentCoefficient_odd` stated using
the semantic parity predicate. -/
theorem centeredRvachevFullMomentCoefficient_eq_zero_of_odd
    {n : ℕ} (hn : Odd n) :
    centeredRvachevFullMomentCoefficient n = 0 := by
  obtain ⟨k, rfl⟩ := hn
  exact centeredRvachevFullMomentCoefficient_odd k

/-- The full centered Rvachev moment sequence in ordinary moment
normalization: its exponential generating coefficient is
`centeredRvachevFullMomentCoefficient n`. -/
def centeredRvachevFullMoment (n : ℕ) : ℚ :=
  factorialDenormalize centeredRvachevFullMomentCoefficient n

/-- The even full centered moment of order `2n` is the existing executable
moment `moment n`. -/
@[simp] theorem centeredRvachevFullMoment_even (n : ℕ) :
    centeredRvachevFullMoment (2 * n) = moment n := by
  rw [centeredRvachevFullMoment, factorialDenormalize,
    centeredRvachevFullMomentCoefficient_even]
  exact EvenMomentCumulant.evenFactorialDenormalize_normalize moment n

/-- Every odd full centered Rvachev moment vanishes. -/
theorem centeredRvachevFullMoment_eq_zero_of_odd
    {n : ℕ} (hn : Odd n) :
    centeredRvachevFullMoment n = 0 := by
  simp [centeredRvachevFullMoment, factorialDenormalize,
    centeredRvachevFullMomentCoefficient_eq_zero_of_odd hn]

/-- Canonical-index form: every odd full centered Rvachev moment vanishes. -/
@[simp] theorem centeredRvachevFullMoment_odd (n : ℕ) :
    centeredRvachevFullMoment (2 * n + 1) = 0 := by
  exact centeredRvachevFullMoment_eq_zero_of_odd ⟨n, rfl⟩

/-- The coefficient of order `n` in the formal logarithm of the full centered
Rvachev moment series.  Unlike `centeredRvachevLogCoefficient`, this family is
indexed by the ordinary order rather than by half the even order. -/
def centeredRvachevFullLogCoefficient (n : ℕ) : ℚ :=
  SaddleExpansion.logCoeff centeredRvachevFullMomentCoefficient n

/-- Every odd coefficient of the full centered Rvachev formal logarithm
vanishes. -/
theorem centeredRvachevFullLogCoefficient_eq_zero_of_odd
    {n : ℕ} (hn : Odd n) :
    centeredRvachevFullLogCoefficient n = 0 := by
  exact SaddleExpansion.logCoeff_eq_zero_of_odd_coeff
    centeredRvachevFullMomentCoefficient
    (fun _ hj ↦ centeredRvachevFullMomentCoefficient_eq_zero_of_odd hj) hn

/-- Canonical-index form: every odd coefficient of the full centered Rvachev
formal logarithm vanishes. -/
@[simp] theorem centeredRvachevFullLogCoefficient_odd (n : ℕ) :
    centeredRvachevFullLogCoefficient (2 * n + 1) = 0 := by
  exact centeredRvachevFullLogCoefficient_eq_zero_of_odd ⟨n, rfl⟩

/-- The even full-series logarithmic coefficient of order `2n` is the
existing compressed logarithmic coefficient of order `n`. -/
@[simp] theorem centeredRvachevFullLogCoefficient_even (n : ℕ) :
    centeredRvachevFullLogCoefficient (2 * n) =
      centeredRvachevLogCoefficient n := by
  have hfullMass :
      SaddleExpansion.massSeries centeredRvachevFullMomentCoefficient =
        centeredRvachevFullMomentPowerSeries := by
    ext m
    simp [centeredRvachevFullMomentCoefficient]
  have hcompressedMass :
      SaddleExpansion.massSeries centeredRvachevMomentCoefficient = momentPS := by
    ext m
    simp
  have hmomentPS0 : PowerSeries.constantCoeff momentPS = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp
  have hlogSeries :
      SaddleExpansion.logSeries centeredRvachevFullMomentCoefficient =
        PowerSeries.expand 2 (by omega)
          (SaddleExpansion.logSeries centeredRvachevMomentCoefficient) := by
    rw [SaddleExpansion.logSeries_eq_logOf _
        centeredRvachevFullMomentCoefficient_zero,
      SaddleExpansion.logSeries_eq_logOf _
        centeredRvachevMomentCoefficient_zero,
      hfullMass, hcompressedMass]
    simpa [centeredRvachevFullMomentPowerSeries] using
      (SaddleExpansion.logOf_expand 2 (by omega) momentPS hmomentPS0)
  have hcoeff := congrArg (PowerSeries.coeff (2 * n)) hlogSeries
  simpa only [centeredRvachevFullLogCoefficient,
    centeredRvachevLogCoefficient, SaddleExpansion.coeff_logSeries,
    PowerSeries.coeff_expand_mul] using hcoeff

/-- The full centered Rvachev cumulant of ordinary order `n`. -/
def centeredRvachevFullCumulant (n : ℕ) : ℚ :=
  factorialDenormalize centeredRvachevFullLogCoefficient n

/-- The even full centered Rvachev cumulant of order `2n` is the existing
compressed-even cumulant indexed by `n`. -/
@[simp] theorem centeredRvachevFullCumulant_even (n : ℕ) :
    centeredRvachevFullCumulant (2 * n) =
      centeredRvachevEvenCumulant n := by
  rw [centeredRvachevFullCumulant, factorialDenormalize,
    centeredRvachevFullLogCoefficient_even,
    centeredRvachevEvenCumulant, EvenMomentCumulant.evenMomentCumulant,
    centeredRvachevLogCoefficient, centeredRvachevMomentCoefficient]

/-- Every odd centered Rvachev cumulant vanishes. -/
theorem centeredRvachevFullCumulant_eq_zero_of_odd
    {n : ℕ} (hn : Odd n) :
    centeredRvachevFullCumulant n = 0 := by
  simp [centeredRvachevFullCumulant, factorialDenormalize,
    centeredRvachevFullLogCoefficient_eq_zero_of_odd hn]

/-- Canonical-index form: the centered Rvachev cumulant of order `2n+1`
vanishes for every `n`. -/
@[simp] theorem centeredRvachevFullCumulant_odd (n : ℕ) :
    centeredRvachevFullCumulant (2 * n + 1) = 0 := by
  exact centeredRvachevFullCumulant_eq_zero_of_odd ⟨n, rfl⟩

end

end Fabius
