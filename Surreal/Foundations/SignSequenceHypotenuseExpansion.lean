import Surreal.Foundations.SignSequenceBinomial
import Surreal.Foundations.SignSequenceRelativeAsymptotics
import Surreal.Surcomplex.PowerSeriesTruncation

/-!
# Hypotenuse expansions with finite actual remainders

The positive square root of `p^2 + y^2`, where `p` is positive appreciable
and `y` is infinitesimal, has its quartic expansion with an exact finite
sixth-order remainder. These unit-denominator expansions support the
normalized-coordinate formulas in `trigonometry:thm:flat` and
`trigonometry:eq:flatslack`.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

private theorem standardPart_pow_of_finite {x : SignSequence.{u}}
    (hx : IsFinite x) (n : ℕ) : standardPart (x ^ n) = standardPart x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, standardPart_mul (finite_pow hx n) hx, ih, pow_succ]

/-- The square-root series through its quadratic term has a finite cubic tail of residue `1/16`. -/
theorem sqrt_one_add_expansion (t : SignSequence.{u}) (ht : IsInfinitesimal t) :
    ∃ R : SignSequence.{u}, IsFinite R ∧ standardPart R = 1 / 16 ∧
      sqrt (1 + t) = 1 + t / 2 - t ^ 2 / 8 + t ^ 3 * R := by
  obtain ⟨R, hR, hr, he⟩ := exists_finite_powerSeries_remainder t ht
    (PowerSeries.binomialSeries ℝ (1 / 2 : ℝ)) 3
  rw [← binomialPower, binomialPower_half_eq_sqrt] at he
  have hs2 : Polynomial.smeval (2 : Polynomial ℤ) (1 / 2 : ℝ) = 2 := by
    simpa using Polynomial.smeval_natCast ℤ (1 / 2 : ℝ) 2
  norm_num [PowerSeries.binomialSeries_coeff, Ring.choose_eq_smul,
    descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_sub,
    Polynomial.smeval_X, Polynomial.smeval_one, Polynomial.smeval_natCast,
    Finset.sum_range_succ, map_div₀, map_ofNat, hs2] at hr he
  exact ⟨R, hR, hr, by linear_combination he⟩

/-- A positive hypotenuse factors through the binomial half-power of its squared slope. -/
theorem sqrt_sq_add_sq_eq_mul_binomial {p y : SignSequence.{u}}
    (hp : 0 < p) (hy : IsInfinitesimal (y / p)) :
    sqrt (p ^ 2 + y ^ 2) =
      p * binomialPower ((y / p) ^ 2) ((infinitesimal_sq_iff _).mpr hy) (1 / 2 : ℝ) := by
  apply sqrt_eq_of_nonneg_sq
    (mul_nonneg hp.le (binomialPower_pos _ _ _).le)
  rw [mul_pow, binomialPower_half_sq]
  field_simp [hp.ne']

private theorem infinitesimal_div_appreciable {p y : SignSequence.{u}}
    (hpf : IsFinite p) (hps : 0 < standardPart p) (hy : IsInfinitesimal y) :
    IsInfinitesimal (y / p) := by
  exact infinitesimal_mul_finite hy (finite_inv_of_standardPart_ne_zero hpf hps.ne')

/-- A positive appreciable leg and an infinitesimal leg have a finite hypotenuse. -/
theorem finite_sqrt_sq_add_sq {p y : SignSequence.{u}}
    (hp : 0 < p) (hpf : IsFinite p) (hps : 0 < standardPart p) (hy : IsInfinitesimal y) :
    IsFinite (sqrt (p ^ 2 + y ^ 2)) := by
  rw [sqrt_sq_add_sq_eq_mul_binomial hp (infinitesimal_div_appreciable hpf hps hy)]
  exact finite_mul hpf (isFinite_binomialPower _ _ _)

/-- The infinitesimal perpendicular leg does not change the hypotenuse's standard part. -/
theorem standardPart_sqrt_sq_add_sq {p y : SignSequence.{u}}
    (hp : 0 < p) (hpf : IsFinite p) (hps : 0 < standardPart p) (hy : IsInfinitesimal y) :
    standardPart (sqrt (p ^ 2 + y ^ 2)) = standardPart p := by
  rw [sqrt_sq_add_sq_eq_mul_binomial hp (infinitesimal_div_appreciable hpf hps hy),
    standardPart_mul hpf (isFinite_binomialPower _ _ _), standardPart_binomialPower]
  exact mul_one _

/-- The actual hypotenuse differs infinitesimally from its appreciable leg. -/
theorem infinitesimal_sqrt_sq_add_sq_sub {p y : SignSequence.{u}}
    (hp : 0 < p) (hpf : IsFinite p) (hps : 0 < standardPart p) (hy : IsInfinitesimal y) :
    IsInfinitesimal (sqrt (p ^ 2 + y ^ 2) - p) := by
  apply (standardPart_eq_zero_iff (finite_sub (finite_sqrt_sq_add_sq hp hpf hps hy) hpf)).mp
  rw [standardPart_sub (finite_sqrt_sq_add_sq hp hpf hps hy) hpf,
    standardPart_sqrt_sq_add_sq hp hpf hps hy, sub_self]

/-- The quartic hypotenuse expansion has an exact finite sixth-order tail with known residue. -/
theorem sqrt_sq_add_sq_expansion {p y : SignSequence.{u}}
    (hp : 0 < p) (hpf : IsFinite p) (hps : 0 < standardPart p) (hy : IsInfinitesimal y) :
    ∃ R : SignSequence.{u}, IsFinite R ∧ standardPart R = 1 / (16 * standardPart p ^ 5) ∧
      sqrt (p ^ 2 + y ^ 2) = p + y ^ 2 / (2 * p) - y ^ 4 / (8 * p ^ 3) + y ^ 6 * R := by
  have hs := infinitesimal_div_appreciable hpf hps hy
  obtain ⟨R, hRf, hRs, hRe⟩ := sqrt_one_add_expansion ((y / p) ^ 2)
    ((infinitesimal_sq_iff _).mpr hs)
  have hpi := finite_inv_of_standardPart_ne_zero hpf hps.ne'
  refine ⟨R * (p⁻¹) ^ 5, finite_mul hRf (finite_pow hpi 5), ?_, ?_⟩
  · rw [standardPart_mul hRf (finite_pow hpi 5), hRs,
      standardPart_pow_of_finite hpi, standardPart_inv_of_ne_zero hpf hps.ne']
    field_simp
  · rw [sqrt_sq_add_sq_eq_mul_binomial hp hs, binomialPower_half_eq_sqrt, hRe]
    field_simp [hp.ne']

/-- The quadratic hypotenuse expansion has a finite quartic tail with its exact residue. -/
theorem sqrt_sq_add_sq_quadratic_expansion {p y : SignSequence.{u}}
    (hp : 0 < p) (hpf : IsFinite p) (hps : 0 < standardPart p) (hy : IsInfinitesimal y) :
    ∃ R : SignSequence.{u}, IsFinite R ∧ standardPart R = -1 / (8 * standardPart p ^ 3) ∧
      sqrt (p ^ 2 + y ^ 2) = p + y ^ 2 / (2 * p) + y ^ 4 * R := by
  obtain ⟨R, hRf, hRs, he⟩ := sqrt_sq_add_sq_expansion hp hpf hps hy
  have hpi := finite_inv_of_standardPart_ne_zero hpf hps.ne'
  have hyf := finite_of_infinitesimal hy
  have hy2 : standardPart (y ^ 2) = 0 :=
    (standardPart_eq_zero_iff (finite_pow hyf 2)).mpr ((infinitesimal_sq_iff _).mpr hy)
  refine ⟨ofReal (-1 / 8 : ℝ) * (p⁻¹) ^ 3 + y ^ 2 * R,
    finite_add (finite_mul (finite_ofReal _) (finite_pow hpi 3))
      (finite_mul (finite_pow hyf 2) hRf), ?_, ?_⟩
  · rw [standardPart_add (finite_mul (finite_ofReal _) (finite_pow hpi 3))
        (finite_mul (finite_pow hyf 2) hRf),
      standardPart_mul (finite_ofReal _) (finite_pow hpi 3), standardPart_ofReal,
      standardPart_pow_of_finite hpi, standardPart_inv_of_ne_zero hpf hps.ne',
      standardPart_mul (finite_pow hyf 2) hRf, hy2]
    field_simp
    ring
  · rw [he]
    norm_num only [map_div₀, map_neg, map_one, map_ofNat]
    field_simp [hp.ne']
    ring

/-- The hypotenuse excess is exactly the squared height times a finite positive-residue factor. -/
theorem sqrt_sq_add_sq_sub_leading_factor {p y : SignSequence.{u}}
    (hp : 0 < p) (hpf : IsFinite p) (hps : 0 < standardPart p) (hy : IsInfinitesimal y) :
    ∃ R : SignSequence.{u}, IsFinite R ∧ standardPart R = 1 / (2 * standardPart p) ∧
      sqrt (p ^ 2 + y ^ 2) - p = y ^ 2 * R := by
  obtain ⟨R, hRf, hRs, he⟩ := sqrt_sq_add_sq_quadratic_expansion hp hpf hps hy
  have hpi := finite_inv_of_standardPart_ne_zero hpf hps.ne'
  have hyf := finite_of_infinitesimal hy
  have hy2 : standardPart (y ^ 2) = 0 :=
    (standardPart_eq_zero_iff (finite_pow hyf 2)).mpr ((infinitesimal_sq_iff _).mpr hy)
  refine ⟨ofReal (1 / 2 : ℝ) * p⁻¹ + y ^ 2 * R,
    finite_add (finite_mul (finite_ofReal _) hpi)
      (finite_mul (finite_pow hyf 2) hRf), ?_, ?_⟩
  · rw [standardPart_add (finite_mul (finite_ofReal _) hpi)
        (finite_mul (finite_pow hyf 2) hRf),
      standardPart_mul (finite_ofReal _) hpi, standardPart_ofReal,
      standardPart_inv_of_ne_zero hpf hps.ne',
      standardPart_mul (finite_pow hyf 2) hRf, hy2]
    field_simp
    ring
  · rw [he]
    norm_num only [map_div₀, map_one, map_ofNat]
    field_simp [hp.ne']
    ring

end
end Surreal.Foundations.SignSequence
