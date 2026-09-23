import Surreal.Foundations.SignSequenceFiniteUnits
import Surreal.Foundations.SignSequenceSqrtInfinitesimal

/-!
# Relative asymptotics in the actual surreal field

Finite units with residue one preserve leading valuations and are closed under
products, reciprocals and quotients. Nonnegative square roots preserve relative
infinitesimal error. These elementary normalization rules support
`trigonometry:eq:defectasym` and the flat-triangle asymptotics in
`trigonometry:thm:flat`.
-/

universe u

namespace Surreal.Foundations.SignSequence

/-- Multiplication by a finite actual surreal preserves infinitesimality. -/
theorem infinitesimal_mul_finite {x y : SignSequence.{u}}
    (hx : IsInfinitesimal x) (hy : IsFinite y) : IsInfinitesimal (x * y) := by
  have hxf := finite_of_infinitesimal hx
  apply (standardPart_eq_zero_iff (finite_mul hxf hy)).mp
  rw [standardPart_mul hxf hy, (standardPart_eq_zero_iff hxf).mpr hx, zero_mul]

/-- A finite actual surreal times an infinitesimal is infinitesimal. -/
theorem finite_mul_infinitesimal {x y : SignSequence.{u}}
    (hx : IsFinite x) (hy : IsInfinitesimal y) : IsInfinitesimal (x * y) := by
  simpa only [mul_comm] using infinitesimal_mul_finite hy hx

/-- Squaring detects infinitesimality, with no sign assumption. -/
theorem infinitesimal_sq_iff (x : SignSequence.{u}) :
    IsInfinitesimal (x ^ 2) ↔ IsInfinitesimal x := by
  constructor
  · intro h
    have ha := infinitesimal_sqrt (sq_nonneg x) h
    rw [sqrt_sq_eq_abs] at ha
    exact infinitesimal_of_abs_le (by simp) ha
  · intro h
    simpa only [pow_two] using infinitesimal_mul_finite h (finite_of_infinitesimal h)

/-- Being infinitesimally close to one already supplies finiteness. -/
theorem finite_of_infinitesimal_sub_one {q : SignSequence.{u}}
    (h : IsInfinitesimal (q - 1)) : IsFinite q := by
  simpa only [sub_add_cancel] using finite_add (finite_of_infinitesimal h) finite_one

/-- An actual surreal infinitesimally close to one has standard part one. -/
theorem standardPart_eq_one_of_infinitesimal_sub_one {q : SignSequence.{u}}
    (h : IsInfinitesimal (q - 1)) : standardPart q = 1 := by
  have hf := finite_of_infinitesimal_sub_one h
  have hs := (standardPart_eq_zero_iff (finite_sub hf finite_one)).mpr h
  rw [standardPart_sub hf finite_one, standardPart_one, sub_eq_zero] at hs
  exact hs

/-- Relative error zero at the residue level is exactly infinitesimal error. -/
theorem infinitesimal_sub_one_iff {q : SignSequence.{u}} :
    IsInfinitesimal (q - 1) ↔ IsFinite q ∧ standardPart q = 1 := by
  constructor
  · intro h
    exact ⟨finite_of_infinitesimal_sub_one h, standardPart_eq_one_of_infinitesimal_sub_one h⟩
  · rintro ⟨hf, hs⟩
    apply (standardPart_eq_zero_iff (finite_sub hf finite_one)).mp
    rw [standardPart_sub hf finite_one, hs, standardPart_one, sub_self]

/-- For a nonnegative normalization, a square near one forces the normalization
itself near one; no finiteness hypothesis is needed. -/
theorem infinitesimal_sub_one_of_sq_sub_one {q : SignSequence.{u}} (hq : 0 ≤ q)
    (h : IsInfinitesimal (q ^ 2 - 1)) : IsInfinitesimal (q - 1) := by
  apply infinitesimal_of_abs_le (y := q ^ 2 - 1) _ h
  calc
    |q - 1| = |q - 1| * 1 := (mul_one _).symm
    _ ≤ |q - 1| * (q + 1) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ = |(q - 1) * (q + 1)| := by rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ q + 1)]
    _ = |q ^ 2 - 1| := by congr 1; ring

/-- A nonnegative element whose square has residue one is finite with residue one. -/
theorem finite_standardPart_eq_one_of_sq_sub_one {q : SignSequence.{u}} (hq : 0 ≤ q)
    (h : IsInfinitesimal (q ^ 2 - 1)) : IsFinite q ∧ standardPart q = 1 :=
  infinitesimal_sub_one_iff.mp (infinitesimal_sub_one_of_sq_sub_one hq h)

/-- A normalization near one is a valuation-zero unit. -/
theorem valuation_eq_zero_of_infinitesimal_sub_one {q : SignSequence.{u}}
    (h : IsInfinitesimal (q - 1)) : valuation q = 0 := by
  apply (valuation_eq_zero_iff_standardPart_ne_zero (finite_of_infinitesimal_sub_one h)).mpr
  rw [standardPart_eq_one_of_infinitesimal_sub_one h]
  exact one_ne_zero

/-- Relative infinitesimal error preserves valuation, at arbitrary input scales. -/
theorem valuation_eq_of_infinitesimal_div_sub_one {x y : SignSequence.{u}} (hy : y ≠ 0)
    (h : IsInfinitesimal (x / y - 1)) : valuation x = valuation y := by
  calc
    valuation x = valuation ((x / y) * y) := by rw [div_mul_cancel₀ _ hy]
    _ = valuation (x / y) + valuation y := valuation_mul _ _
    _ = valuation y := by rw [valuation_eq_zero_of_infinitesimal_sub_one h, _root_.zero_add]

/-- Products of normalizations near one remain near one. -/
theorem infinitesimal_mul_sub_one {p q : SignSequence.{u}}
    (hp : IsInfinitesimal (p - 1)) (hq : IsInfinitesimal (q - 1)) :
    IsInfinitesimal (p * q - 1) := by
  obtain ⟨hpf, hps⟩ := infinitesimal_sub_one_iff.mp hp
  obtain ⟨hqf, hqs⟩ := infinitesimal_sub_one_iff.mp hq
  apply infinitesimal_sub_one_iff.mpr
  exact ⟨finite_mul hpf hqf, by rw [standardPart_mul hpf hqf, hps, hqs, one_mul]⟩

/-- The reciprocal of a normalization near one remains near one. -/
theorem infinitesimal_inv_sub_one {q : SignSequence.{u}}
    (hq : IsInfinitesimal (q - 1)) : IsInfinitesimal (q⁻¹ - 1) := by
  obtain ⟨hqf, hqs⟩ := infinitesimal_sub_one_iff.mp hq
  have hne : standardPart q ≠ 0 := by rw [hqs]; exact one_ne_zero
  apply infinitesimal_sub_one_iff.mpr
  exact ⟨finite_inv_of_standardPart_ne_zero hqf hne,
    by rw [standardPart_inv_of_ne_zero hqf hne, hqs, inv_one]⟩

/-- Quotients of normalizations near one remain near one. -/
theorem infinitesimal_div_sub_one {p q : SignSequence.{u}}
    (hp : IsInfinitesimal (p - 1)) (hq : IsInfinitesimal (q - 1)) :
    IsInfinitesimal (p / q - 1) := by
  simpa only [div_eq_mul_inv] using infinitesimal_mul_sub_one hp (infinitesimal_inv_sub_one hq)

/-- Multiplication preserves relative infinitesimal equivalence. -/
theorem infinitesimal_mul_div_mul_sub_one {a b c d : SignSequence.{u}}
    (hab : IsInfinitesimal (a / b - 1)) (hcd : IsInfinitesimal (c / d - 1)) :
    IsInfinitesimal ((a * c) / (b * d) - 1) := by
  simpa only [div_mul_div_comm] using infinitesimal_mul_sub_one hab hcd

/-- Division preserves relative infinitesimal equivalence. -/
theorem infinitesimal_div_div_div_sub_one {a b c d : SignSequence.{u}}
    (hab : IsInfinitesimal (a / b - 1)) (hcd : IsInfinitesimal (c / d - 1)) :
    IsInfinitesimal ((a / c) / (b / d) - 1) := by
  rw [div_div_div_comm a c b d]
  exact infinitesimal_div_sub_one hab hcd

/-- Taking a nonnegative square root preserves normalization near one. -/
theorem infinitesimal_sqrt_sub_one {q : SignSequence.{u}} (hq : 0 ≤ q)
    (h : IsInfinitesimal (q - 1)) : IsInfinitesimal (sqrt q - 1) := by
  apply infinitesimal_sub_one_of_sq_sub_one (sqrt_nonneg q)
  simpa only [sqrt_sq hq] using h

/-- Positive square roots preserve relative infinitesimal equivalence at arbitrary scales. -/
theorem infinitesimal_sqrt_div_sqrt_sub_one {x y : SignSequence.{u}}
    (hx : 0 ≤ x) (hy : 0 < y) (h : IsInfinitesimal (x / y - 1)) :
    IsInfinitesimal (sqrt x / sqrt y - 1) := by
  apply infinitesimal_sub_one_of_sq_sub_one
    (div_nonneg (sqrt_nonneg x) (sqrt_nonneg y))
  simpa only [div_pow, sqrt_sq hx, sqrt_sq hy.le] using h

end Surreal.Foundations.SignSequence
