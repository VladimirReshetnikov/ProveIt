import Surreal.Foundations.MonomialPowerSeries
import Surreal.Foundations.OmnificScaleGaps
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# The bounded-exponent telescope in actual surreal numbers

The actual-surreal case of `osq:lem:telescope`, `osq:eq:telescope` and
`osq:eq:finitetelescope`. The geometric series is first evaluated as one
actual surreal number, with its exact normal-form coefficients. Its finite
product identity then gives a certificate inside the purely infinite ideal.
No homomorphism is required to preserve an infinite sum.
-/

universe u
namespace Surreal.Foundations.SignSequence
open SmallNormalForm
noncomputable section

/-- The geometric quotient, evaluated by the established monomial substitution. -/
def omnificTelescope (c a b : SignSequence.{u}) (hba : b < a) : SignSequence.{u} :=
  omegaPower (c - a) * monomialEvaluation (a - b) (sub_pos.mpr hba) (PowerSeries.mk 1)

/-- Every displayed coefficient of the geometric telescope is one. -/
theorem omnificTelescope_coeff (c a b : SignSequence.{u}) (hba : b < a) (n : ℕ) :
    coeff (normalForm (omnificTelescope c a b hba)) (c - a - (n : SignSequence) * (a - b)) = 1 := by
  have he : c - a - (n : SignSequence) * (a - b) = c - a + (n : SignSequence) * (-(a - b)) := by ring
  rw [he, omnificTelescope, coeff_normalForm_omegaPower_mul, coeff_monomialEvaluation]
  simp only [PowerSeries.coeff_mk, Pi.one_apply]

/-- No exponent outside the displayed geometric progression occurs. -/
theorem omnificTelescope_coeff_eq_zero (c a b : SignSequence.{u}) (hba : b < a)
    (e : SignSequence.{u}) (he : ∀ n : ℕ, e ≠ c - a - (n : SignSequence) * (a - b)) :
    coeff (normalForm (omnificTelescope c a b hba)) e = 0 := by
  have hs : e = (c - a) + (e - (c - a)) := by ring
  rw [omnificTelescope, hs, coeff_normalForm_omegaPower_mul]
  apply coeff_monomialEvaluation_eq_zero
  intro n hn
  apply he n
  linear_combination hn

/-- The support is exactly the range of the ordinary geometric exponents. -/
theorem omnificTelescope_support (c a b : SignSequence.{u}) (hba : b < a) :
    support (normalForm (omnificTelescope c a b hba)) =
      Set.range (fun n : ℕ => c - a - (n : SignSequence) * (a - b)) := by
  ext e
  constructor
  · intro he
    by_contra hn
    exact he (omnificTelescope_coeff_eq_zero c a b hba e (by
      intro n hen
      exact hn ⟨n, hen.symm⟩))
  · rintro ⟨n, rfl⟩
    rw [mem_support, omnificTelescope_coeff]
    exact one_ne_zero

/-- In particular the telescope has countable support. -/
theorem omnificTelescope_support_countable (c a b : SignSequence.{u}) (hba : b < a) :
    (support (normalForm (omnificTelescope c a b hba))).Countable := by
  rw [omnificTelescope_support]
  exact Set.countable_range _

/-- The geometric exponents strictly decrease. -/
theorem omnificTelescope_exponents_strictAnti (c a b : SignSequence.{u}) (hba : b < a) :
    StrictAnti (fun n : ℕ => c - a - (n : SignSequence) * (a - b)) := by
  intro m n hmn
  have hm : (m : SignSequence.{u}) < n := Nat.cast_lt.mpr hmn
  have := mul_lt_mul_of_pos_right hm (sub_pos.mpr hba)
  linarith

/-- The infinite geometric identity is an identity of two already constructed field elements. -/
theorem omnificTelescope_mul (c a b : SignSequence.{u}) (hba : b < a) :
    (omegaPower a - omegaPower b) * omnificTelescope c a b hba = omegaPower c := by
  have hg := congrArg (monomialEvaluation (a - b) (sub_pos.mpr hba))
    (PowerSeries.mk_one_mul_one_sub_eq_one ℝ)
  rw [map_mul, map_sub, map_one, monomialEvaluation_X] at hg
  have he : (omegaPower a - omegaPower b) * omegaPower (c - a) =
      omegaPower c * (1 - omegaPower (-(a - b))) := by
    rw [sub_mul, mul_sub, mul_one, ← omegaPower_add, ← omegaPower_add, ← omegaPower_add]
    congr 1 <;> congr 1 <;> ring
  rw [omnificTelescope, ← mul_assoc, he]
  calc
    omegaPower c * (1 - omegaPower (-(a - b))) *
        monomialEvaluation (a - b) (sub_pos.mpr hba) (PowerSeries.mk 1) =
      omegaPower c * (monomialEvaluation (a - b) (sub_pos.mpr hba) (PowerSeries.mk 1) *
        (1 - omegaPower (-(a - b)))) := by ring
    _ = omegaPower c := by rw [hg, mul_one]

/-- Every finite partial telescope retains its explicit remainder monomial. -/
theorem omnificTelescope_partial_mul (c a b : SignSequence.{u}) (N : ℕ) :
    (omegaPower a - omegaPower b) *
      (∑ n ∈ Finset.range (N + 1), omegaPower (c - a - (n : SignSequence) * (a - b))) =
      omegaPower c - omegaPower (c - ((N + 1 : ℕ) : SignSequence) * (a - b)) := by
  have hstep (n : ℕ) :
      (omegaPower a - omegaPower b) * omegaPower (c - a - (n : SignSequence) * (a - b)) =
        omegaPower (c - (n : SignSequence) * (a - b)) -
          omegaPower (c - ((n + 1 : ℕ) : SignSequence) * (a - b)) := by
    rw [sub_mul, ← omegaPower_add, ← omegaPower_add, Nat.cast_add, Nat.cast_one]
    congr 1 <;> congr 1 <;> ring
  induction N with
  | zero => simpa using hstep 0
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih, hstep]
    ring

/-- Even the finite remainder has strictly positive growth exponent. -/
theorem omnificTelescope_remainder_pos (c a b : SignSequence.{u}) (hb : 0 < b)
    (hac : ∀ n : ℕ, (n : SignSequence) * a < c) (N : ℕ) :
    0 < c - ((N + 1 : ℕ) : SignSequence) * (a - b) := by
  have hn := hac (N + 1)
  have hnb := mul_nonneg (Nat.cast_nonneg (N + 1) : (0 : SignSequence.{u}) ≤ (N + 1 : ℕ)) hb.le
  nlinarith

/-- Every finite remainder monomial is infinite, despite the exact infinite telescope. -/
theorem omnificTelescope_remainder_not_finite (c a b : SignSequence.{u}) (hb : 0 < b)
    (hac : ∀ n : ℕ, (n : SignSequence) * a < c) (N : ℕ) :
    ¬ IsFinite (omegaPower (c - ((N + 1 : ℕ) : SignSequence) * (a - b))) := by
  rw [finite_iff_leadingExponent_nonpos (omegaPower_ne_zero _), leadingExponent_omegaPower]
  exact (omnificTelescope_remainder_pos c a b hb hac N).not_ge

/-- Subordination makes every geometric exponent positive. -/
theorem omnificTelescope_exponent_pos (c a b : SignSequence.{u}) (hb : 0 < b)
    (hac : ∀ n : ℕ, (n : SignSequence) * a < c) (n : ℕ) :
    0 < c - a - (n : SignSequence) * (a - b) := by
  have hn := hac (n + 1)
  rw [Nat.cast_add, Nat.cast_one] at hn
  have hnb := mul_nonneg (Nat.cast_nonneg n : (0 : SignSequence.{u}) ≤ n) hb.le
  nlinarith

/-- The geometric quotient belongs to the actual purely infinite omnific ideal. -/
theorem omnificTelescope_purelyInfinite (c a b : SignSequence.{u}) (hb : 0 < b)
    (hba : b < a) (hac : ∀ n : ℕ, (n : SignSequence) * a < c) :
    ∃ q ∈ omnificPurelyInfiniteIdeal, omnificToSurreal q = omnificTelescope c a b hba := by
  apply exists_purelyInfinite_of_support_pos
  intro e he
  rw [omnificTelescope_support] at he
  obtain ⟨n, rfl⟩ := he
  exact omnificTelescope_exponent_pos c a b hb hac n

/-- A finite multiplicative certificate inside the actual omnific ring. -/
theorem omnific_monomial_difference_certificate (c a b : SignSequence.{u}) (hb : 0 < b)
    (hba : b < a) (hac : ∀ n : ℕ, (n : SignSequence) * a < c) :
    ∃ q ∈ omnificPurelyInfiniteIdeal,
      (omnificMonomial a (hb.trans hba) - omnificMonomial b hb) * q =
        omnificMonomial c (by simpa only [Nat.cast_zero, zero_mul] using hac 0) := by
  obtain ⟨q, hq, he⟩ := omnificTelescope_purelyInfinite c a b hb hba hac
  refine ⟨q, hq, omnificToSurreal_injective ?_⟩
  rw [map_mul, map_sub, omnificToSurreal_monomial, omnificToSurreal_monomial,
    omnificToSurreal_monomial, he, omnificTelescope_mul]

end
end Surreal.Foundations.SignSequence
