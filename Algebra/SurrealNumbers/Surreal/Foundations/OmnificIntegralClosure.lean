import Surreal.Foundations.SignSequenceRoots
import Surreal.Foundations.OmnificRealScaling
import Surreal.Foundations.OmnificSupportBounds
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Integral elements outside the omnific ring

The integral-closure assertions in `odg:prop:notnormal`. Both the real
square root of two and the actual surreal square root of omega squared
plus one are integral over the omnific ring but are not omnific integers.
The previously proved fraction-field structure places both witnesses in
the fraction field of the actual omnific ring.
-/

universe u
namespace Surreal.Foundations.SignSequence

noncomputable section

/-- Any surreal whose square is omnific is integral over the omnific ring. -/
theorem omnific_isIntegral_of_sq (x : SignSequence.{u}) (a : OmnificInteger.{u})
    (hx : x ^ 2 = omnificToSurreal a) : IsIntegral OmnificInteger x := by
  apply IsIntegral.of_pow (n := 2) (by norm_num)
  rw [hx]
  exact isIntegral_algebraMap

/-- The embedded real square root of two is integral over the actual omnific ring. -/
theorem omnific_sqrt_two_isIntegral :
    IsIntegral OmnificInteger.{u} (ofReal (Real.sqrt 2) : SignSequence.{u}) := by
  apply omnific_isIntegral_of_sq _ 2
  rw [← map_pow, Real.sq_sqrt (by norm_num), map_ofNat, map_ofNat]

/-- The real square root of two is not the image of any omnific integer. -/
theorem omnific_sqrt_two_not_mem :
    ¬ ∃ a : OmnificInteger.{u}, omnificToSurreal a = ofReal (Real.sqrt 2) := by
  rintro ⟨a, ha⟩
  obtain ⟨n, rfl⟩ := (omnific_isFinite_iff a).mp (ha ▸ finite_ofReal (Real.sqrt 2))
  have hn : (n : ℝ) = Real.sqrt 2 := by
    apply ofReal_injective
    simpa only [omnificToSurreal_intCast, map_intCast] using ha
  exact irrational_sqrt_two.ne_rational n 1 (by simpa using hn.symm)

/-- A direct omnific numerator and denominator for the real square root of two. -/
theorem omnific_sqrt_two_fraction :
    let w := omnificMonomial (1 : SignSequence.{u}) zero_lt_one
    let hw := omnificMonomial_mem_purelyInfinite (1 : SignSequence.{u}) zero_lt_one
    omnificToSurreal w ≠ 0 ∧
      ofReal (Real.sqrt 2) =
        omnificToSurreal (omnificRealScale (Real.sqrt 2) w hw) / omnificToSurreal w := by
  dsimp only
  rw [omnificToSurreal_realScale, omnificToSurreal_monomial,
    mul_div_cancel_right₀ _ (omegaPower_ne_zero 1)]
  exact ⟨omegaPower_ne_zero 1, rfl⟩

/-- No nonzero omnific square has an omnific square exactly one larger. -/
theorem omnific_sq_add_one_not_sq (w : OmnificInteger.{u}) (hw : w ≠ 0) :
    ¬ ∃ a : OmnificInteger.{u}, a ^ 2 = w ^ 2 + 1 := by
  rintro ⟨a, ha⟩
  have he : (a - w) * (a + w) = 1 := by nlinarith
  have hu : IsUnit (a - w) := isUnit_iff_dvd_one.mpr ⟨a + w, he.symm⟩
  have hv : IsUnit (a + w) := isUnit_iff_dvd_one.mpr ⟨a - w, by rw [mul_comm]; exact he.symm⟩
  rcases (omnific_isUnit_iff _).mp hu with hu | hu <;>
    rcases (omnific_isUnit_iff _).mp hv with hv | hv <;>
    apply hw <;> nlinarith

/-- The actual surreal square root of an omnific square plus one is integral. -/
theorem omnific_sqrt_sq_add_one_isIntegral (w : OmnificInteger.{u}) :
    IsIntegral OmnificInteger (sqrt (omnificToSurreal w ^ 2 + 1)) := by
  apply omnific_isIntegral_of_sq _ (w ^ 2 + 1)
  rw [sqrt_sq (by positivity), map_add, map_pow, map_one]

/-- For every nonzero omnific w, sqrt(w²+1) is outside the omnific ring. -/
theorem omnific_sqrt_sq_add_one_not_mem (w : OmnificInteger.{u}) (hw : w ≠ 0) :
    ¬ ∃ a : OmnificInteger.{u}, omnificToSurreal a = sqrt (omnificToSurreal w ^ 2 + 1) := by
  rintro ⟨a, ha⟩
  apply omnific_sq_add_one_not_sq w hw
  refine ⟨a, omnificToSurreal_injective ?_⟩
  rw [map_pow, ha, sqrt_sq (by positivity), map_add, map_pow, map_one]

/-- The second source witness is integral, positive, outside the ring, and a fraction of
purely infinite omnific integers with nonzero denominator. -/
theorem omnific_omega_sqrt_sq_add_one_witness :
    let x := sqrt (omegaPower (1 : SignSequence.{u}) ^ 2 + 1)
    0 < x ∧ IsIntegral OmnificInteger x ∧
      (¬ ∃ a : OmnificInteger, omnificToSurreal a = x) ∧
      ∃ a b : OmnificInteger, a ∈ omnificPurelyInfiniteIdeal ∧
        b ∈ omnificPurelyInfiniteIdeal ∧ b ≠ 0 ∧
        x = omnificToSurreal a / omnificToSurreal b := by
  refine ⟨sqrt_pos (by positivity), ?_, ?_, surreal_eq_omnific_fraction _⟩
  · exact omnific_sqrt_sq_add_one_isIntegral (omnificMonomial 1 zero_lt_one)
  · exact omnific_sqrt_sq_add_one_not_mem (omnificMonomial 1 zero_lt_one)
      (omnificMonomial_ne_zero _ _)

/-- The actual omnific ring is not integrally closed in its own fraction field. -/
theorem omnific_not_isIntegrallyClosed : ¬ IsIntegrallyClosed OmnificInteger.{u} := by
  intro h
  exact omnific_sqrt_two_not_mem
    ((isIntegrallyClosed_iff SignSequence.{u}).mp h omnific_sqrt_two_isIntegral)

end
end Surreal.Foundations.SignSequence
