import Surreal.Foundations.OmnificFloor

/-!
# Ordered division in the omnific integers

The quotient, remainder, and their uniqueness in `odg:prop:division`.
Division takes place in the actual surreal fraction field before applying
the omnific floor. The order bounds do not assert termination of a
Euclidean algorithm.
-/

universe u
namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The ordered quotient is the omnific floor of the surreal quotient. -/
def omnificQuotient (a b : OmnificInteger.{u}) : OmnificInteger.{u} :=
  omnificFloor (omnificToSurreal a / omnificToSurreal b)

/-- The remainder associated to the ordered quotient. -/
def omnificRemainder (a b : OmnificInteger.{u}) : OmnificInteger.{u} :=
  a - b * omnificQuotient a b

/-- The quotient and remainder reconstruct the dividend. -/
theorem omnific_quotient_remainder (a b : OmnificInteger.{u}) :
    a = b * omnificQuotient a b + omnificRemainder a b := by
  unfold omnificRemainder
  ring

/-- For a positive divisor, the floor bounds give exactly the required remainder interval. -/
theorem omnific_remainder_bounds_iff (a b q : OmnificInteger.{u}) (hb : 0 < b) :
    (0 ≤ a - b * q ∧ a - b * q < b) ↔
      (omnificToSurreal q ≤ omnificToSurreal a / omnificToSurreal b ∧
        omnificToSurreal a / omnificToSurreal b < omnificToSurreal q + 1) := by
  have hb' : 0 < omnificToSurreal b := hb
  rw [le_div_iff₀ hb', div_lt_iff₀ hb']
  change (0 ≤ omnificToSurreal a - omnificToSurreal b * omnificToSurreal q ∧
    omnificToSurreal a - omnificToSurreal b * omnificToSurreal q < omnificToSurreal b) ↔ _
  constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> nlinarith

/-- The ordered remainder is nonnegative and strictly smaller than a positive divisor. -/
theorem omnificRemainder_bounds (a b : OmnificInteger.{u}) (hb : 0 < b) :
    0 ≤ omnificRemainder a b ∧ omnificRemainder a b < b :=
  (omnific_remainder_bounds_iff a b _ hb).mpr (omnificFloor_spec _)

/-- Any quotient producing an admissible remainder is the floor quotient. -/
theorem omnificQuotient_eq_of_bounds (a b q : OmnificInteger.{u}) (hb : 0 < b)
    (hq : 0 ≤ a - b * q ∧ a - b * q < b) : q = omnificQuotient a b :=
  omnific_integerPart_unique _ _ _ ((omnific_remainder_bounds_iff a b q hb).mp hq)
    (omnificFloor_spec _)

/-- An admissible quotient/remainder pair agrees with the explicit floor construction. -/
theorem omnific_division_unique (a b q r : OmnificInteger.{u}) (hb : 0 < b)
    (he : a = b * q + r) (hr : 0 ≤ r ∧ r < b) :
    q = omnificQuotient a b ∧ r = omnificRemainder a b := by
  have hre : r = a - b * q := by rw [he]; ring
  have hq := omnificQuotient_eq_of_bounds a b q hb (hre ▸ hr)
  exact ⟨hq, by rw [hre, hq]; rfl⟩

/-- Ordered division has a unique quotient/remainder pair (`odg:prop:division`). -/
theorem existsUnique_omnific_division (a b : OmnificInteger.{u}) (hb : 0 < b) :
    ∃! qr : OmnificInteger.{u} × OmnificInteger.{u},
      a = b * qr.1 + qr.2 ∧ 0 ≤ qr.2 ∧ qr.2 < b := by
  refine ⟨(omnificQuotient a b, omnificRemainder a b),
    ⟨omnific_quotient_remainder a b, omnificRemainder_bounds a b hb⟩, ?_⟩
  rintro ⟨q, r⟩ ⟨he, hr⟩
  obtain ⟨hq, hr⟩ := omnific_division_unique a b q r hb he hr
  exact Prod.ext hq hr

/-- A positive divisor divides the dividend exactly when its ordered remainder is zero. -/
theorem omnific_dvd_iff_remainder_eq_zero (a b : OmnificInteger.{u}) (hb : 0 < b) :
    b ∣ a ↔ omnificRemainder a b = 0 := by
  constructor
  · rintro ⟨q, hq⟩
    have h := omnific_division_unique a b q 0 hb (by simpa using hq) ⟨le_rfl, hb⟩
    exact h.2.symm
  · intro hr
    exact ⟨omnificQuotient a b, by
      simpa only [hr, _root_.add_zero] using omnific_quotient_remainder a b⟩

end
end Surreal.Foundations.SignSequence
