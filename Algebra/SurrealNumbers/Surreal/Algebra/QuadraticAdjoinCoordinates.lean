import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic

/-!
# Rational coordinates in a quadratic simple extension

The field-theoretic prerequisite of `odg:def:lem:tailored`: if x is
irrational and x² is rational, every element of Q(x) is a + bx.
-/

namespace Surreal.QuadraticAdjoinCoordinates

variable {K : Type*} [Field K] [CharZero K]

/-- An irrational element and one are linearly independent over the rationals. -/
theorem affine_eq_zero {x : K} (hx : ∀ r : ℚ, x ≠ (r : K)) (a b : ℚ)
    (h : (a : K) + (b : K) * x = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst b
    simp only [Rat.cast_zero, zero_mul, add_zero] at h
    exact ⟨by exact_mod_cast h, rfl⟩
  · exfalso
    apply hx (-a / b)
    have hbK : (b : K) ≠ 0 := by exact_mod_cast hb
    push_cast
    apply (eq_div_iff hbK).mpr
    linear_combination h

/-- Every element of the simple quadratic field has rational affine coordinates. -/
theorem exists_affine_of_mem_adjoin {x : K} (d : ℚ) (hs : x ^ 2 = (d : K))
    (hx : ∀ r : ℚ, x ≠ (r : K)) {y : K} (hy : y ∈ IntermediateField.adjoin ℚ {x}) :
    ∃ a b : ℚ, y = (a : K) + (b : K) * x := by
  refine IntermediateField.adjoin_induction ℚ ?_ ?_ ?_ ?_ ?_ hy
  · intro z hz
    obtain rfl : z = x := Set.mem_singleton_iff.mp hz
    exact ⟨0, 1, by simp⟩
  · intro r
    exact ⟨r, 0, by simp⟩
  · intro u v _ _ hu hv
    obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨c, e, rfl⟩ := hv
    exact ⟨a + c, b + e, by push_cast; ring⟩
  · intro u _ hu
    obtain ⟨a, b, rfl⟩ := hu
    by_cases hz : (a : K) + (b : K) * x = 0
    · exact ⟨0, 0, by simp [hz]⟩
    have hprod : ((a : K) + (b : K) * x) * ((a : K) - (b : K) * x) =
        ((a ^ 2 - b ^ 2 * d : ℚ) : K) := by
      push_cast
      linear_combination -(b : K) ^ 2 * hs
    have hden : a ^ 2 - b ^ 2 * d ≠ 0 := by
      intro hd
      have he : ((a : K) + (b : K) * x) * ((a : K) - (b : K) * x) = 0 := by
        rw [hprod, hd, Rat.cast_zero]
      have hc := (mul_eq_zero.mp he).resolve_left hz
      have hab := affine_eq_zero hx a (-b) (by simpa only [Rat.cast_neg, neg_mul, sub_eq_add_neg] using hc)
      have hb : b = 0 := neg_eq_zero.mp hab.2
      exact hz (by simp [hab.1, hb])
    have hdenK : ((a ^ 2 - b ^ 2 * d : ℚ) : K) ≠ 0 := by exact_mod_cast hden
    refine ⟨a / (a ^ 2 - b ^ 2 * d), -b / (a ^ 2 - b ^ 2 * d), ?_⟩
    calc
      _ = ((a : K) - (b : K) * x) / ((a ^ 2 - b ^ 2 * d : ℚ) : K) := by
        apply (eq_div_iff hdenK).mpr
        rw [← hprod, ← mul_assoc, inv_mul_cancel₀ hz, one_mul]
      _ = _ := by push_cast; ring
  · intro u v _ _ hu hv
    obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨c, e, rfl⟩ := hv
    refine ⟨a * c + b * e * d, a * e + b * c, ?_⟩
    push_cast
    linear_combination (b : K) * (e : K) * hs

end Surreal.QuadraticAdjoinCoordinates
