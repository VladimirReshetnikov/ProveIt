import Surreal.Foundations.SignSequenceValuation

/-!
# Scaled valuation bounds as ordinary surreal inequalities

Dividing by the positive Conway monomial converts a valuation threshold
into finiteness or infinitesimality. The latter is equivalent to a countable
family of strict ordinary bounds. These bounds provide the cut options for
small compatible valuation balls in the infinite normal-form construction.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- Monomial scaling turns a weak valuation bound into finiteness. -/
theorem isFinite_div_tMonomial_iff (x a : SignSequence.{u}) :
    IsFinite (x / tMonomial a) ↔ (a : WithTop SignSequence.{u}) ≤ valuation x := by
  rw [isFinite_iff_valuation_nonneg, valuation_div, valuation_tMonomial]
  cases h : valuation x with
  | top => simp
  | coe b =>
    change ((0 : SignSequence.{u}) : WithTop SignSequence.{u}) ≤ ↑(b - a) ↔ ↑a ≤ (b : WithTop SignSequence.{u})
    simp only [WithTop.coe_le_coe, sub_nonneg]

/-- Monomial scaling turns a strict valuation bound into infinitesimality. -/
theorem isInfinitesimal_div_tMonomial_iff (x a : SignSequence.{u}) :
    IsInfinitesimal (x / tMonomial a) ↔ (a : WithTop SignSequence.{u}) < valuation x := by
  rw [isInfinitesimal_iff_valuation_pos, valuation_div, valuation_tMonomial]
  cases h : valuation x with
  | top => simp
  | coe b =>
    change ((0 : SignSequence.{u}) : WithTop SignSequence.{u}) < ↑(b - a) ↔ ↑a < (b : WithTop SignSequence.{u})
    simp only [WithTop.coe_lt_coe, sub_pos]

/-- Strict valuation bounds are all reciprocal-natural monomial bounds.
Zero is included, since its valuation is infinity. -/
theorem valuation_gt_iff_forall_nat_abs_lt (x a : SignSequence.{u}) :
    (a : WithTop SignSequence.{u}) < valuation x ↔
      ∀ n : ℕ, |x| < tMonomial a / ((n : SignSequence.{u}) + 1) := by
  have hscale (n : ℕ) :
      |x / tMonomial a| < 1 / ((n : SignSequence.{u}) + 1) ↔
        |x| < tMonomial a / ((n : SignSequence.{u}) + 1) := by
    rw [abs_div, abs_of_pos (tMonomial_pos a), div_lt_iff₀ (tMonomial_pos a)]
    simp only [div_eq_mul_inv, one_mul, mul_comm]
  rw [← isInfinitesimal_div_tMonomial_iff, isInfinitesimal_iff_forall_nat_abs_lt]
  constructor
  · intro h n
    apply (hscale n).mp
    simpa only [Nat.cast_add, Nat.cast_one] using h (n + 1) (Nat.succ_pos n)
  · intro h n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    simpa only [Nat.cast_succ] using (hscale m).mpr (h m)

/-- A valuation ball is the intersection of its explicit open intervals. -/
theorem valuation_sub_gt_iff_forall_nat_between (x p a : SignSequence.{u}) :
    (a : WithTop SignSequence.{u}) < valuation (x - p) ↔
      ∀ n : ℕ, p - tMonomial a / ((n : SignSequence.{u}) + 1) < x ∧
        x < p + tMonomial a / ((n : SignSequence.{u}) + 1) := by
  rw [valuation_gt_iff_forall_nat_abs_lt]
  apply forall_congr'
  intro n
  rw [abs_lt]
  constructor <;> rintro ⟨hl, hr⟩ <;> constructor <;> linarith

end

end Surreal.Foundations.SignSequence
