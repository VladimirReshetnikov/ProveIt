import Surreal.Foundations.OmnificUnits
import Surreal.Foundations.SmallNormalFormCutTruncation
import Mathlib.Algebra.Order.Floor.Ring

/-!
# The exact omnific integer part

The integer-part formula `odg:thm:floor`, including the negative-infinitesimal
correction at an ordinary integer. The positive-growth part is the actual
normal-form truncation, and the residual estimate proves the discarded tail
infinitesimal. Mathlib's ordinary real floor supplies the constant term.
-/

universe u
namespace Surreal.Foundations.SignSequence

open SmallNormalForm

noncomputable section

/-- The strictly positive-growth part, as an actual omnific integer. -/
def positiveGrowthPart (x : SignSequence.{u}) : OmnificInteger.{u} :=
  ⟨⟨cutEvaluation (trunc (normalForm x) 0), by
      rw [mem_nonnegativeSupportSubring_iff]
      intro a ha
      simp only [normalForm_cutEvaluation, coeff_trunc, if_neg (not_lt_of_ge ha.le)]⟩,
    by
      rw [mem_omnificSubring_iff]
      exact ⟨0, by simp⟩⟩

/-- The positive-growth part has zero constant coefficient. -/
@[simp] theorem omnificConstantCoeff_positiveGrowthPart (x : SignSequence.{u}) :
    omnificConstantCoeff (positiveGrowthPart x) = 0 := by
  apply Int.cast_injective (α := ℝ)
  rw [cast_omnificConstantCoeff, Int.cast_zero]
  change coeff (normalForm (cutEvaluation (trunc (normalForm x) 0))) 0 = (0 : ℝ)
  simp

/-- The truncation belongs to the purely infinite omnific ideal. -/
theorem positiveGrowthPart_mem_purelyInfiniteIdeal (x : SignSequence.{u}) :
    positiveGrowthPart x ∈ omnificPurelyInfiniteIdeal :=
  omnificConstantCoeff_positiveGrowthPart x

/-- The tail left after removing positive growth and the real constant term. -/
def infinitesimalTail (x : SignSequence.{u}) : SignSequence.{u} :=
  x - (omnificToSurreal (positiveGrowthPart x) + ofReal (coeff (normalForm x) 0))

/-- Every surreal splits into positive growth, its real coefficient, and the tail. -/
theorem positiveGrowth_constant_tail (x : SignSequence.{u}) :
    x = omnificToSurreal (positiveGrowthPart x) + ofReal (coeff (normalForm x) 0) +
      infinitesimalTail x := by
  unfold infinitesimalTail
  abel

/-- The exact normal-form tail is infinitesimal, including when it is zero. -/
theorem infinitesimal_infinitesimalTail (x : SignSequence.{u}) :
    IsInfinitesimal (infinitesimalTail x) := by
  rw [isInfinitesimal_iff_valuation_pos]
  have h := cutEvaluation_remainder_all (normalForm x) 0
  simpa only [WithTop.coe_zero, neg_zero, cutEvaluation_normalForm, omegaPower_zero,
    mul_one, infinitesimalTail, positiveGrowthPart, omnificToSurreal,
    RingHom.comp_apply, Subring.subtype_apply] using h

/-- The tail retains exactly the strictly negative growth coefficients. -/
theorem coeff_infinitesimalTail (x a : SignSequence.{u}) :
    coeff (normalForm (infinitesimalTail x)) a =
      if a < 0 then coeff (normalForm x) a else 0 := by
  change coeff (normalForm (x - (cutEvaluation (trunc (normalForm x) 0) +
    ofReal (coeff (normalForm x) 0)))) a = _
  rw [normalForm_sub, normalForm_add, normalForm_cutEvaluation, normalForm_ofReal]
  simp only [coeff_sub, coeff_add, coeff_trunc, coeff_single]
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · simp [ha, not_lt_of_ge ha.le, ne_of_lt ha]
  · simp
  · simp [ha, not_lt_of_ge ha.le, ne_of_gt ha]

private theorem real_add_infinitesimal_floor_bounds (r : ℝ) (ε : SignSequence.{u})
    (hε : IsInfinitesimal ε) :
    let n : ℤ := if r = (⌊r⌋ : ℝ) ∧ ε < 0 then ⌊r⌋ - 1 else ⌊r⌋
    (n : SignSequence.{u}) ≤ ofReal r + ε ∧ ofReal r + ε < n + 1 := by
  have hbound := (isInfinitesimal_iff_forall_real_abs_lt ε).mp hε
  have hu := hbound ((⌊r⌋ : ℝ) + 1 - r) (sub_pos.mpr (Int.lt_floor_add_one r))
  rw [map_sub, map_add, map_intCast, map_one] at hu
  obtain ⟨_, hu⟩ := abs_lt.mp hu
  have hle : (⌊r⌋ : SignSequence.{u}) ≤ ofReal r := by
    simpa only [map_intCast] using ofReal_strictMono.monotone (Int.floor_le r)
  dsimp only
  split_ifs with h
  · have he : ofReal r = (⌊r⌋ : SignSequence.{u}) := by
      exact congrArg ofReal h.1 |>.trans (map_intCast ofReal _)
    have hsmall := hbound 1 (by norm_num)
    rw [map_one] at hsmall
    obtain ⟨hl, _⟩ := abs_lt.mp hsmall
    rw [Int.cast_sub, Int.cast_one, he]
    constructor <;> linarith [h.2]
  · by_cases he : r = (⌊r⌋ : ℝ)
    · have hnonneg : 0 ≤ ε := le_of_not_gt (fun hn => h ⟨he, hn⟩)
      constructor <;> linarith
    · have hl := hbound (r - (⌊r⌋ : ℝ)) (sub_pos.mpr (lt_of_le_of_ne
        (Int.floor_le r) (Ne.symm he)))
      rw [map_sub, map_intCast] at hl
      obtain ⟨hl, _⟩ := abs_lt.mp hl
      constructor <;> linarith

/-- The omnific floor, with the correction for a negative tail at an integer constant. -/
def omnificFloor (x : SignSequence.{u}) : OmnificInteger.{u} :=
  positiveGrowthPart x + omnificIntCast
    (if coeff (normalForm x) 0 = (⌊coeff (normalForm x) 0⌋ : ℝ) ∧ infinitesimalTail x < 0
      then ⌊coeff (normalForm x) 0⌋ - 1 else ⌊coeff (normalForm x) 0⌋)

/-- The constructed integer part satisfies the required half-open unit interval. -/
theorem omnificFloor_spec (x : SignSequence.{u}) :
    omnificToSurreal (omnificFloor x) ≤ x ∧ x < omnificToSurreal (omnificFloor x) + 1 := by
  have h := real_add_infinitesimal_floor_bounds (coeff (normalForm x) 0)
    (infinitesimalTail x) (infinitesimal_infinitesimalTail x)
  rw [omnificFloor, map_add, omnificToSurreal_intCast]
  have hx := positiveGrowth_constant_tail x
  dsimp only at h
  constructor <;> linarith [h.1, h.2]

/-- Discreteness makes the omnific integer in a half-open unit interval unique. -/
theorem omnific_integerPart_unique (x : SignSequence.{u}) (a b : OmnificInteger.{u})
    (ha : omnificToSurreal a ≤ x ∧ x < omnificToSurreal a + 1)
    (hb : omnificToSurreal b ≤ x ∧ x < omnificToSurreal b + 1) : a = b := by
  apply le_antisymm
  · by_contra! h
    have hd := one_le_omnific_of_pos (a - b) (sub_pos.mpr h)
    have hd' : (1 : SignSequence.{u}) ≤ omnificToSurreal a - omnificToSurreal b := by
      simpa only [map_one, map_sub] using omnificToSurreal_strictMono.monotone hd
    linarith [ha.1, hb.2]
  · by_contra! h
    have hd := one_le_omnific_of_pos (b - a) (sub_pos.mpr h)
    have hd' : (1 : SignSequence.{u}) ≤ omnificToSurreal b - omnificToSurreal a := by
      simpa only [map_one, map_sub] using omnificToSurreal_strictMono.monotone hd
    linarith [hb.1, ha.2]

/-- Every actual surreal has exactly one omnific integer part (`odg:thm:floor`). -/
theorem existsUnique_omnific_integerPart (x : SignSequence.{u}) :
    ∃! a : OmnificInteger.{u}, omnificToSurreal a ≤ x ∧ x < omnificToSurreal a + 1 :=
  ⟨omnificFloor x, omnificFloor_spec x,
    fun a ha => omnific_integerPart_unique x a (omnificFloor x) ha (omnificFloor_spec x)⟩

/-- Away from a negative infinitesimal displacement at an integer, floor the real coefficient. -/
theorem omnificFloor_of_noninteger_or_nonnegative_tail (x : SignSequence.{u})
    (h : (¬ ∃ n : ℤ, coeff (normalForm x) 0 = (n : ℝ)) ∨ 0 ≤ infinitesimalTail x) :
    omnificFloor x = positiveGrowthPart x + omnificIntCast ⌊coeff (normalForm x) 0⌋ := by
  unfold omnificFloor
  rw [if_neg]
  rintro ⟨he, ht⟩
  rcases h with hn | hp
  · exact hn ⟨_, he⟩
  · exact ht.not_ge hp

/-- At an integer coefficient with negative tail, subtract one from that integer. -/
theorem omnificFloor_of_integer_negative_tail (x : SignSequence.{u}) (n : ℤ)
    (hr : coeff (normalForm x) 0 = (n : ℝ)) (ht : infinitesimalTail x < 0) :
    omnificFloor x = positiveGrowthPart x + omnificIntCast (n - 1) := by
  simp only [omnificFloor, hr, Int.floor_intCast, ht, and_self, if_true]

/-- Taking the floor of an omnific integer returns it. -/
@[simp] theorem omnificFloor_omnificToSurreal (a : OmnificInteger.{u}) :
    omnificFloor (omnificToSurreal a) = a := by
  apply omnific_integerPart_unique _ _ _ (omnificFloor_spec _)
  exact ⟨le_rfl, lt_add_one _⟩

/-- On ordinary reals, omnific floor agrees with Mathlib's integer floor. -/
@[simp] theorem omnificFloor_ofReal (r : ℝ) :
    omnificFloor (ofReal r : SignSequence.{u}) = omnificIntCast ⌊r⌋ := by
  apply omnific_integerPart_unique _ _ _ (omnificFloor_spec _)
  rw [omnificToSurreal_intCast]
  constructor
  · simpa only [map_intCast] using ofReal_strictMono.monotone (Int.floor_le r)
  · simpa only [map_add, map_intCast, map_one] using
      ofReal_strictMono (Int.lt_floor_add_one r)

/-- Floor commutes with translation by any omnific integer. -/
theorem omnificFloor_add_omnific (x : SignSequence.{u}) (a : OmnificInteger.{u}) :
    omnificFloor (x + omnificToSurreal a) = omnificFloor x + a := by
  apply omnific_integerPart_unique _ _ _ (omnificFloor_spec _)
  rw [map_add]
  obtain ⟨hl, hu⟩ := omnificFloor_spec x
  constructor <;> linarith

/-- A negative infinitesimal has floor minus one, the boundary example in the source. -/
theorem omnificFloor_of_negative_infinitesimal {ε : SignSequence.{u}}
    (hε : IsInfinitesimal ε) (hneg : ε < 0) : omnificFloor ε = -1 := by
  apply omnific_integerPart_unique _ _ _ (omnificFloor_spec _)
  have hsmall := (isInfinitesimal_iff_forall_real_abs_lt ε).mp hε 1 (by norm_num)
  rw [map_one] at hsmall
  obtain ⟨hl, _⟩ := abs_lt.mp hsmall
  simp only [map_neg, map_one, neg_add_cancel]
  exact ⟨hl.le, hneg⟩

end
end Surreal.Foundations.SignSequence
