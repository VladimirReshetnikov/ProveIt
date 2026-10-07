import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

noncomputable def integerAbsInterval (B : ℝ) : Finset ℤ :=
  Finset.Icc (-⌊B⌋) ⌊B⌋

theorem mem_integerAbsInterval (B : ℝ) (z : ℤ) :
    z ∈ integerAbsInterval B ↔ |(z : ℝ)| ≤ B := by
  rw [integerAbsInterval, Finset.mem_Icc, abs_le]
  constructor
  · rintro ⟨hlo, hhi⟩
    have hn : -z ≤ ⌊B⌋ := by omega
    have hn' := Int.le_floor.mp hn
    have hp := Int.le_floor.mp hhi
    push_cast at hn'
    exact ⟨by linarith, hp⟩
  · rintro ⟨hlo, hhi⟩
    have hn : (-z : ℤ) ≤ ⌊B⌋ := Int.le_floor.mpr (by push_cast; linarith)
    exact ⟨by omega, Int.le_floor.mpr hhi⟩

theorem integerAbsInterval_card_le (B : ℝ) (hB : 0 ≤ B) :
    ((integerAbsInterval B).card : ℝ) ≤ 2 * B + 1 := by
  have hf : (0 : ℤ) ≤ ⌊B⌋ := Int.floor_nonneg.mpr hB
  have hc : ((integerAbsInterval B).card : ℤ) = 2 * ⌊B⌋ + 1 := by
    rw [integerAbsInterval, Int.card_Icc]
    omega
  have hc' : ((integerAbsInterval B).card : ℝ) = 2 * (⌊B⌋ : ℝ) + 1 := by
    exact_mod_cast hc
  rw [hc']
  linarith [Int.floor_le B]

theorem integerAbsInterval_card_le_three (B : ℝ) (hB : 1 ≤ B) :
    ((integerAbsInterval B).card : ℝ) ≤ 3 * B :=
  (integerAbsInterval_card_le B (by linarith)).trans (by linarith)

end Erdos3

end

end OAI
