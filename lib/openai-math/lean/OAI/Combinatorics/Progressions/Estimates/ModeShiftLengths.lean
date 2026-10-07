import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

noncomputable def modeShiftLength (H T : ℝ) (stride : ℕ) : ℕ :=
  ⌊H / ((stride : ℝ) * T)⌋₊

theorem modeShiftLength_bounds {H T B : ℝ} {stride : ℕ}
    (hs : 0 < stride) (hT : 0 < T) (hB : 1 ≤ B)
    (hsize : (stride : ℝ) * T * (B + 1) ≤ H) :
    B ≤ (modeShiftLength H T stride : ℝ) ∧
      ((stride : ℝ) * T) * (modeShiftLength H T stride : ℝ) ≤ H ∧
      H ≤ (2 * T) * ((stride : ℝ) * (modeShiftLength H T stride : ℝ)) := by
  have hs' : 0 < (stride : ℝ) := by exact_mod_cast hs
  have hd : 0 < (stride : ℝ) * T := mul_pos hs' hT
  have hx : B + 1 ≤ H / ((stride : ℝ) * T) :=
    (le_div_iff₀ hd).mpr (by nlinarith [hsize])
  have hx0 : 0 ≤ H / ((stride : ℝ) * T) := by linarith
  have hf := Nat.lt_floor_add_one (H / ((stride : ℝ) * T))
  have hnb : B < (modeShiftLength H T stride : ℝ) := by
    dsimp [modeShiftLength]
    linarith
  have hu := (le_div_iff₀ hd).mp (Nat.floor_le hx0)
  have hl := (div_lt_iff₀ hd).mp hf
  have hn1 : 1 ≤ (modeShiftLength H T stride : ℝ) := hB.trans hnb.le
  have hprod := mul_le_mul_of_nonneg_left hn1 hd.le
  refine ⟨hnb.le, ?_, ?_⟩
  · change ((stride : ℝ) * T) * (⌊H / ((stride : ℝ) * T)⌋₊ : ℝ) ≤ H
    nlinarith [hu]
  · change H ≤ (2 * T) * ((stride : ℝ) * (⌊H / ((stride : ℝ) * T)⌋₊ : ℝ))
    dsimp [modeShiftLength] at hprod
    nlinarith [hl]

theorem exists_mode_shift_lengths {I K : Type*} (m : ℕ) {D T B ρ r : ℝ}
    (hT : 0 < T) (hB : 1 ≤ B) (hρ : 0 < ρ) (hr : 0 ≤ r)
    (hmove : (m : ℝ) * D ≤ r * ρ * T)
    (H : I → ℝ) (stride : I → ℕ) (hs : ∀ j, 0 < stride j)
    (hsize : ∀ j, (stride j : ℝ) * T * (B + 1) ≤ H j)
    (V : K × I → ℝ) (hwidth : ∀ z, ρ * H z.2 ≤ V z) :
    ∃ N : I → ℕ, (∀ j, B ≤ (N j : ℝ)) ∧
      (∀ j, H j ≤ (2 * T) * ((stride j : ℝ) * (N j : ℝ))) ∧
      ∀ z, (m : ℝ) * D * ((stride z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z := by
  let N := fun j => modeShiftLength (H j) T (stride j)
  have hn j := modeShiftLength_bounds (hs j) hT hB (hsize j)
  refine ⟨N, (fun j => (hn j).1), (fun j => (hn j).2.2), ?_⟩
  intro z
  have hn0 : 0 ≤ (stride z.2 : ℝ) * (N z.2 : ℝ) := by positivity
  calc
    _ ≤ (r * ρ * T) * ((stride z.2 : ℝ) * (N z.2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hmove hn0
    _ = (r * ρ) * (((stride z.2 : ℝ) * T) * (N z.2 : ℝ)) := by ring
    _ ≤ (r * ρ) * H z.2 := mul_le_mul_of_nonneg_left (hn z.2).2.1 (mul_nonneg hr hρ.le)
    _ = r * (ρ * H z.2) := by ring
    _ ≤ r * V z := mul_le_mul_of_nonneg_left (hwidth z) hr

end Erdos3

end

end OAI
