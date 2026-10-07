import OAI.Combinatorics.Progressions.Fourier.UniformScaledRetainedCharacters

namespace OAI

section

namespace Erdos3

def positiveModerateLengthExponent (n : ℕ) : ℕ :=
  majorArcLengthExponent n + majorArcLengthExponent (n + 1)

noncomputable def positiveModerateLengthConstant (n : ℕ) (U : ℝ) : ℝ :=
  1 + majorArcLengthConstant n U + majorArcLengthConstant (n + 1) U

def positiveModerateCoverExponent (n j : ℕ) : ℕ :=
  majorArcLengthExponent (n + 1) + majorArcCoverExponent n j +
    majorArcCoverExponent (n + 1) j

noncomputable def positiveModerateCoverConstant (n j : ℕ) (U V : ℝ) : ℝ :=
  (1 + majorArcLengthConstant (n + 1) U) * majorArcCoverConstant n j U (4 * V) +
    majorArcCoverConstant (n + 1) j U V

theorem positiveModerateLengthConstant_pos (n : ℕ) {U : ℝ} (hU : 1 ≤ U) :
    0 < positiveModerateLengthConstant n U := by
  have h0 := majorArcLengthConstant_pos n hU
  have h1 := majorArcLengthConstant_pos (n + 1) hU
  unfold positiveModerateLengthConstant
  positivity

theorem positiveModerateLengthExponent_pos (n : ℕ) :
    0 < positiveModerateLengthExponent n := by
  unfold positiveModerateLengthExponent majorArcLengthExponent
  omega

theorem positiveModerateLengthBudget_bounds (n : ℕ) {U ζ : ℝ}
    (hU : 1 ≤ U) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    majorArcLengthConstant n U / ζ ^ majorArcLengthExponent n ≤
      positiveModerateLengthConstant n U / ζ ^ positiveModerateLengthExponent n ∧
    majorArcLengthConstant (n + 1) U / ζ ^ majorArcLengthExponent (n + 1) ≤
      positiveModerateLengthConstant n U / ζ ^ positiveModerateLengthExponent n := by
  have h0 := majorArcLengthConstant_pos n hU
  have h1 := majorArcLengthConstant_pos (n + 1) hU
  have hC := (positiveModerateLengthConstant_pos n hU).le
  constructor
  · exact inverse_power_mono hC (by unfold positiveModerateLengthConstant; linarith)
      hζ hζ1 (by unfold positiveModerateLengthExponent; omega)
  · exact inverse_power_mono hC (by unfold positiveModerateLengthConstant; linarith)
      hζ hζ1 (by unfold positiveModerateLengthExponent; omega)

theorem positiveModerateCoverConstant_one_le (n j : ℕ) {U V : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) : 1 ≤ positiveModerateCoverConstant n j U V := by
  have hL := majorArcLengthConstant_pos (n + 1) hU
  have hS := majorArcCoverConstant_one_le n j hU (show 0 ≤ 4 * V by positivity)
  have hT := majorArcCoverConstant_one_le (n + 1) j hU hV
  unfold positiveModerateCoverConstant
  nlinarith

theorem positiveModerateCoverBudget_bounds (n j : ℕ) {U V ζ : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    majorArcCoverConstant n j U (4 * V) / ζ ^ majorArcCoverExponent n j ≤
      positiveModerateCoverConstant n j U V / ζ ^ positiveModerateCoverExponent n j ∧
    majorArcCoverConstant (n + 1) j U V / ζ ^ majorArcCoverExponent (n + 1) j ≤
      positiveModerateCoverConstant n j U V / ζ ^ positiveModerateCoverExponent n j ∧
    (majorArcLengthConstant (n + 1) U / ζ ^ majorArcLengthExponent (n + 1)) *
        (majorArcCoverConstant n j U (4 * V) / ζ ^ majorArcCoverExponent n j) ≤
      positiveModerateCoverConstant n j U V / ζ ^ positiveModerateCoverExponent n j := by
  have hL := majorArcLengthConstant_pos (n + 1) hU
  have hS := majorArcCoverConstant_one_le n j hU (show 0 ≤ 4 * V by positivity)
  have hT := majorArcCoverConstant_one_le (n + 1) j hU hV
  have hC := (show (0 : ℝ) ≤ 1 by norm_num).trans
    (positiveModerateCoverConstant_one_le n j hU hV)
  refine ⟨?_, ?_, ?_⟩
  · exact inverse_power_mono hC (by unfold positiveModerateCoverConstant; nlinarith)
      hζ hζ1 (by unfold positiveModerateCoverExponent; omega)
  · exact inverse_power_mono hC (by unfold positiveModerateCoverConstant; nlinarith)
      hζ hζ1 (by unfold positiveModerateCoverExponent; omega)
  · rw [div_mul_div_comm, ← pow_add]
    exact inverse_power_mono hC (by unfold positiveModerateCoverConstant; nlinarith)
      hζ hζ1 (by unfold positiveModerateCoverExponent; omega)

end Erdos3

end

end OAI
