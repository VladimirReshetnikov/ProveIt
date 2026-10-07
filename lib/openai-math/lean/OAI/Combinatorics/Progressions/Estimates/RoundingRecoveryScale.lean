import Mathlib

namespace OAI

section

namespace Erdos3

theorem exists_rounding_modulus (l : ℕ) (hl : 0 < l) {ε : ℝ}
    (hε : 0 < ε) (hsmall : 2 * (l : ℝ) * ε ≤ 1) :
    ∃ M : ℕ, 0 < M ∧ 1 / (2 * (l : ℝ) * ε) ≤ (M : ℝ) ∧
      (M : ℝ) * l * ε ≤ 1 := by
  let u : ℝ := (l : ℝ) * ε
  have hu : 0 < u := mul_pos (by exact_mod_cast hl) hε
  have hu2 : 2 * u ≤ 1 := by simpa only [u, mul_assoc] using hsmall
  have hx : 2 ≤ 1 / u := (le_div_iff₀ hu).mpr hu2
  let M := ⌊1 / u⌋₊
  have hM : 0 < M := Nat.floor_pos.mpr (by linarith)
  have hfloor : (M : ℝ) ≤ 1 / u := Nat.floor_le (by positivity)
  have hlt : 1 / u < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨M, hM, ?_, ?_⟩
  · have heq : 1 / (2 * (l : ℝ) * ε) = (1 / u) / 2 := by
      dsimp only [u]
      ring
    rw [heq]
    linarith
  · have h := (le_div_iff₀ hu).mp hfloor
    simpa only [u, mul_assoc] using h

end Erdos3

end

section

namespace Erdos3

theorem rounding_recovery_error_le (M l : ℕ) [NeZero M] (hl : 0 < l)
    {ε : ℝ} (hε : 0 < ε) (hM : 1 / (2 * (l : ℝ) * ε) ≤ (M : ℝ)) :
    1 / ((M : ℝ) * l) ≤ 2 * ε := by
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hMR : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hmul := (div_le_iff₀ (by positivity : 0 < 2 * (l : ℝ) * ε)).mp hM
  apply (div_le_iff₀ (mul_pos hMR hlR)).mpr
  nlinarith

theorem exists_rounding_modulus_with_recovery (l : ℕ) (hl : 0 < l) {ε : ℝ}
    (hε : 0 < ε) (hsmall : 2 * (l : ℝ) * ε ≤ 1) :
    ∃ M : ℕ, 0 < M ∧ (M : ℝ) * l * ε ≤ 1 ∧ 1 / ((M : ℝ) * l) ≤ 2 * ε := by
  obtain ⟨M, hM, hlower, hupper⟩ := exists_rounding_modulus l hl hε hsmall
  let _ : NeZero M := ⟨hM.ne'⟩
  exact ⟨M, hM, hupper, rounding_recovery_error_le M l hl hε hlower⟩

end Erdos3

end

end OAI
