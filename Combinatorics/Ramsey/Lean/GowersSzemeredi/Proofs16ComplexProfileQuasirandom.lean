import GowersSzemeredi.Proofs16OneSidedQuasirandom
import Mathlib.Analysis.Complex.Basic

/-! Quasirandomness from a complex degree profile.

Claim 34 (`bohr_card_factor_of_split_mixed`) gives, for typical `y`,
`deg y ≈ W·|X|` and `codeg(y,y′) ≈ W²·|X|` with a complex weight `W`.
[49] treats the corresponding `δᵢ` as a real number in `[0,1]`. Here the
real density is read off a typical vertex `y*`: `δ = deg y*/|X|`. Then:

* `|W − δ|·|X| ≤ E` and `‖W‖ ≤ 1 + E/|X|`;
* typical degrees are within `2E` of `δ|X|`;
* typical codegrees are within `E(3 + E/|X|) ≤ 4E` of `δ²|X|` when
  `E ≤ |X|`.

So `boxSum (G − δ) ≤ 3(4E/|X| + η)|X|²|Y|²`
(`boxSum_le_of_complex_profile`), where `η` bounds the atypical fractions.
No bound on `W` is assumed. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Finset

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]

/-- **Quasirandomness from a complex degree profile.** -/
theorem boxSum_le_of_complex_profile {G : X → Y → ℝ} (hG0 : ∀ x y, 0 ≤ G x y)
    (hG1 : ∀ x y, G x y ≤ 1) (hX : 0 < Fintype.card X) {W : ℂ} {E η : ℝ} (hE0 : 0 ≤ E)
    (hEX : E ≤ Fintype.card X) (Ybad : Finset Y)
    (hYbad : (Ybad.card : ℝ) ≤ η * Fintype.card Y) {y₀ : Y} (hy₀ : y₀ ∉ Ybad)
    (hdeg : ∀ y ∉ Ybad, ‖((∑ x, G x y : ℝ) : ℂ) - W * Fintype.card X‖ ≤ E)
    (Pbad : Finset (Y × Y)) (hPbad : (Pbad.card : ℝ) ≤ η * (Fintype.card Y : ℝ) ^ 2)
    (hcodeg : ∀ y y', (y, y') ∉ Pbad →
      ‖((∑ x, G x y * G x y' : ℝ) : ℂ) - W ^ 2 * Fintype.card X‖ ≤ E) :
    let δ := (∑ x, G x y₀) / Fintype.card X
    0 ≤ δ ∧ δ ≤ 1 ∧
      boxSum (fun x y => G x y - δ) ≤
        3 * (4 * E / Fintype.card X + η) * (Fintype.card X : ℝ) ^ 2 *
          (Fintype.card Y : ℝ) ^ 2 := by
  intro δ
  obtain ⟨NX, hNX⟩ : ∃ NX : ℝ, NX = Fintype.card X := ⟨_, rfl⟩
  have hNX0 : 0 < NX := by rw [hNX]; exact_mod_cast hX
  have hcastX : ((Fintype.card X : Nat) : ℂ) = ((NX : ℝ) : ℂ) := by rw [hNX]; push_cast; rfl
  have hdeg0 : 0 ≤ ∑ x, G x y₀ := Finset.sum_nonneg fun x _ => hG0 x y₀
  have hdeg1 : ∑ x, G x y₀ ≤ NX := by
    rw [hNX]
    calc ∑ x, G x y₀ ≤ ∑ _x : X, (1 : ℝ) := Finset.sum_le_sum fun x _ => hG1 x y₀
      _ = _ := by simp
  have hδ : δ * NX = ∑ x, G x y₀ := by
    simp only [δ]; rw [← hNX]; field_simp
  have hδ0 : 0 ≤ δ := by simp only [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    simp only [δ]; rw [← hNX, div_le_one hNX0]; exact hdeg1
  refine ⟨hδ0, hδ1, ?_⟩
  -- `|W − δ|·|X| ≤ E`
  have hWδ : ‖W - (δ : ℂ)‖ * NX ≤ E := by
    have h := hdeg y₀ hy₀
    rw [hcastX] at h
    have heq : ((∑ x, G x y₀ : ℝ) : ℂ) - W * NX = -((W - (δ : ℂ)) * NX) := by
      rw [← hδ]; push_cast; ring
    rw [heq, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNX0] at h
    exact h
  have hWδ' : ‖W - (δ : ℂ)‖ ≤ E / NX := by rw [le_div_iff₀ hNX0]; exact hWδ
  have hW : ‖W‖ ≤ 1 + E / NX := by
    calc ‖W‖ = ‖(W - (δ : ℂ)) + (δ : ℂ)‖ := by ring_nf
      _ ≤ ‖W - (δ : ℂ)‖ + ‖(δ : ℂ)‖ := norm_add_le _ _
      _ ≤ E / NX + 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ0]
          linarith
      _ = _ := by ring
  have hENX : E / NX ≤ 1 := by rw [div_le_one hNX0, hNX]; exact hEX
  -- typical degrees
  have hdeg' : ∀ y ∉ Ybad, |∑ x, G x y - δ * Fintype.card X| ≤
      (4 * E / Fintype.card X) * Fintype.card X := by
    intro y hy
    rw [← hNX]
    have h := hdeg y hy
    rw [hcastX] at h
    have hcast : ((∑ x, G x y - δ * NX : ℝ) : ℂ) =
        (((∑ x, G x y : ℝ) : ℂ) - W * NX) + (W - (δ : ℂ)) * NX := by push_cast; ring
    have hn : |∑ x, G x y - δ * NX| ≤ 2 * E := by
      rw [← Real.norm_eq_abs, ← Complex.norm_real, hcast]
      calc _ ≤ ‖((∑ x, G x y : ℝ) : ℂ) - W * NX‖ + ‖(W - (δ : ℂ)) * NX‖ := norm_add_le _ _
        _ ≤ E + E := by
            apply add_le_add h
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNX0]
            exact hWδ
        _ = 2 * E := by ring
    have : 4 * E / NX * NX = 4 * E := by field_simp
    rw [this]; linarith
  -- typical codegrees
  have hcodeg' : ∀ y y', (y, y') ∉ Pbad →
      |∑ x, G x y * G x y' - δ ^ 2 * Fintype.card X| ≤
        (4 * E / Fintype.card X) * Fintype.card X := by
    intro y y' hp
    rw [← hNX]
    have h := hcodeg y y' hp
    rw [hcastX] at h
    have hcast : ((∑ x, G x y * G x y' - δ ^ 2 * NX : ℝ) : ℂ) =
        (((∑ x, G x y * G x y' : ℝ) : ℂ) - W ^ 2 * NX) +
          (W - (δ : ℂ)) * (W + (δ : ℂ)) * NX := by push_cast; ring
    have hsum : ‖W + (δ : ℂ)‖ ≤ 2 + E / NX := by
      calc ‖W + (δ : ℂ)‖ ≤ ‖W‖ + ‖(δ : ℂ)‖ := norm_add_le _ _
        _ ≤ (1 + E / NX) + 1 := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ0]
            linarith
        _ = _ := by ring
    have hprod : ‖(W - (δ : ℂ)) * (W + (δ : ℂ)) * NX‖ ≤ E * (2 + E / NX) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNX0]
      calc ‖W - (δ : ℂ)‖ * ‖W + (δ : ℂ)‖ * NX = (‖W - (δ : ℂ)‖ * NX) * ‖W + (δ : ℂ)‖ := by
            ring
        _ ≤ E * (2 + E / NX) :=
            mul_le_mul hWδ hsum (norm_nonneg _) hE0
    have hn : |∑ x, G x y * G x y' - δ ^ 2 * NX| ≤ 4 * E := by
      rw [← Real.norm_eq_abs, ← Complex.norm_real, hcast]
      calc _ ≤ ‖((∑ x, G x y * G x y' : ℝ) : ℂ) - W ^ 2 * NX‖ +
            ‖(W - (δ : ℂ)) * (W + (δ : ℂ)) * NX‖ := norm_add_le _ _
        _ ≤ E + E * (2 + E / NX) := add_le_add h hprod
        _ ≤ 4 * E := by nlinarith
    have : 4 * E / NX * NX = 4 * E := by field_simp
    rw [this]; exact hn
  have he : 0 ≤ 4 * E / Fintype.card X := by positivity
  exact boxSum_le_of_typical_codegrees hG0 hG1 hδ0 hδ1 he Ybad hYbad hdeg' Pbad hPbad hcodeg'

end LeanProofs.GowersSzemeredi
