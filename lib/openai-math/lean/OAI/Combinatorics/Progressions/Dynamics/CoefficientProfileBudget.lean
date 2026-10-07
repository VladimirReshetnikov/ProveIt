import Mathlib

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def coefficientProfileCenter {J : Type*} (P : Finset J) (γ : ℝ) (j : J) : ℝ := by
  classical
  exact if j ∈ P then 3 * γ / 2 else 0

noncomputable def coefficientProfileWidth {J : Type*} (P : Finset J) (j₀ : J)
    (ρ γ ε : ℝ) (j : J) : ℝ := by
  classical
  exact if j = j₀ then ρ else if j ∈ P then γ / 2 else ε

theorem coefficientProfileWidth_pos {J : Type*} (P : Finset J) (j₀ : J)
    {ρ γ ε : ℝ} (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε) (j : J) :
    0 < coefficientProfileWidth P j₀ ρ γ ε j := by
  classical
  unfold coefficientProfileWidth
  split_ifs <;> positivity

theorem coefficientProfile_budget {J : Type*} [Fintype J] (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) {ρ γ ε : ℝ} (hγ : 0 ≤ γ) (hε : 0 ≤ ε) :
    (∑ j, (|coefficientProfileCenter P γ j| + coefficientProfileWidth P j₀ ρ γ ε j)) ≤
      ρ + 2 * γ * P.card + ε * Fintype.card J := by
  classical
  have hpoint (j : J) : |coefficientProfileCenter P γ j| + coefficientProfileWidth P j₀ ρ γ ε j ≤
      (if j = j₀ then ρ else 0) + (if j ∈ P then 2 * γ else 0) + ε := by
    by_cases hj : j = j₀
    · subst j
      simp [coefficientProfileCenter, coefficientProfileWidth, hj₀, hε]
    · by_cases hP : j ∈ P
      · have hpos : 0 ≤ 3 * γ / 2 := by positivity
        simp only [coefficientProfileCenter, coefficientProfileWidth, hj, hP,
          ↓reduceIte, abs_of_nonneg hpos]
        linarith
      · simp [coefficientProfileCenter, coefficientProfileWidth, hj, hP]
  calc
    _ ≤ ∑ j, ((if j = j₀ then ρ else 0) + (if j ∈ P then 2 * γ else 0) + ε) :=
      Finset.sum_le_sum (fun j _ => hpoint j)
    _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_ite_mem]; ring

noncomputable def principalProfileSize (R : ℝ) (b : ℕ) : ℝ := R / (8 * ((b : ℝ) + 1))

noncomputable def tailProfileSize (R σ : ℝ) (m : ℕ) : ℝ := σ * R / (4 * ((m : ℝ) + 1))

theorem principalProfileSize_pos {R : ℝ} (hR : 0 < R) (b : ℕ) : 0 < principalProfileSize R b := by
  unfold principalProfileSize
  positivity

theorem tailProfileSize_pos {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (m : ℕ) :
    0 < tailProfileSize R σ m := by
  unfold tailProfileSize
  positivity

theorem allocatedProfile_budget {R σ : ℝ} (hR : 0 ≤ R) (hσ1 : σ ≤ 1) (b m : ℕ) :
    R / 4 + 2 * principalProfileSize R b * b + tailProfileSize R σ m * m ≤ 3 * R / 4 := by
  have hb : (b : ℝ) / ((b : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  have hm : (m : ℝ) / ((m : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  have hp : 2 * principalProfileSize R b * b ≤ R / 4 := by
    calc
      _ = (R / 4) * ((b : ℝ) / ((b : ℝ) + 1)) := by
        unfold principalProfileSize
        field_simp; ring
      _ ≤ (R / 4) * 1 := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := mul_one _
  have ht : tailProfileSize R σ m * m ≤ R / 4 := by
    calc
      _ = σ * (R / 4) * ((m : ℝ) / ((m : ℝ) + 1)) := by
        unfold tailProfileSize
        field_simp
      _ ≤ 1 * (R / 4) * 1 := by gcongr
      _ = _ := by ring
  linarith

end Erdos3

end

end OAI
