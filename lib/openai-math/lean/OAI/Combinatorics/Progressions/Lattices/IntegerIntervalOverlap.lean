import Mathlib.Data.Int.Interval
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem integerIco_card (c len : ℕ) :
    (Finset.Ico (c : ℤ) (c + len)).card = len := by
  simp

theorem integerIco_subset_range (c len N : ℕ) (hN : c + len ≤ N) :
    Finset.Ico (c : ℤ) (c + len) ⊆ Finset.Ico (0 : ℤ) N := by
  intro x hx
  obtain ⟨hx₀, hx₁⟩ := Finset.mem_Ico.mp hx
  exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩

theorem integerIco_intersection (c₁ l₁ c₂ l₂ N : ℕ)
    (hN₁ : c₁ + l₁ ≤ N) (hN₂ : c₂ + l₂ ≤ N)
    (hne : (Finset.Ico (c₁ : ℤ) (c₁ + l₁) ∩ Finset.Ico (c₂ : ℤ) (c₂ + l₂)).Nonempty) :
    ∃ c len : ℕ, 0 < len ∧ c + len ≤ N ∧ len ≤ l₁ ∧ len ≤ l₂ ∧
      Finset.Ico (c₁ : ℤ) (c₁ + l₁) ∩ Finset.Ico (c₂ : ℤ) (c₂ + l₂) =
        Finset.Ico (c : ℤ) (c + len) := by
  let c := max c₁ c₂
  let e := min (c₁ + l₁) (c₂ + l₂)
  obtain ⟨x, hx⟩ := hne
  obtain ⟨hx₁, hx₂⟩ := Finset.mem_inter.mp hx
  obtain ⟨hx₁₀, hx₁₁⟩ := Finset.mem_Ico.mp hx₁
  obtain ⟨hx₂₀, hx₂₁⟩ := Finset.mem_Ico.mp hx₂
  have hce : c < e := by dsimp [c, e]; omega
  have heq : c + (e - c) = e := by omega
  refine ⟨c, e - c, by omega, ?_, ?_, ?_, ?_⟩
  · dsimp [e] at heq
    omega
  · dsimp [c, e]
    omega
  · dsimp [c, e]
    omega
  · ext y
    simp only [Finset.mem_inter, Finset.mem_Ico]
    dsimp [c, e] at *
    omega

end Erdos3

end

end OAI
