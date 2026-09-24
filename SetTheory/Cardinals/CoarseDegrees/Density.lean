import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Asymptotic density zero

`count S n` is the number of elements of `S` below `n`, and `S` has *density zero* when
`count S n / n → 0`.  This is the quantity `ρ_n(S)` of Section 2 of the synthesis
(`docs/coarse-degrees/research-synthesis/Turing_Degrees_Synthesis.tex`).  Everything in this file is proved.
-/

noncomputable section

open Filter Topology
open scoped Classical

namespace CoarseDegrees

/-- The number of elements of `S` below `n`. -/
def count (S : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (· ∈ S)).card

theorem count_mono {S T : Set ℕ} (h : S ⊆ T) (n : ℕ) : count S n ≤ count T n := by
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

theorem count_union_le (S T : Set ℕ) (n : ℕ) :
    count (S ∪ T) n ≤ count S n + count T n := by
  unfold count
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_union, Set.mem_union] at hx ⊢
  tauto

@[simp]
theorem count_empty (n : ℕ) : count ∅ n = 0 := by
  simp [count]

/-- `S` has asymptotic density zero: `|S ∩ [0,n)| / n → 0`. -/
def DensityZero (S : Set ℕ) : Prop :=
  Tendsto (fun n => (count S n : ℝ) / n) atTop (𝓝 0)

theorem densityZero_empty : DensityZero ∅ := by
  unfold DensityZero
  simp

theorem DensityZero.mono {S T : Set ℕ} (hT : DensityZero T) (h : S ⊆ T) : DensityZero S := by
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) hT
  exact div_le_div_of_nonneg_right (by exact_mod_cast count_mono h n) (Nat.cast_nonneg n)

/-- A finite union of density-zero sets has density zero. -/
theorem DensityZero.union {S T : Set ℕ} (hS : DensityZero S) (hT : DensityZero T) :
    DensityZero (S ∪ T) := by
  have hsum : Tendsto (fun n => (count S n : ℝ) / n + (count T n : ℝ) / n) atTop (𝓝 0) := by
    simpa using hS.add hT
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) hsum
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast count_union_le S T n) (Nat.cast_nonneg n)

end CoarseDegrees
