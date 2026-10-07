/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Geometry.PhysicalBoxPartition

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem roundedPartitionLength_bounds (N : ℕ) (ρ : ℝ)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1) (hlarge : 2 ≤ ρ * (N : ℝ)) :
    0 < ⌊ρ * (N : ℝ)⌋₊ ∧ ⌊ρ * (N : ℝ)⌋₊ ≤ N ∧
      ρ * (N : ℝ) / 2 ≤ (⌊ρ * (N : ℝ)⌋₊ : ℝ) ∧
      (⌊ρ * (N : ℝ)⌋₊ : ℝ) ≤ ρ * (N : ℝ) ∧
      ((N / ⌊ρ * (N : ℝ)⌋₊ : ℕ) : ℝ) ≤ 2 / ρ := by
  let H := ⌊ρ * (N : ℝ)⌋₊
  have hH : 0 < H := Nat.floor_pos.mpr (by linarith)
  have hHN : H ≤ N := Nat.floor_le_of_le (by
    nlinarith [Nat.cast_nonneg (α := ℝ) N])
  have hupper : (H : ℝ) ≤ ρ * (N : ℝ) := Nat.floor_le (by linarith)
  have hnext : ρ * (N : ℝ) < (H : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlower : ρ * (N : ℝ) / 2 ≤ (H : ℝ) := by linarith
  have hHreal : 0 < (H : ℝ) := by exact_mod_cast hH
  have hquot : ((N / H : ℕ) : ℝ) * (H : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self N H
  have hcount : ((N / H : ℕ) : ℝ) ≤ 2 / ρ := by
    calc
      ((N / H : ℕ) : ℝ) ≤ (N : ℝ) / (H : ℝ) :=
        (le_div_iff₀ hHreal).mpr hquot
      _ ≤ 2 / ρ := (div_le_div_iff₀ hHreal hρ).mpr (by nlinarith)
  exact ⟨hH, hHN, hlower, hupper, hcount⟩

theorem comparableBoxPartitions_relative_length {I : Type*}
    (N H : I → ℕ) (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i)
    (ρ : ℝ) (hlower : ∀ i, ρ * (N i : ℝ) / 2 ≤ (H i : ℝ))
    (hupper : ∀ i, (H i : ℝ) ≤ ρ * (N i : ℝ))
    (i : I) (k : (comparableBoxPartitions N H hH hHN i).Label) :
    ρ * (N i : ℝ) / 2 ≤ ((comparableBoxPartitions N H hH hHN i).length k : ℝ) ∧
      ((comparableBoxPartitions N H hH hHN i).length k : ℝ) < 2 * ρ * (N i : ℝ) := by
  obtain ⟨hlo, hhi⟩ := comparableBoxPartitions_length N H hH hHN i k
  have hlo' : (H i : ℝ) ≤ ((comparableBoxPartitions N H hH hHN i).length k : ℝ) := by
    exact_mod_cast hlo
  have hhi' : ((comparableBoxPartitions N H hH hHN i).length k : ℝ) < 2 * (H i : ℝ) := by
    exact_mod_cast hhi
  constructor
  · exact (hlower i).trans hlo'
  · nlinarith [hupper i]

theorem comparableBoxPartitions_relative_card {I : Type*} [Fintype I] [DecidableEq I]
    (N H : I → ℕ) (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i)
    (ρ : ℝ) (hcount : ∀ i, ((N i / H i : ℕ) : ℝ) ≤ 2 / ρ) :
    (Fintype.card (∀ i, (comparableBoxPartitions N H hH hHN i).Label) : ℝ) ≤
      (2 / ρ) ^ Fintype.card I := by
  rw [comparableBoxPartitions_card, Nat.cast_prod]
  calc
    (∏ i, ((N i / H i : ℕ) : ℝ)) ≤ ∏ _i : I, 2 / ρ :=
      Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hcount i)
    _ = (2 / ρ) ^ Fintype.card I := by
      simp only [Finset.prod_const, Finset.card_univ]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_descent_partition_lengths {I : Type*} [Fintype I]
    (N : I → ℕ) (M : ℕ) (A : I → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hsize : ∀ i, (N i : ℝ) ≤ 2 * (M : ℝ) * A i)
    (hlarge : ∀ i, 8 ≤ δ * (N i : ℝ))
    (R : I → ℝ) (hR : ∀ i, 0 ≤ R i) (ε : ℝ)
    (hcount : (∑ i, R i / (N i : ℝ)) ≤ δ * ε / 8) :
    ∃ H : I → ℕ, (∀ i, 0 < H i) ∧ (∀ i, H i ≤ N i) ∧
      (∀ i, δ * (N i : ℝ) / 8 ≤ (H i : ℝ)) ∧
      (∀ i, (H i : ℝ) ≤ δ * (N i : ℝ) / 4) ∧
      (∀ i, 2 * (H i : ℝ) ≤ (M : ℝ) * A i * δ) ∧
      (∑ i, R i / (H i : ℝ)) ≤ ε := by
  let H : I → ℕ := fun i => ⌊(δ / 4) * (N i : ℝ)⌋₊
  have hround (i : I) := roundedPartitionLength_bounds (N i) (δ / 4)
    (by positivity) (by linarith) (by nlinarith [hlarge i])
  have hH : ∀ i, 0 < H i := fun i => (hround i).1
  have hHN : ∀ i, H i ≤ N i := fun i => (hround i).2.1
  have hlo : ∀ i, δ * (N i : ℝ) / 8 ≤ (H i : ℝ) := by
    intro i
    have h := (hround i).2.2.1
    change (δ / 4) * (N i : ℝ) / 2 ≤ (H i : ℝ) at h
    nlinarith
  have hhi : ∀ i, (H i : ℝ) ≤ δ * (N i : ℝ) / 4 := by
    intro i
    have h := (hround i).2.2.2.1
    change (H i : ℝ) ≤ (δ / 4) * (N i : ℝ) at h
    nlinarith
  have hfreeze : ∀ i, 2 * (H i : ℝ) ≤ (M : ℝ) * A i * δ := by
    intro i
    calc
      2 * (H i : ℝ) ≤ δ * (N i : ℝ) / 2 := by nlinarith [hhi i]
      _ ≤ δ * (2 * (M : ℝ) * A i) / 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hsize i) hδ.le) (by norm_num)
      _ = _ := by ring
  have hratio (i : I) : R i / (H i : ℝ) ≤ (8 / δ) * (R i / (N i : ℝ)) := by
    have hN : 0 < (N i : ℝ) := by nlinarith [hlarge i, Nat.cast_nonneg (α := ℝ) (N i)]
    calc
      R i / (H i : ℝ) ≤ R i / (δ * (N i : ℝ) / 8) :=
        div_le_div_of_nonneg_left (hR i) (by positivity) (hlo i)
      _ = _ := by field_simp
  refine ⟨H, hH, hHN, hlo, hhi, hfreeze, ?_⟩
  calc
    (∑ i, R i / (H i : ℝ)) ≤ ∑ i, (8 / δ) * (R i / (N i : ℝ)) :=
      Finset.sum_le_sum (fun i _ => hratio i)
    _ = (8 / δ) * ∑ i, R i / (N i : ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ (8 / δ) * (δ * ε / 8) := mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = ε := by field_simp

end Erdos3

end

end OAI
