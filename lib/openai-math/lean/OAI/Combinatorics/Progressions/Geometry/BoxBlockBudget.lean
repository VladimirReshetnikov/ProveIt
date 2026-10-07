/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.ProgressionPartitionComposition
import OAI.Combinatorics.Progressions.Probability.ComplexPartitionMixture

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
    [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)] (i : ι) (f : X i → ℝ) :
    (𝔼 x : (∀ j, X j), f (x i)) = 𝔼 a, f a := by
  have h := Fintype.expect_equiv (Equiv.piSplitAt i X)
    (fun x => f (x i)) (fun x => f x.1) (fun _ => rfl)
  rw [h]
  simpa using Finset.expect_product' (Finset.univ : Finset (X i))
    (Finset.univ : Finset (∀ j : {j // j ≠ i}, X j)) (fun a _ => f a)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def coordinateExceptional {ι X : Type*} [Fintype ι] [Fintype X]
    (B : Finset X) : Finset (ι → X) := by
  classical
  exact Finset.univ.filter (fun x => ∃ i, x i ∈ B)

theorem not_mem_coordinateExceptional {ι X : Type*} [Fintype ι] [Fintype X]
    (B : Finset X) (x : ι → X) : x ∉ coordinateExceptional B ↔ ∀ i, x i ∉ B := by
  classical
  simp [coordinateExceptional]

theorem coordinateExceptional_density_le {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype X] [Nonempty X] (B : Finset X) :
    ((coordinateExceptional (ι := ι) B).card : ℝ) / Fintype.card (ι → X) ≤
      (Fintype.card ι : ℝ) * (B.card : ℝ) / Fintype.card X := by
  classical
  have hpoint (x : ι → X) : (if ∃ i, x i ∈ B then (1 : ℝ) else 0) ≤
      ∑ i, if x i ∈ B then (1 : ℝ) else 0 := by
    by_cases h : ∃ i, x i ∈ B
    · obtain ⟨i, hi⟩ := h
      rw [ite_eq_left ⟨i, hi⟩]
      calc
        (1 : ℝ) = if x i ∈ B then 1 else 0 := by rw [ite_eq_left hi]
        _ ≤ _ := Finset.single_le_sum
          (f := fun j : ι => if x j ∈ B then (1 : ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
    · rw [ite_eq_right h]
      exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)
  calc
    _ = 𝔼 x : ι → X, if ∃ i, x i ∈ B then (1 : ℝ) else 0 := by
      simp [coordinateExceptional, Fintype.expect_eq_sum_div_card]
      congr 1
      ext x
      simp
    _ ≤ 𝔼 x : ι → X, ∑ i, if x i ∈ B then (1 : ℝ) else 0 :=
      Finset.expect_le_expect (fun x _ => hpoint x)
    _ = ∑ i, 𝔼 x : ι → X, if x i ∈ B then (1 : ℝ) else 0 := Finset.expect_sum_comm _ _ _
    _ = ∑ _i : ι, (B.card : ℝ) / Fintype.card X := by
      congr 1
      funext i
      rw [expect_coordinate (X := fun _ : ι => X) i (fun x : X => if x ∈ B then (1 : ℝ) else 0)]
      simp [Fintype.expect_eq_sum_div_card, Finset.sum_ite_mem]
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Erdos3

end

section

namespace Erdos3.BoxProgressionPartition

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i))

def cell (x : ∀ i, Fin (N i)) : ∀ i, (P i).Label := fun i => (P i).cell (x i)

def point (a : ∀ i, (P i).Label) (j : ∀ i, Fin ((P i).length (a i))) : ∀ i, Fin (N i) :=
  fun i => (P i).point (a i) (j i)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem point_val (a : ∀ i, (P i).Label) (j : ∀ i, Fin ((P i).length (a i))) (i : ι) :
    (point P a j i).val = (P i).start (a i) + (P i).step (a i) * (j i).val :=
  (P i).point_val _ _

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem cell_point (a : ∀ i, (P i).Label) (j : ∀ i, Fin ((P i).length (a i))) :
    cell P (point P a j) = a := by
  funext i
  exact (P i).cell_point _ _

noncomputable def pointEquiv (a : ∀ i, (P i).Label) :
    (∀ i, Fin ((P i).length (a i))) ≃ ↥(partitionCell (cell P) a) :=
  (Equiv.piCongrRight (fun i => (P i).pointEquiv (a i))).trans
    (Equiv.subtypePiEquivPi.symm.trans (Equiv.subtypeEquivRight (fun x => by
      simp only [mem_partitionCell, cell, funext_iff])))

@[simp] theorem pointEquiv_val (a : ∀ i, (P i).Label) (j : ∀ i, Fin ((P i).length (a i))) :
    (pointEquiv P a j).val = point P a j := rfl

theorem card_cell (a : ∀ i, (P i).Label) :
    (partitionCell (cell P) a).card = ∏ i, (P i).length (a i) := by
  simpa only [Fintype.card_coe, Fintype.card_pi, Fintype.card_fin] using
    (Fintype.card_congr (pointEquiv P a)).symm

theorem expect_cell (a : ∀ i, (P i).Label) (f : (∀ i, Fin (N i)) → ℝ) :
    (𝔼 x ∈ partitionCell (cell P) a, f x) =
      𝔼 j : (∀ i, Fin ((P i).length (a i))), f (point P a j) := by
  have h := Fintype.expect_equiv (pointEquiv P a)
    (fun j => f (point P a j)) (fun x => f x.val) (fun _ => rfl)
  have hcoe : (𝔼 x : ↥(partitionCell (cell P) a), f x.val) =
      𝔼 x ∈ partitionCell (cell P) a, f x := by
    rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, Fintype.card_coe,
      Finset.sum_coe_sort]
  exact hcoe.symm.trans h.symm

end Erdos3.BoxProgressionPartition

end

section

namespace Erdos3.BoxProgressionPartition

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i))

noncomputable def normalizedPoint (x : ∀ i, Fin (N i)) : ι → ℝ :=
  fun i => (x i).val / (N i : ℝ)

noncomputable def normalizedStart (a : ∀ i, (P i).Label) : ι → ℝ :=
  fun i => ((P i).start (a i) : ℝ) / N i

omit [DecidableEq ι] in
theorem normalizedPoint_dist_start (hN : ∀ i, 0 < N i) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (a : ∀ i, (P i).Label)
    (hwidth : ∀ i, ((P i).step (a i) : ℝ) * (P i).length (a i) ≤ ρ * N i)
    (j : ∀ i, Fin ((P i).length (a i))) :
    dist (normalizedPoint (point P a j)) (normalizedStart P a) ≤ ρ := by
  apply (dist_pi_le_iff hρ).mpr
  intro i
  have hNi : (0 : ℝ) < N i := by exact_mod_cast hN i
  have hj : ((j i).val : ℝ) ≤ (P i).length (a i) := by exact_mod_cast (j i).isLt.le
  rw [Real.dist_eq]
  change |((point P a j i).val : ℝ) / N i - ((P i).start (a i) : ℝ) / N i| ≤ ρ
  rw [point_val, Nat.cast_add, Nat.cast_mul, ← sub_div, add_sub_cancel_left]
  rw [abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ hNi).mpr
  exact (mul_le_mul_of_nonneg_left hj (Nat.cast_nonneg _)).trans (hwidth i)

omit [Fintype ι] [DecidableEq ι] in
theorem point_residue (a : ∀ i, (P i).Label) (j : ∀ i, Fin ((P i).length (a i)))
    (q : ℕ) (hstep : ∀ i, q ∣ (P i).step (a i)) (i : ι) :
    (point P a j i).val % q = (P i).start (a i) % q := by
  rw [point_val, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd (hstep i)]
  simp

omit [DecidableEq ι] in
theorem blocks_normalizedPoint_dist_start (q : ℕ) (H : ι → ℕ)
    (hq : 0 < q) (hH : ∀ i, 0 < H i) (hN : ∀ i, 0 < N i) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hfit : ∀ i, (q : ℝ) * H i ≤ ρ * N i)
    (a : ∀ i, (FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)).Label)
    (j : ∀ i, Fin ((FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)).length (a i))) :
    dist (normalizedPoint (point (fun i => FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)) a j))
      (normalizedStart (fun i => FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)) a) ≤ ρ := by
  apply normalizedPoint_dist_start _ hN hρ a _ j
  intro i
  have hlen : ((FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)).length (a i) : ℝ) ≤ H i := by
    exact_mod_cast truncatedProgressionLength_le (N i) (progressionBlockStart (a i)) q (H i)
  exact (mul_le_mul_of_nonneg_left hlen (Nat.cast_nonneg q)).trans (hfit i)

end Erdos3.BoxProgressionPartition

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_partition_cell_norm_mean_le {X K : Type*} [Fintype X] [Nonempty X]
    [Fintype K] (cell : X → K) (f : X → ℂ) :
    ∃ k, (partitionCell cell k).Nonempty ∧
      ‖𝔼 x, f x‖ ≤ ‖𝔼 x ∈ partitionCell cell k, f x‖ := by
  classical
  obtain ⟨x, _, hx⟩ := Finset.univ.exists_max_image
    (fun x : X => ‖𝔼 y ∈ partitionCell cell (cell x), f y‖) Finset.univ_nonempty
  have hmax (k : K) : ‖𝔼 y ∈ partitionCell cell k, f y‖ ≤
      ‖𝔼 y ∈ partitionCell cell (cell x), f y‖ := by
    by_cases hk : (partitionCell cell k).Nonempty
    · obtain ⟨y, hy⟩ := hk
      have h := hx y (Finset.mem_univ _)
      simpa only [(mem_partitionCell cell k y).mp hy] using h
    · rw [Finset.not_nonempty_iff_eq_empty.mp hk]
      simp only [Finset.expect_empty, norm_zero]
      exact norm_nonneg (𝔼 y ∈ partitionCell cell (cell x), f y)
  refine ⟨cell x, ⟨x, (mem_partitionCell cell _ _).mpr rfl⟩, ?_⟩
  have hcard : (Fintype.card X : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := X))
  rw [complex_expect_partition_count_weights cell f, card_partitionCell_sum]
  calc
    _ ≤ ∑ k, ‖(((partitionCell cell k).card : ℝ) / Fintype.card X : ℂ) *
        (𝔼 y ∈ partitionCell cell k, f y)‖ := norm_sum_le _ _
    _ ≤ ∑ k, ((partitionCell cell k).card : ℝ) / Fintype.card X *
        ‖𝔼 y ∈ partitionCell cell (cell x), f y‖ := by
      apply Finset.sum_le_sum
      intro k _
      simp only [norm_mul, norm_div, Complex.norm_real, norm_natCast]
      exact mul_le_mul_of_nonneg_left (hmax k) (by positivity)
    _ = ‖𝔼 y ∈ partitionCell cell (cell x), f y‖ := by
      rw [← Finset.sum_mul, ← Finset.sum_div, card_partitionCell_sum, div_self hcard,
        one_mul]

namespace BoxProgressionPartition

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i))

theorem expect_cell_complex (a : ∀ i, (P i).Label) (f : (∀ i, Fin (N i)) → ℂ) :
    (𝔼 x ∈ partitionCell (cell P) a, f x) =
      𝔼 j : (∀ i, Fin ((P i).length (a i))), f (point P a j) := by
  have h := Fintype.expect_equiv (pointEquiv P a)
    (fun j => f (point P a j)) (fun x => f x.val) (fun _ => rfl)
  have hcoe : (𝔼 x : ↥(partitionCell (cell P) a), f x.val) =
      𝔼 x ∈ partitionCell (cell P) a, f x := by
    rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, Fintype.card_coe,
      Finset.sum_coe_sort]
  exact hcoe.symm.trans h.symm

theorem exists_positive_box_norm_mean_le (hN : ∀ i, 0 < N i) (f : (ι → ℕ) → ℂ) :
    ∃ a : ∀ i, (P i).Label, (∀ i, 0 < (P i).length (a i)) ∧
      ‖𝔼 x : (∀ i, Fin (N i)), f (fun i => (x i).val)‖ ≤
        ‖𝔼 j : (∀ i, Fin ((P i).length (a i))),
          f (fun i => (P i).start (a i) + (P i).step (a i) * (j i).val)‖ := by
  classical
  let : Nonempty (∀ i, Fin (N i)) := ⟨fun i => ⟨0, hN i⟩⟩
  obtain ⟨a, ha, hmean⟩ := exists_partition_cell_norm_mean_le (cell P)
    (fun x => f (fun i => (x i).val))
  refine ⟨a, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := ha
    let j := (pointEquiv P a).symm ⟨x, hx⟩
    exact fun i => Nat.zero_lt_of_lt (j i).isLt
  · rw [expect_cell_complex] at hmean
    simpa only [point_val] using hmean

theorem exists_box_norm_mean_le (hN : ∀ i, 0 < N i) (f : (ι → ℕ) → ℂ) :
    ∃ a : ∀ i, (P i).Label,
      ‖𝔼 x : (∀ i, Fin (N i)), f (fun i => (x i).val)‖ ≤
        ‖𝔼 j : (∀ i, Fin ((P i).length (a i))),
          f (fun i => (P i).start (a i) + (P i).step (a i) * (j i).val)‖ := by
  obtain ⟨a, _, ha⟩ := exists_positive_box_norm_mean_le P hN f
  exact ⟨a, ha⟩

end BoxProgressionPartition
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem short_progression_cell_mass_le {N : ℕ} (P : FiniteProgressionPartition N)
    {L : ℝ} (hL : 0 ≤ L) :
    (𝔼 n : Fin N, if ((P.length (P.cell n) : ℕ) : ℝ) < L then 1 else 0) ≤
      (Fintype.card P.Label : ℝ) * L / N := by
  classical
  let b : Fin N → ℝ := fun n => if (P.length (P.cell n) : ℝ) < L then 1 else 0
  have hcell (a : P.Label) : (∑ n ∈ partitionCell P.cell a, b n) ≤ L := by
    have heq : (∑ n ∈ partitionCell P.cell a, b n) =
        if (P.length a : ℝ) < L then (P.length a : ℝ) else 0 := by
      calc
        _ = ∑ _n ∈ partitionCell P.cell a, if (P.length a : ℝ) < L then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          simp only [b, (mem_partitionCell _ _ _).mp hn]
        _ = _ := by split_ifs <;> simp [P.card_cell]
    rw [heq]
    split_ifs with h
    · exact h.le
    · exact hL
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset P.Label)) => hcell a)
  rw [sum_partitionCell] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg N)

theorem short_box_side_mass_le {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i)) (hN : ∀ i, 0 < N i)
    (L : ι → ℝ) (hL : ∀ i, 0 ≤ L i) :
    (𝔼 x : (∀ i, Fin (N i)), if (∀ i, L i ≤ ((P i).length ((P i).cell (x i)) : ℝ)) then 0 else 1) ≤
      ∑ i, (Fintype.card (P i).Label : ℝ) * L i / N i := by
  classical
  let : ∀ i, Nonempty (Fin (N i)) := fun i => ⟨⟨0, hN i⟩⟩
  have hpoint (x : ∀ i, Fin (N i)) :
      (if (∀ i, L i ≤ ((P i).length ((P i).cell (x i)) : ℝ)) then (0 : ℝ) else 1) ≤
        ∑ i, if ((P i).length ((P i).cell (x i)) : ℝ) < L i then 1 else 0 := by
    split_ifs with h
    · exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
    · push Not at h
      obtain ⟨i, hi⟩ := h
      have hs := Finset.single_le_sum (s := Finset.univ)
        (f := fun j => if ((P j).length ((P j).cell (x j)) : ℝ) < L j then (1 : ℝ) else 0)
        (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
      simpa only [hi, ite_true] using hs
  apply (Finset.expect_le_expect (fun x _ => hpoint x)).trans
  rw [Finset.expect_sum_comm]
  apply Finset.sum_le_sum
  intro i _
  rw [expect_coordinate (X := fun j => Fin (N j)) i
    (fun n : Fin (N i) => if ((P i).length ((P i).cell n) : ℝ) < L i then (1 : ℝ) else 0)]
  exact short_progression_cell_mass_le (P i) (hL i)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem progressionBlock_short_side_bound {N q H : ℕ} (hN : 0 < N) (hH : 0 < H)
    (hfit : q * H ≤ N) {L : ℝ} (hL : 0 ≤ L) :
    (Fintype.card (Fin q × Fin (N / q / H + 1)) : ℝ) * L / N ≤ 2 * L / H := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  apply (div_le_div_iff₀ hNr hHr).mpr
  have hc : (Fintype.card (Fin q × Fin (N / q / H + 1)) : ℝ) * H ≤ 2 * N := by
    exact_mod_cast progressionBlock_label_count_mul_le_twice hfit
  nlinarith [mul_le_mul_of_nonneg_right hc hL]

theorem boxBlock_short_side_budget {ι : Type*} [Fintype ι] (N H : ι → ℕ) (q : ℕ)
    (hN : ∀ i, 0 < N i) (hH : ∀ i, 0 < H i) (hfit : ∀ i, q * H i ≤ N i)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    (∑ i, (Fintype.card (Fin q × Fin (N i / q / H i + 1)) : ℝ) *
      (θ * H i / (2 * (Fintype.card ι + 1))) / N i) ≤ θ := by
  have hn : (0 : ℝ) < Fintype.card ι + 1 := by positivity
  calc
    _ ≤ ∑ i, 2 * (θ * H i / (2 * (Fintype.card ι + 1))) / H i := by
      apply Finset.sum_le_sum
      intro i _
      exact progressionBlock_short_side_bound (hN i) (hH i) (hfit i) (by positivity)
    _ = ∑ _i : ι, θ / (Fintype.card ι + 1) := by
      apply Finset.sum_congr rfl
      intro i _
      have hHi : (H i : ℝ) ≠ 0 := by exact_mod_cast (hH i).ne'
      field_simp
    _ ≤ θ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hn).mpr
      nlinarith

theorem exists_box_block_mesh {ι : Type*} (N : ι → ℕ) (q : ℕ) (hq : 0 < q)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hlarge : ∀ i, 2 * (q : ℝ) ≤ ρ * N i) :
    ∃ H : ι → ℕ, (∀ i, 0 < H i) ∧ (∀ i, q * H i ≤ N i) ∧
      (∀ i, (q : ℝ) * H i ≤ ρ * N i) ∧
      (∀ i, ρ * N i / (2 * q) ≤ (H i : ℝ)) := by
  let H : ι → ℕ := fun i => ⌊ρ * N i / q⌋₊
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hx (i) : 2 ≤ ρ * N i / q := (le_div_iff₀ hqr).mpr (hlarge i)
  have hlo (i) : ρ * N i / q - 1 < (H i : ℝ) := Nat.sub_one_lt_floor _
  have hhi (i) : (H i : ℝ) ≤ ρ * N i / q := Nat.floor_le (by positivity)
  have hH (i) : 0 < H i := by
    have h : (0 : ℝ) < H i := by linarith [hlo i, hx i]
    exact_mod_cast h
  have hwidth (i) : (q : ℝ) * H i ≤ ρ * N i := by
    have h := (le_div_iff₀ hqr).mp (hhi i)
    simpa only [mul_comm] using h
  refine ⟨H, hH, ?_, hwidth, ?_⟩
  · intro i
    have h := (hwidth i).trans (mul_le_of_le_one_left (Nat.cast_nonneg (N i)) hρ1)
    exact_mod_cast h
  · intro i
    have heq : ρ * N i / (2 * q) = (ρ * N i / q) / 2 := by ring
    rw [heq]
    linarith [hlo i, hx i]

end Erdos3

end

end OAI
