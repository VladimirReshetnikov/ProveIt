/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Sampling.PhysicalGridCorrelation

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem translated_box_volume_ratio {I : Type*} [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) :
    (translatedIntegerBox lo N).card / (∏ i, H i) = ∏ i, (N i : ℝ) / H i := by
  simp only [translatedIntegerBox, card_translateSupport, card_integerBox, Nat.cast_prod, Finset.prod_div_distrib]

theorem translated_box_volume_ratio_le {I : Type*} [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) (hH : ∀ i, 0 < H i)
    {A : ℝ} (hside : ∀ i, (N i : ℝ) ≤ A * H i) :
    (translatedIntegerBox lo N).card / (∏ i, H i) ≤ A ^ Fintype.card I := by
  rw [translated_box_volume_ratio]
  calc
    _ ≤ ∏ _i : I, A := Finset.prod_le_prod₀
      (fun i _ => div_nonneg (Nat.cast_nonneg _) (hH i).le)
      (fun i _ => (div_le_iff₀ (hH i)).mpr (hside i))
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ]

theorem translated_box_pair_volume_le {I : Type*} [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) (hH : ∀ i, 0 < H i)
    {A : ℝ} (hside : ∀ i, (N i : ℝ) ≤ A * H i) :
    ((translatedIntegerBox lo N).card : ℝ) ^ 2 / (∏ i, H i ^ 2) ≤ A ^ (2 * Fintype.card I) := by
  rw [Finset.prod_pow, ← div_pow]
  have h := pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => (hH i).le)))
    (translated_box_volume_ratio_le lo N H hH hside) 2
  simpa only [← pow_mul, Nat.mul_comm] using h

theorem normalizedBoxPartitions_card_le {I : Type*} [Fintype I] [DecidableEq I]
    (N : I → ℕ) (H : I → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    {A : ℝ} (hA : 0 ≤ A) (hside : ∀ i, (N i : ℝ) ≤ A * H i) :
    (Fintype.card (∀ i, (normalizedBoxPartitions N H ρ hlarge hwhole i).Label) : ℝ) ≤
      (4 * A / ρ) ^ Fintype.card I := by
  have hi (i : I) : ((N i / ⌊ρ * H i / 2⌋₊ : ℕ) : ℝ) ≤ 4 * A / ρ := by
    obtain ⟨hpos, _, hlo, _⟩ := normalizedGridLength_bounds (N i) (H i) ρ (hlarge i) (hwhole i)
    have hp : (0 : ℝ) < ⌊ρ * H i / 2⌋₊ := by exact_mod_cast hpos
    have hq : ((N i / ⌊ρ * H i / 2⌋₊ : ℕ) : ℝ) * (⌊ρ * H i / 2⌋₊ : ℝ) ≤ N i := by
      exact_mod_cast Nat.div_mul_le_self (N i) ⌊ρ * H i / 2⌋₊
    apply ((le_div_iff₀ hp).mpr hq).trans
    apply (div_le_div_iff₀ hp hρ).mpr
    calc
      (N i : ℝ) * ρ ≤ (A * H i) * ρ := mul_le_mul_of_nonneg_right (hside i) hρ.le
      _ = (4 * A) * (ρ * H i / 4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (by positivity)
  rw [normalizedBoxPartitions_card, Nat.cast_prod]
  calc
    _ ≤ ∏ _i : I, 4 * A / ρ := Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hi i)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem normalizedBoxPartitions_coordinate_card_le {I : Type*}
    (N : I → ℕ) (H : I → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (hlarge : ∀ i, 4 ≤ rho * H i) (hwhole : ∀ i, rho * H i ≤ 2 * (N i : ℝ))
    {A : ℝ} (hA : 0 ≤ A) (hside : ∀ i, (N i : ℝ) ≤ A * H i) (i : I) :
    (Fintype.card (normalizedBoxPartitions N H rho hlarge hwhole i).Label : ℝ) ≤ 4 * A / rho := by
  have hcard : Fintype.card (normalizedBoxPartitions N H rho hlarge hwhole i).Label =
      N i / ⌊rho * H i / 2⌋₊ :=
    FiniteProgressionPartition.mergedIntervals_card (N i) ⌊rho * H i / 2⌋₊
      (normalizedGridLength_bounds (N i) (H i) rho (hlarge i) (hwhole i)).1
      (normalizedGridLength_bounds (N i) (H i) rho (hlarge i) (hwhole i)).2.1
  rw [hcard]
  obtain ⟨hpos, _, hlo, _⟩ := normalizedGridLength_bounds (N i) (H i) rho (hlarge i) (hwhole i)
  have hp : (0 : ℝ) < ⌊rho * H i / 2⌋₊ := by exact_mod_cast hpos
  have hq : ((N i / ⌊rho * H i / 2⌋₊ : ℕ) : ℝ) * (⌊rho * H i / 2⌋₊ : ℝ) ≤ N i := by
    exact_mod_cast Nat.div_mul_le_self (N i) ⌊rho * H i / 2⌋₊
  apply ((le_div_iff₀ hp).mpr hq).trans
  apply (div_le_div_iff₀ hp hrho).mpr
  calc
    (N i : ℝ) * rho ≤ (A * H i) * rho := mul_le_mul_of_nonneg_right (hside i) hrho.le
    _ = (4 * A) * (rho * H i / 4) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlo (by positivity)

theorem rounded_boundary_ratio_le {delta H c width : ℝ}
    (hdelta : 0 < delta) (hH : 0 < H) (hc : 0 < c)
    (hlarge : 1 ≤ delta * H) (hwidth : c * H ≤ width) :
    (2 * (⌈delta * H⌉₊ : ℝ) + 1) / width ≤ 5 * delta / c := by
  have hW : 0 < width := (mul_pos hc hH).trans_le hwidth
  have hceil := (Nat.ceil_lt_add_one (mul_pos hdelta hH).le).le
  have hnum : 2 * (⌈delta * H⌉₊ : ℝ) + 1 ≤ 5 * delta * H := by nlinarith
  apply (div_le_div_iff₀ hW hc).mpr
  calc
    _ ≤ (5 * delta * H) * c := mul_le_mul_of_nonneg_right hnum hc.le
    _ = (5 * delta) * (c * H) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hwidth (by positivity)

theorem normalized_physical_boundary_budget_le {I : Type*} [Fintype I] [DecidableEq I]
    (N : I → ℕ) (H width : I → ℝ) (rho : ℝ) (hrho : 0 < rho) (hH : ∀ i, 0 < H i)
    (hlarge : ∀ i, 4 ≤ rho * H i) (hwhole : ∀ i, rho * H i ≤ 2 * (N i : ℝ))
    {A c delta : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hdelta : 0 < delta)
    (hside : ∀ i, (N i : ℝ) ≤ A * H i)
    (hround : ∀ i, 1 ≤ delta * H i) (hwidth : ∀ i, c * H i ≤ width i) :
    physicalBoundaryBudget N (normalizedBoxPartitions N H rho hlarge hwhole)
      (fun i => ⌈delta * H i⌉₊) width ≤
      40 * (Fintype.card I : ℝ) * A * delta / (rho * c) := by
  unfold physicalBoundaryBudget
  calc
    _ ≤ ∑ _i : I, (2 * (4 * A / rho)) * (5 * delta / c) := by
      apply Finset.sum_le_sum
      intro i _
      have hn := normalizedBoxPartitions_coordinate_card_le N H rho hrho hlarge hwhole hA hside i
      have hw := rounded_boundary_ratio_le hdelta (hH i) hc (hround i) (hwidth i)
      have hW : 0 < width i := (mul_pos hc (hH i)).trans_le (hwidth i)
      calc
        _ = (2 * (Fintype.card (normalizedBoxPartitions N H rho hlarge hwhole i).Label : ℝ)) *
            ((2 * (⌈delta * H i⌉₊ : ℝ) + 1) / width i) := by ring
        _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hn (by norm_num)) hw (by positivity) (by positivity)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Erdos3

end

end OAI
