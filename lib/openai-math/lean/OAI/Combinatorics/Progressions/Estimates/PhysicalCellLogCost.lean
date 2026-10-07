import OAI.Combinatorics.Progressions.Sampling.PhysicalGridCorrelation

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*}

theorem physicalBoxCell_subbox (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (c : ∀ i, (P i).Label) :
    PhysicalSubbox lo N (fun i => intervalCellLower (lo i) (P i) (c i)) (fun i => (P i).length (c i)) := by
  intro i
  have hend : ((P i).start (c i) : ℤ) + (P i).length (c i) ≤ N i := by
    exact_mod_cast (P i).end_le_of_step_one (hstep i) (c i) (hpos i (c i))
  have hstart : (0 : ℤ) ≤ (P i).start (c i) := Int.natCast_nonneg _
  dsimp only [intervalCellLower]
  constructor <;> omega

theorem physicalBoxCell_log_cost (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (c : ∀ i, (P i).Label) (budget : ℝ)
    (hwidth : ∀ i, Real.exp (-budget) * (N i : ℝ) ≤ ((P i).length (c i) : ℝ)) :
    ResidueSliceLogCostLE N (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => (P i).length (c i)) 1 (fun _ => 0) budget := by
  intro i
  simpa only [Nat.cast_one, residueIndexLength_one_zero] using hwidth i

theorem normalized_physical_cell_log_cost (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ)
    (rho A budget : ℝ) (hH : ∀ i, 0 ≤ H i)
    (hlarge : ∀ i, 4 ≤ rho * H i) (hwhole : ∀ i, rho * H i ≤ 2 * (N i : ℝ))
    (hratio : ∀ i, (N i : ℝ) ≤ A * H i) (hpay : 4 * A * Real.exp (-budget) ≤ rho)
    (c : ∀ i, (normalizedBoxPartitions N H rho hlarge hwhole i).Label) :
    ResidueSliceLogCostLE N
      (fun i => intervalCellLower (lo i) (normalizedBoxPartitions N H rho hlarge hwhole i) (c i))
      (fun i => (normalizedBoxPartitions N H rho hlarge hwhole i).length (c i)) 1 (fun _ => 0) budget := by
  apply physicalBoxCell_log_cost
  intro i
  have hc := (normalizedBoxPartitions_lengths N H rho hlarge hwhole i (c i)).1
  have hp := mul_le_mul_of_nonneg_right hpay (hH i)
  have hn := mul_le_mul_of_nonneg_left (hratio i) (Real.exp_nonneg (-budget))
  nlinarith

end Erdos3

end

end OAI
