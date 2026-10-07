import OAI.Combinatorics.Progressions.Estimates.PhysicalActiveIdealSite

namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

variable {D G α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
  (Z : Type*) [Fintype Z] {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)
  (R : D → ℝ) (hR : ∀ d, 0 < R d)

theorem physicalActiveProfileIdeal_normalized_support {degree : ℕ}
    (hdegree : ∀ d, h d ≤ degree) (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (v : (Σ d, O d) → ℝ)
    (hv : physicalActiveProfileIdeal (G := G) (B := B) Z h P sets R hR δ v ≠ 0) :
    ‖fun o : Σ d, O d => v o / R o.1.val‖ ≤ partitionedIdealRadius α degree + 1 := by
  apply le_of_not_gt
  intro hlarge
  apply hv
  rw [physicalActiveProfileIdeal_eq,
    activeAveragedProfileIdeal_zero_outside Z h P sets hdegree δ hδ hδ1 _ hlarge,
    mul_zero]

theorem physicalActiveProfileIdeal_relative_support {degree : ℕ}
    (hdegree : ∀ d, h d ≤ degree) (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (v : (Σ d, O d) → ℝ)
    (hv : physicalActiveProfileIdeal (G := G) (B := B) Z h P sets R hR δ v ≠ 0)
    (o : Σ d, O d) :
    |v o| ≤ (partitionedIdealRadius α degree + 1) * R o.1.val := by
  have hs := physicalActiveProfileIdeal_normalized_support Z h P sets R hR hdegree δ hδ hδ1 v hv
  have hc := (norm_le_pi_norm (fun q : Σ d, O d => v q / R q.1.val) o).trans hs
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hR o.1.val)] at hc
  exact (div_le_iff₀ (hR o.1.val)).mp hc

end Erdos3

end

end OAI
