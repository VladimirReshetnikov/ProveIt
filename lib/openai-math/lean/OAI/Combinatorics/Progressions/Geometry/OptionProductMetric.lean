import Mathlib.Logic.Equiv.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Pseudo.Pi

namespace OAI

section

namespace Erdos3

theorem piOptionEquivProd_isometry {ι : Type*} [Fintype ι] {X : Option ι → Type*}
    [∀ i, PseudoMetricSpace (X i)] :
    Isometry (Equiv.piOptionEquivProd : (∀ i, X i) → X none × (∀ i, X (some i))) := by
  apply Isometry.of_dist_eq
  intro x y
  change dist (x none, fun i => x (some i)) (y none, fun i => y (some i)) = dist x y
  rw [Prod.dist_eq]
  apply le_antisymm
  · apply max_le (dist_le_pi_dist x y none)
    exact (dist_pi_le_iff dist_nonneg).mpr (fun i => dist_le_pi_dist x y (some i))
  · apply (dist_pi_le_iff (le_trans dist_nonneg (le_max_left _ _))).mpr
    intro i
    cases i with
    | none => exact le_max_left _ _
    | some i => exact (dist_le_pi_dist (fun i => x (some i)) (fun i => y (some i)) i).trans (le_max_right _ _)

noncomputable def optionPiIsometryEquiv {ι : Type*} [Fintype ι] {X : Option ι → Type*}
    [∀ i, PseudoMetricSpace (X i)] : (∀ i, X i) ≃ᵢ X none × (∀ i, X (some i)) where
  toEquiv := Equiv.piOptionEquivProd
  isometry_toFun := piOptionEquivProd_isometry

end Erdos3

end

end OAI
