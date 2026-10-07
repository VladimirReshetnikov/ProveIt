import OAI.Combinatorics.Progressions.Probability.ScalarCubeDomainDensity

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def scalarCubeJoin {α : Type*} (z : (α → ℝ) × ℝ) : Option α → ℝ :=
  (MeasurableEquiv.piOptionEquivProd (fun _ : Option α => ℝ)).symm z

theorem scalarCubeJoin_none {α : Type*} (z : (α → ℝ) × ℝ) : scalarCubeJoin z none = z.2 := rfl

theorem scalarCubeJoin_some {α : Type*} (z : (α → ℝ) × ℝ) (i : α) :
    scalarCubeJoin z (some i) = z.1 i := rfl

theorem scalarCubeJoin_measurable (α : Type*) : Measurable (@scalarCubeJoin α) :=
  (MeasurableEquiv.piOptionEquivProd (fun _ : Option α => ℝ)).symm.measurable

theorem scalarCubeJoin_measurePreserving (α : Type*) [Fintype α] :
    MeasurePreserving (@scalarCubeJoin α) volume volume := by
  refine ⟨scalarCubeJoin_measurable α, ?_⟩
  exact Measure.pi_map_piOptionEquivProd (fun _ : Option α => (volume : Measure ℝ))

theorem scalarCubeJoin_value {α : Type*} [Fintype α] [DecidableEq α]
    (z : (α → ℝ) × ℝ) (t : Finset α) :
    scalarCubeValue (scalarCubeJoin z) t = z.2 + ∑ i ∈ t, z.1 i := by
  simp [scalarCubeValue, Fintype.sum_option, booleanFeature, scalarCubeJoin_none,
    scalarCubeJoin_some, ite_mul]

theorem scalarCubeJoin_face {α : Type*} [Fintype α] [DecidableEq α]
    (z : (α → ℝ) × ℝ) (i : Bool × Finset α) :
    scalarCubeFace i (scalarCubeJoin z) =
      if i.1 then 1 - (z.2 + ∑ k ∈ i.2, z.1 k) else z.2 + ∑ k ∈ i.2, z.1 k := by
  simp only [scalarCubeFace, scalarCubeJoin_value]

end Erdos3

end

end OAI
