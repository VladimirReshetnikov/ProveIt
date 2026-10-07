/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Geometry.ProgressionTupleSliceSupport

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerScalarCube_progression {I : Type*} [Fintype I] [DecidableEq I]
    {L H step : ℕ} (c : ℤ)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (z : Option I → ℤ) (hz : IntegerScalarCube H z) :
    IntegerScalarCube L (fun i => (if i = none then c else 0) + (step : ℤ) * z i) := by
  intro t
  have ht : c + (step : ℤ) * integerScalarCubeValue z t ∈
      integerProgressionSupport c (step : ℤ) H := by
    rw [integerProgressionSupport, mem_translateSupport]
    apply Finset.mem_image.mpr
    refine ⟨integerScalarCubeValue z t, Finset.mem_Ico.mpr (hz t), ?_⟩
    change (step : ℤ) * integerScalarCubeValue z t = _
    ring
  have he : integerScalarCubeValue
      (fun i => (if i = none then c else 0) + (step : ℤ) * z i) t =
      c + (step : ℤ) * integerScalarCubeValue z t := by
    simp only [integerScalarCubeValue, ite_true, Option.some_ne_none, ite_false,
      zero_add, Finset.mul_sum, mul_add]
    ring
  rw [he]
  exact Finset.mem_Ico.mp (hsubset ht)

noncomputable def containedProgressionCubeMap (I : Type*) [Fintype I] [DecidableEq I]
    (L H step : ℕ) (c : ℤ) (hL : 0 < L)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (z : IntegerScalarCubeBox I H) : IntegerScalarCubeBox I L :=
  if hz : IntegerScalarCube H (fun i => (z i : ℤ)) then
    fun i => ⟨(if i = none then c else 0) + (step : ℤ) * (z i : ℤ),
      Finset.mem_Ico.mpr ⟨(integerScalarCube_coordinates
        (integerScalarCube_progression c hsubset _ hz) i).1.le,
        (integerScalarCube_coordinates (integerScalarCube_progression c hsubset _ hz) i).2⟩⟩
  else fun _ => ⟨0, Finset.mem_Ico.mpr (by constructor <;> omega)⟩

theorem containedProgressionCubeMap_value (I : Type*) [Fintype I] [DecidableEq I]
    (L H step : ℕ) (c : ℤ) (hL : 0 < L)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (z : IntegerScalarCubeBox I H) (hz : IntegerScalarCube H (fun i => (z i : ℤ)))
    (i : Option I) :
    (containedProgressionCubeMap I L H step c hL hsubset z i : ℤ) =
      (if i = none then c else 0) + (step : ℤ) * (z i : ℤ) := by
  rw [containedProgressionCubeMap, dite_eq_left hz]

theorem containedProgressionCubeMap_cube (I : Type*) [Fintype I] [DecidableEq I]
    (L H step : ℕ) (c : ℤ) (hL : 0 < L)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (z : IntegerScalarCubeBox I H) :
    IntegerScalarCube L (fun i => (containedProgressionCubeMap I L H step c hL hsubset z i : ℤ)) := by
  by_cases hz : IntegerScalarCube H (fun i => (z i : ℤ))
  · simp_rw [containedProgressionCubeMap_value I L H step c hL hsubset z hz]
    exact integerScalarCube_progression c hsubset _ hz
  · simp only [containedProgressionCubeMap, dite_eq_right hz]
    intro t
    simp only [integerScalarCubeValue, Finset.sum_const_zero, add_zero]
    exact ⟨le_rfl, Nat.cast_pos.mpr hL⟩

end Erdos3

end

end OAI
