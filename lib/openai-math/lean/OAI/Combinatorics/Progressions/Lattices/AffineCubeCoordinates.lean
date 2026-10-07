import OAI.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding

namespace OAI

section

namespace Erdos3

def affineCubeCoordinates {I : Type*} (u : Option I → ℝ) (v : Option I → ℕ)
    (x : Option I → ℝ) : Option I → ℝ := fun i => u i + (v i : ℝ) * x i

def affineIntegerCubeCoordinates {I : Type*} (u : Option I → ℤ) (v : Option I → ℕ)
    (x : Option I → ℤ) : Option I → ℤ := fun i => u i + (v i : ℤ) * x i

theorem affineIntegerCubeCoordinates_cast {I : Type*} (u : Option I → ℤ) (v : Option I → ℕ)
    (x : Option I → ℤ) :
    (fun i => (affineIntegerCubeCoordinates u v x i : ℝ)) =
      affineCubeCoordinates (fun i => (u i : ℝ)) v (fun i => (x i : ℝ)) := by
  funext i
  simp only [affineIntegerCubeCoordinates, affineCubeCoordinates, Int.cast_add, Int.cast_mul, Int.cast_natCast]

theorem ScalarCubeLocalizationData.affine_point_scale {I : Type*} [Fintype I] [DecidableEq I]
    (d : ScalarCubeLocalizationData I) (u : Option I → ℝ) (v : Option I → ℕ)
    (z : IntegerScalarCubeBox I d.length) :
    affineCubeCoordinates u v (fun i => (d.length : ℝ) * d.point z i) =
      affineCubeCoordinates u v (fun i => (z i : ℝ)) := by
  congr 1
  funext i
  exact d.point_scale z i

theorem ScalarCubeLocalizationData.affine_cell_scale {I : Type*} [Fintype I] [DecidableEq I]
    (d : ScalarCubeLocalizationData I) (u : Option I → ℝ) (v : Option I → ℕ)
    (k : Option I → Fin d.cellCount) (t : Option I → Fin d.cellLength) :
    affineCubeCoordinates u v (fun i => (d.length : ℝ) * d.cell k t i) =
      fun i => (u i + (v i : ℝ) * d.integerOffset k i) +
        ((v i * d.modulus i : ℕ) : ℝ) * (t i).val := by
  rw [d.cell_scale]
  funext i
  simp only [affineCubeCoordinates, Nat.cast_mul]
  ring

end Erdos3

end

end OAI
