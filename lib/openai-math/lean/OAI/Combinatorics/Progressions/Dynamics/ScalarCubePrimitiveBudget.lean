import OAI.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding
import OAI.Combinatorics.Progressions.Lattices.ResidueCutoffLengthBudget

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

structure ScalarCubePrimitiveBudget {I : Type*} [Fintype I] [DecidableEq I]
    (s : NormalizedScalarCubeSource I) (A : ℝ≥0) (U : ℝ) : Prop where
  one_le : 1 ≤ U
  dimension_le : (Fintype.card I : ℝ) + 1 ≤ U
  modulus_le : (s.modulusBound : ℝ) ≤ U
  weight_le : (s.weightBound : ℝ) ≤ U
  weightLipschitz_le : (s.weightLipschitz : ℝ) ≤ U
  boundary_le : scalarCubeBoundaryConstant I ≤ U
  grid_le : 2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) ≤ U
  derivative_le : scalarCubeCutoffDerivativeNumerator I A ≤ U
  density_le : paddedResidueDensityCap I s.modulusBound ≤ U

end Erdos3

end

end OAI
