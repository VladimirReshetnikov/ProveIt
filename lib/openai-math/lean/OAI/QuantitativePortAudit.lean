/-
Added for ProveIt (not an upstream file; distributed under Apache-2.0).
Incremental axiom audit of the first 100 modules listed in
quantitative-port-manifest.json, plus the newly added compatibility lemmas.
This does not import or certify Results.Conclusions. Extend this checkpoint
as the remaining quantitative dependency port compiles.
-/
import OAI.Combinatorics.Progressions.Model
import OAI.Combinatorics.Progressions.Results.Basic
import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans
import OAI.Combinatorics.Progressions.Estimates.WeightedSummandCorrelation
import OAI.Combinatorics.Progressions.Estimates.BufferedSiteExpansion
import OAI.Combinatorics.Progressions.Lattices.RectangularLatticeCells
import OAI.Combinatorics.Progressions.Geometry.CompactBoxIntegral
import OAI.Combinatorics.Progressions.Probability.FiniteProbabilityLipschitz
import OAI.Combinatorics.Progressions.Sampling.ModelScoreComparison
import OAI.Combinatorics.Progressions.Estimates.CorrelationDerivative
import OAI.Combinatorics.Progressions.Estimates.CyclicShortShiftSet
import OAI.Combinatorics.Progressions.Estimates.UnitExpansionCorrelation
import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget
import OAI.Combinatorics.Progressions.Geometry.BoxDetectionExponents
import OAI.Combinatorics.Progressions.Estimates.FixedPartnerPower
import OAI.Combinatorics.Progressions.Linear.BalancedDualBounds
import OAI.Combinatorics.Progressions.Estimates.ShiftTestingGowers
import OAI.Combinatorics.Progressions.Estimates.FiniteFiberTest
import OAI.Combinatorics.Progressions.Probability.FiniteConditionedMass
import OAI.Combinatorics.Progressions.Estimates.DenseCorrelationPairs
import OAI.Combinatorics.Progressions.Estimates.BooleanCubeProduct
import OAI.Combinatorics.Progressions.Fourier.FiniteSpectrumCutoff
import OAI.Combinatorics.Progressions.Fourier.FiniteFourierSmoothing
import OAI.Combinatorics.Progressions.Estimates.FiniteConvolution
import OAI.Combinatorics.Progressions.Fourier.GowersFourierMultiplier
import OAI.Combinatorics.Progressions.Lattices.IntegerAbsInterval
import OAI.Combinatorics.Progressions.Estimates.CyclicCutNeighborhood
import OAI.Combinatorics.Progressions.Estimates.LinearCutoff
import OAI.Combinatorics.Progressions.Fourier.RectangularGridCharacter
import OAI.Combinatorics.Progressions.Estimates.InteriorIntervalCutoff
import OAI.Combinatorics.Progressions.Fourier.CRTConfigurationTorus
import OAI.Combinatorics.Progressions.Estimates.FiniteImageCover
import OAI.Combinatorics.Progressions.Lattices.IntegerLiftOffset
import OAI.Combinatorics.Progressions.Fourier.RationalLiftCharacterTwist
import OAI.Combinatorics.Progressions.Estimates.DependentPatchValue
import OAI.Combinatorics.Progressions.Sampling.FrozenPartitionScore
import OAI.Combinatorics.Progressions.Estimates.ProgressionPartitionComposition
import OAI.Combinatorics.Progressions.Estimates.SimultaneousDirichlet
import OAI.Combinatorics.Progressions.Fourier.AffineTorusDensityIncrement
import OAI.Combinatorics.Progressions.Dynamics.FlatPatchReset
import OAI.Combinatorics.Progressions.Estimates.NormalizedCutoffs
import OAI.Combinatorics.Progressions.Linear.PeriodicKernelPartition
import OAI.Combinatorics.Progressions.Lattices.AffineLowestLayer
import OAI.Combinatorics.Progressions.Polynomial.VectorPolynomialReconstruction
import OAI.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename
import OAI.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
import OAI.Combinatorics.Progressions.Estimates.WeightedPatchReparam
import OAI.Combinatorics.Progressions.Linear.WeightedParameterPatchRankPadding
import OAI.Combinatorics.Progressions.Sampling.PositivePartitionScore
import OAI.Combinatorics.Progressions.Fourier.TorusCellBudget
import OAI.Combinatorics.Progressions.Lattices.CRTProgressionVanishing
import OAI.Combinatorics.Progressions.Estimates.AlgebraicMajorUniformExponent
import OAI.Combinatorics.Progressions.Estimates.SymmetricIntervalDilation
import OAI.Combinatorics.Progressions.Lattices.IntegerFiberCount
import OAI.Combinatorics.Progressions.Lattices.ShortIntegerDifference
import OAI.Combinatorics.Progressions.Estimates.CommonDenominatorMultiples
import OAI.Combinatorics.Progressions.Estimates.GowersWeightedDerivative
import OAI.Combinatorics.Progressions.Geometry.SupportedCubeEquivTransport
import OAI.Combinatorics.Progressions.Estimates.CubeTranslation
import OAI.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost
import OAI.Combinatorics.Progressions.Estimates.PhysicalSliceCost
import OAI.Combinatorics.Progressions.Estimates.WeightedOverlapCorrelation
import OAI.Combinatorics.Progressions.Probability.NormalizedDensityL1
import OAI.Combinatorics.Progressions.Estimates.EmbeddedFiniteConditioning
import OAI.Combinatorics.Progressions.Estimates.FiniteReciprocalTenthTail
import OAI.Combinatorics.Progressions.Probability.ComplexPartitionMixture
import OAI.Combinatorics.Progressions.Lattices.BoxResiduePartition
import OAI.Combinatorics.Progressions.Geometry.BoxBlockBudget
import OAI.Combinatorics.Progressions.Sampling.NormalizedRealBoxHalfGrid
import OAI.Combinatorics.Progressions.Lattices.ResidueSliceNormalizedCell
import OAI.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice
import OAI.Combinatorics.Progressions.Polynomial.AffinePhaseBias
import OAI.Combinatorics.Progressions.Lattices.NearIntegerMultiples
import OAI.Combinatorics.Progressions.Dynamics.DenseProductPowerBudget
import OAI.Combinatorics.Progressions.Estimates.DenseProductApproximation
import OAI.Combinatorics.Progressions.Probability.DenseProductDensity
import OAI.Combinatorics.Progressions.Geometry.IntervalBoxDifference
import OAI.Combinatorics.Progressions.Estimates.ProductDifferenceBias
import OAI.Combinatorics.Progressions.Dynamics.MultiaffineBiasBudget
import OAI.Combinatorics.Progressions.Polynomial.PhasePreservingCauchySchwarz
import OAI.Combinatorics.Progressions.Probability.FiniteMassErrorSelection
import OAI.Combinatorics.Progressions.Geometry.BoxDifferenceHom
import OAI.Combinatorics.Progressions.Estimates.MultiaffineExpansion
import OAI.Combinatorics.Progressions.Fourier.BoxDifferenceCharacter
import OAI.Combinatorics.Progressions.Polynomial.MultiaffinePhaseDifference
import OAI.Combinatorics.Progressions.Estimates.MultiaffineBias
import OAI.Combinatorics.Progressions.Estimates.BlockSubsetCount
import OAI.Combinatorics.Progressions.Estimates.SquarefreeExponents
import OAI.Combinatorics.Progressions.Estimates.SquarefreeCoefficients
import OAI.Combinatorics.Progressions.Estimates.FormalExpLog
import OAI.Combinatorics.Progressions.Estimates.RationalHeight
import OAI.Combinatorics.Progressions.Estimates.TruncatedSeries
import OAI.Combinatorics.Progressions.Estimates.TensorContraction
import OAI.Combinatorics.Progressions.Estimates.DynkinTrees
import OAI.Combinatorics.Progressions.Linear.DynkinProjection
import OAI.Combinatorics.Progressions.Estimates.FreePrimitiveCriterion
import OAI.Combinatorics.Progressions.Linear.LieWordProjection
import OAI.Combinatorics.Progressions.Estimates.FreeLieTreeCoefficientBounds
import OAI.Combinatorics.Progressions.Nilpotent.NilpotentBilinearExponential
import OAI.Combinatorics.Progressions.Nilpotent.LieBCHContinuity
import OAI.Compat.Set
import OAI.Compat.Isometry
import OAI.Compat.FinsetInj
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, info) in env.constants do
    if (`OAI).isPrefixOf name && info.isTheorem then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "{name} depends on unapproved axiom {axiomName}"
      checked := checked + 1
  if checked == 0 then throwError "No OAI theorems found"
  logInfo m!"Audited {checked} public OAI theorems: only propext, Classical.choice, Quot.sound."
#print axioms Set.mem_ofPred_eq
#print axioms Isometry.lipschitzWith
#print axioms Finset.sum_le_sum_of_injOn
