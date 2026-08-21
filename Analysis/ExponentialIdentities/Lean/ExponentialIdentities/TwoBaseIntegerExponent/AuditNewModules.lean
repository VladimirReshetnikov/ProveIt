import ExponentialIdentities.TwoBaseIntegerExponent.CandidateLattice
import ExponentialIdentities.TwoBaseIntegerExponent.KernelDichotomy
import ExponentialIdentities.TwoBaseIntegerExponent.SecondIterateKernel
import ExponentialIdentities.TwoBaseIntegerExponent.TowerRigidity
import ExponentialIdentities.TwoBaseIntegerExponent.SymmetricTowerConstants
import ExponentialIdentities.TwoBaseIntegerExponent.PrimeLogSpaceOperator
import ExponentialIdentities.TwoBaseIntegerExponent.ArbitraryNodeRepulsion
import ExponentialIdentities.TwoBaseIntegerExponent.SemigroupGapBound
import ExponentialIdentities.TwoBaseIntegerExponent.OrderedChamberPositivity
import ExponentialIdentities.TwoBaseIntegerExponent.ExternalRankClassification
import ExponentialIdentities.TwoBaseIntegerExponent.PerfectPowerContent
import ExponentialIdentities.TwoBaseIntegerExponent.RootSaturation
import ExponentialIdentities.TwoBaseIntegerExponent.ValuationLattice
import ExponentialIdentities.TwoBaseIntegerExponent.RationalFunctionRigidity
import ExponentialIdentities.TwoBaseIntegerExponent.MinPlusCeiling
import ExponentialIdentities.TwoBaseIntegerExponent.ComplexSolutions

/-!
# Assumption audit for the newly formalized modules

Each `#print axioms` below must report only the three standard Lean foundations
`propext`, `Classical.choice`, `Quot.sound`.  Anything else — in particular
`sorryAx` — is a trust breach and must fail review.

The two explicit analytic inputs of this round, `RpowDividedDifferenceMeanValue`
and `NewtonFactorization`, are *hypotheses of theorems*, not axioms, so they do
not and cannot appear here; they are visible instead in the statements of
`le_vandermondeProduct_of_dividedDiffMeanValue`, `packing_of_dividedDiffMeanValue`
and `card_le_ten_thousand_log_sq`.
-/

namespace LeanProofs.TwoBaseIntegerExponent

-- Candidate lattice
#print axioms twoBaseNaturalCandidate_gcd
#print axioms twoBaseNaturalCandidate_lcm
#print axioms exists_fixed_odd_core_of_not_alaogluErdosConjecture

-- Kernel dichotomy
#print axioms multiplicativelyDependentOutputs_iff_secondIterateKernelRelation
#print axioms twoBaseNonintegerSolution_kernel_dichotomy

-- Second-iterate kernel
#print axioms kernelPairs_det_eq_zero
#print axioms kernelPairs_prop_dim
#print axioms saturatedKernel_invariant

-- Tower rigidity
#print axioms alaogluErdosConjecture_iff_two_rpow_square_cube_isAlgebraic
#print axioms TwoBaseNonintegerSolution.base_two_tower_dichotomy

-- Symmetric tower constants
#print axioms TwoBaseNonintegerSolution.hasPositiveRationalPower_symmetricTowerThree
#print axioms TwoBaseNonintegerSolution.hasPositiveRationalPower_symmetricTowerTwo

-- Prime-log-space operator
#print axioms primeLogSpanThetaPullbackRankOne_iff_rationalOutput
#print axioms alaogluErdosConjecture_of_primeLogSpanThetaPullbackRankOne

-- Arbitrary-node repulsion
#print axioms det_nodeMatrix_eq_vandermondeProduct_mul_dividedDiff
#print axioms le_vandermondeProduct_of_dividedDiffMeanValue
#print axioms packing_of_dividedDiffMeanValue

-- Semigroup gap bound
#print axioms abs_det_le_of_abs_entry_le
#print axioms det_semigroupMatrix_ne_zero
#print axioms card_le_ten_thousand_log_sq

-- Ordered-chamber positivity
#print axioms det_rpowVandermonde_pos
#print axioms det_semigroupMatrix_pos
#print axioms one_le_det_semigroupMatrix_of_strictMono

-- External-rank classification
#print axioms existsUnique_hasExternalRankType
#print axioms TwoBaseNonintegerSolution.externalRankClassification
#print axioms hasExternalRankType_independent_iff_not_multiplicativelyDependentOutputs

-- Perfect-power content
#print axioms isCommonOutputPower_iff_twoBaseIntegralSolution_div

-- Root saturation
#print axioms exists_canonicalConeData_of_not_alaogluErdosConjecture

-- Valuation lattice
#print axioms finite_quotient_ratOutputLattice
#print axioms closure_quotient_pair_eq_top

-- Rational-function rigidity
#print axioms twoBaseIntegralSolution_mul_iff
#print axioms alaogluErdosConjecture_iff_solutions_closed_under_mul
#print axioms alaogluErdosConjecture_iff_solutions_closed_under_sq
#print axioms rationalFunction_rigidity_at_generator

-- Min-plus ceiling
#print axioms minPlusContent_le_of_le
#print axioms minPlusContent_le_of_natAbs_le
#print axioms primeContent_le_log
#print axioms det_dvd_and_not_dvd_of_unique_min

-- Complex exponents
#print axioms im_eq_zero_of_complexTwoBaseIntegralSolution
#print axioms twoBaseIntegralSolution_re_of_complex

end LeanProofs.TwoBaseIntegerExponent
