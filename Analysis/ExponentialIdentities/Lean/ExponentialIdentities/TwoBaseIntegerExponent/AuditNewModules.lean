import ExponentialIdentities.TwoBaseIntegerExponent.CandidateLattice
import ExponentialIdentities.TwoBaseIntegerExponent.KernelDichotomy
import ExponentialIdentities.TwoBaseIntegerExponent.SecondIterateKernel
import ExponentialIdentities.TwoBaseIntegerExponent.TowerRigidity
import ExponentialIdentities.TwoBaseIntegerExponent.SymmetricTowerConstants
import ExponentialIdentities.TwoBaseIntegerExponent.PrimeLogSpaceOperator
import ExponentialIdentities.TwoBaseIntegerExponent.ArbitraryNodeRepulsion
import ExponentialIdentities.TwoBaseIntegerExponent.SemigroupGapBound

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

end LeanProofs.TwoBaseIntegerExponent
