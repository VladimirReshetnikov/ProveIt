"""Delete unused declarations left behind by the folds and the earlier inlining passes.

Policy (as in cc482c5): private declarations, small undocumented helpers (at most 16 lines), and
orphans whose last user a refactor removed; documented results, larger standalone results and the
deliberate dichotomies / counterexamples stay. The `…W_printed` rfl hooks are dropped too: the
printed theorems are now instances of the parametric ones, which witnesses the same rfl facts.
"""
from foldlib import Fold

DEAD = {
    'Proofs05Weyl': ['iteratedNonzeroDifferenceNormSum_nonneg', 'iteratedDifferenceNormSum_nonneg',
                     'iteratedDifferenceNormSqSum_nonneg'],
    'Proofs05Lemma9Induction': ['section5_getLast?_tail_of_cons', 'section5_getLast?_cons_of_eq_some',
                                'section5MaximalTargets_getLast?'],
    'Proofs15Restriction': ['selectionEta_negativeCanonical'],
    'ProofInfrastructure': ['indicator_discValued', 'IsPartition.mem_iff', 'IsPartition.pairwise_disjoint'],
    'Proofs05Lemma9': ['polynomialPartition_rounding_threshold_gap'],
    'Proofs16ClassStepBounds': ['gen_exp_fact2'],
    'Proofs16ClassStepFejer': ['classPieceThresholdW_eq'],
    'Proofs16WidthMonotonicity': ['section16Lemma6Width_mono'],
    'Proofs18FejerCubicAt': ['fejerSquareAt_corpus'],
    'Proofs18GeneralIntervalStopping': ['interval_uniform_stopping'],
    'Proofs18JointSliceInverseFejer': ['singlePieceGlobalDensityFJ_le_one'],
    'Proofs18LengthSixCounts': ['nat_max_one_le_pow', 'pow_le_pow_of_base_le', 'pow_mono_exp'],
    'Proofs18LengthSixScale': ['nestC_three_eq'],
    'Proofs18WidthPowerBounds': ['WidthPowerLB.mono_exponent'],
    'Proofs18FinalEnvelopes': ['succ_sq_le_four_pow'],
    'Proofs16SplitStepBounds': ['swLW', 'split_step_basics'],
    'Proofs16SplitStepFejer': ['split_step_basics_fejer'],
    'Proofs16SinglePieceSpectrum': ['single_piece_on_affine_cell'],
    'Proofs16WithLift': ['Section16SampledOrAnchoredOn.synchronized_compressed_cover_with'],
    'Proofs16ClassPieces': ['classBudgetW_printed', 'classPieceThrW_printed'],
    'Proofs16PolyPieceTwoData': ['polyPieceBudgetW_printed', 'polyPieceSpecCountW_printed',
                                 'polyPieceFaceCountW_printed'],
    'Proofs16SinglePieceCoverGlobal': ['globalBudgetW_printed', 'globalTheta2W_printed', 'coverRho1W_printed',
                                       'coverRemWidthW_printed'],
}
F = Fold()
n = 0
for m, names in DEAD.items():
    for x in names:
        F.delete_decl(m, x)
        n += 1
F.commit()
print(n, 'declarations deleted')
