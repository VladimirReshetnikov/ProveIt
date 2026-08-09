(**
  Kernel and public-surface audit for the two positive implication rows.

  The two public corollaries below are deliberately a finite-production
  boundary.  Each consumes four actual represented roots in one witnessed
  PA context and returns the named shared Sigma/Pi row-production root.  In
  particular, neither corollary assumes the implication truth law that the
  direct Imp-I soundness split is ultimately meant to construct.

  The final checks make the residual interface explicit.  The existing
  growing-tail compiler can consume a fixed production together with append
  and inherited-row roots, while the predecessor decision is produced in
  its native joint-state context.  Transporting those outputs into the exact
  direct Imp-I ready context remains separate from this finite leaf proof.
*)

From BoundedPAConsistency Require Import
  RawCodedDynamicTruthPredecessorDirectEvidenceLogicalRoots
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthSigmaImpFixedProductionCompilation
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth.

Module
  PABoundedRawCodedDynamicTruthSigmaImpFixedProductionCompilationAudit.

Import
  PABoundedRawCodedDynamicTruthPredecessorDirectEvidenceLogicalRoots.
Import
  PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import
  PABoundedRawCodedDynamicTruthSigmaImpFixedProductionCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth.

(** Literal decomposition and branch positions of the two selected leaves. *)
Check coqDynamicTruthSigmaImpFalseLeftOpenedLeafAt_shape.
Check coqDynamicTruthSigmaImpFalseLeftOpenedLeafAt_nth.
Check coqDynamicTruthSigmaImpTrueRightOpenedLeafAt_shape.
Check coqDynamicTruthSigmaImpTrueRightOpenedLeafAt_nth.

(** The reusable template derivation and represented four-root compiler. *)
Check coqDynamicTruthSigmaImpFixedProductionProofOnTailAt_derives.
Check coqDynamicTruthSigmaImpFixedProductionCurriedProofAt_derives.
Check
  raw_codedPALocalProofOf_dynamic_truth_sigma_imp_fixed_production_of_four_roots.

(** Concrete positive-row endpoints for ImpFalseLeft and ImpTrueRight. *)
Check
  raw_codedPALocalProofOf_dynamic_truth_sigma_imp_false_left_fixed_production_of_four_roots.
Check
  raw_codedPALocalProofOf_dynamic_truth_sigma_imp_true_right_fixed_production_of_four_roots.

(** Existing consumers/producers on the two sides of the remaining reroot. *)
Check
  raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_shared_successor_global_of_append_and_inherited_row_roots.
Check
  raw_dynamicTruthPredecessorEvidenceDecision_of_projected_decision_under_prefix_atomic_and_domain.
Check RawCoqRestrictedPADirectImpIntroductionFixedRowSplitRoots.
Check RawCoqRestrictedPADirectSelectedImpIntroductionFixedRowSplitTail.

Print Assumptions
  coqDynamicTruthSigmaImpFixedProductionProofOnTailAt_derives.
Print Assumptions
  coqDynamicTruthSigmaImpFixedProductionCurriedProofAt_derives.
Print Assumptions
  raw_codedPALocalProofOf_dynamic_truth_sigma_imp_fixed_production_of_four_roots.
Print Assumptions
  raw_codedPALocalProofOf_dynamic_truth_sigma_imp_false_left_fixed_production_of_four_roots.
Print Assumptions
  raw_codedPALocalProofOf_dynamic_truth_sigma_imp_true_right_fixed_production_of_four_roots.

End
  PABoundedRawCodedDynamicTruthSigmaImpFixedProductionCompilationAudit.
