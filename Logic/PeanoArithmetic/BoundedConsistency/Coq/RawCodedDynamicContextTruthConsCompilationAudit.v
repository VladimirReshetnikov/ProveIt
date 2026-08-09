(**
  Kernel and public-surface audit for represented dynamic-context cons.

  The source theorem is purely arithmetical: it extends one coded traversal
  and classifies every new live row as the adjoined head or an inherited row.
  The template proof then combines that classifier with an opaque Sigma leaf;
  completeness is never applied to the carrier-selected truth predicate.

  The final checks expose the exact public Imp-I formula-code adapter and the
  standard-witness-tail producer/transport boundary.  In particular, the
  producer does not consume an Imp-I recursive-child law root.
*)

From BoundedPAConsistency Require Import
  RawCodedDynamicContextTruthConsCompilation.

Module PABoundedRawCodedDynamicContextTruthConsCompilationAudit.

Import PABoundedRawCodedDynamicContextTruthConsCompilation.

(** Semantic closure and its represented arithmetic source. *)
Check raw_dynamicContextAllSigma_cons.
Check RawContextListConsTruthTransfer.
Check raw_contextListConsTruthTransfer.
Check contextListConsTruthTransferFormula.
Check contextListConsTruthTransferUniversalFormula.
Check raw_sat_contextListConsTruthTransferTermAt_iff.
Check contextListConsTruthTransferFormula_raw_valid.
Check PA_proves_contextListConsTruthTransferFormula.
Check PA_proves_contextListConsTruthTransferUniversalFormula.

(** Exact native and public template interfaces. *)
Check coqDynamicContextConsStructuralSourceTemplate.
Check coqDynamicContextConsNativeLawTemplate.
Check coqRestrictedPADirectImpIntroductionNewContextTruthTemplate.
Check coqRestrictedPADirectImpIntroductionContextConsLawTemplate.
Check RawCoqRestrictedPADirectImpIntroductionContextConsLawRoot.
Check coqDynamicContextConsStructuralAntecedent_agreement.
Check coqDynamicContextConsHeadEquality_shape.
Check coqDynamicContextConsSigmaMotive_head.
Check coqDynamicContextConsSigmaMotive_formula.

(** Honest template and carrier proof production. *)
Check coqDynamicContextConsRowAlternativeRoot_derives.
Check coqDynamicContextConsHeadBranchSigmaRoot_derives.
Check coqDynamicContextConsOldBranchSigmaRoot_derives.
Check coqDynamicContextConsFinalNewTruthRoot_derives.
Check coqDynamicContextConsStructuralImplicationRoot_derives.
Check
  raw_codedTemplatePALocalProofOf_contextListConsTruthTransferUniversal_on_tail.
Check raw_codedPALocalProof_dynamicContextConsNativeLaw_on_selected_tail.

(** Literal public-code transport and witnessed-tail composition. *)
Check raw_coqRestrictedPADirectImpIntroductionContextConsLaw_code.
Check coqDynamicContextConsImpIntroductionReadyContext_app_witnesses.
Check
  raw_coqRestrictedPADirectImpIntroductionContextConsLaw_on_selected_tail.
Check raw_impIntroductionContextConsLawRoot_surround_witnessed_tail.

Print Assumptions raw_dynamicContextAllSigma_cons.
Print Assumptions PA_proves_contextListConsTruthTransferUniversalFormula.
Print Assumptions coqDynamicContextConsStructuralImplicationRoot_derives.
Print Assumptions
  raw_codedPALocalProof_dynamicContextConsNativeLaw_on_selected_tail.
Print Assumptions
  raw_coqRestrictedPADirectImpIntroductionContextConsLaw_code.
Print Assumptions
  raw_coqRestrictedPADirectImpIntroductionContextConsLaw_on_selected_tail.
Print Assumptions
  raw_impIntroductionContextConsLawRoot_surround_witnessed_tail.

End PABoundedRawCodedDynamicContextTruthConsCompilationAudit.
