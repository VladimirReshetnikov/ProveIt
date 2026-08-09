(** Kernel audit for the honest selected-Sigma Or source bridge. *)

From BoundedPAConsistency Require Import
  RawCodedDynamicTruthSigmaOrOpenedConstructorCodeProjection
  RawCodedRestrictedPASelectedSigmaBottomOrCorrelatedSourceBridge.

Import
  PABoundedRawCodedDynamicTruthSigmaOrOpenedConstructorCodeProjection.
Import
  PABoundedRawCodedRestrictedPASelectedSigmaBottomOrCorrelatedSourceBridge.

(** The bridge uses the literal applied-row tuple and the full substitution
    identity, including the global ternary substitution below fifteen
    binders. *)
Check coqRestrictedPASelectedSigmaBottomOrRowReplacements_exact.
Check
  coqRestrictedPASelectedSigmaBottomAppliedRootRowSelectedPayload_open_sequence.
Check coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaRow_substitution.
Check coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaDomain_substitution.
Check coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaOr_substitution.

(** Domain and Or leaf share one Ex8 spine.  Renaming by the eight Ex-E
    eigenvariables and reopening with [#7; ...; #0] recovers that exact
    correlated body. *)
Check
  coqRestrictedPASelectedSigmaBottomOrCorrelatedSourceTemplate_ex8_shape.
Check
  coqRestrictedPASelectedSigmaBottomOrCorrelatedSource_opened_rename8.
Check
  coqRestrictedPASelectedSigmaBottomOrCaseCorrelatedBodyProof_derives.
Check coqRestrictedPASelectedSigmaBottomOrCaseRenamedSourceProof_derives.

(** The represented endpoints first discharge only the honest Or residual,
    then close the eight local Ex-E nodes against the genuine selected-row
    root. *)
Check
  raw_codedPALocalProofOf_selectedSigmaBottom_or_case_correlated_source_imp.
Check
  raw_codedPALocalProofOf_selectedSigmaBottom_or_case_correlated_source_of_root.
Check
  raw_codedPALocalProofOf_selectedSigmaBottom_native_applied_or_correlated_source.

(** Re-audit the scope boundary: the honest parent is [#10], and is
    syntactically distinct from the historical guarded [#2] alias. *)
Check coqDynamicTruthSigmaOrOpenedConstructorCodeRootTemplate_shape.
Check coqDynamicTruthSigmaOrOpenedConstructorCodeRootTemplate_neq_guarded.

Print Assumptions
  coqRestrictedPASelectedSigmaBottomAppliedRootRowSelectedPayload_open_sequence.
Print Assumptions
  coqRestrictedPASelectedSigmaBottomOrCorrelatedSource_opened_rename8.
Print Assumptions
  coqRestrictedPASelectedSigmaBottomOrCaseRenamedSourceProof_derives.
Print Assumptions
  raw_codedPALocalProofOf_selectedSigmaBottom_or_case_correlated_source_imp.
Print Assumptions
  raw_codedPALocalProofOf_selectedSigmaBottom_native_applied_or_correlated_source.
Print Assumptions
  coqDynamicTruthSigmaOrOpenedConstructorCodeRootTemplate_neq_guarded.
