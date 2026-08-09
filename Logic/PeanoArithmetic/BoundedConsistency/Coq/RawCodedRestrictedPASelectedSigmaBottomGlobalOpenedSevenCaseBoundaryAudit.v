(** Kernel audit for the scope-correct selected-Sigma bottom boundary. *)

From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedStandardFormulaScopeDecision
  RawCodedDynamicTruthQFBranchExclusivity
  RawCodedDynamicTruthImpBranchExclusivity
  RawCodedDynamicTruthBooleanBranchExclusivity
  RawCodedDynamicTruthQuantifierBranchExclusivity
  RawCodedRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseBoundary.

Import PA.
Import PABoundedRawCodedStandardFormulaScopeDecision.
Import PABoundedRawCodedDynamicTruthQFBranchExclusivity.
Import PABoundedRawCodedDynamicTruthImpBranchExclusivity.
Import PABoundedRawCodedDynamicTruthBooleanBranchExclusivity.
Import PABoundedRawCodedDynamicTruthQuantifierBranchExclusivity.
Import
  PABoundedRawCodedRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseBoundary.

(** The old direct-local producer already fails on each of the five fixed
    middle constructors: those Ex8 sources retain row/global slots and are
    not ternary predicates.  QF is genuinely ternary; the universal branch
    is ternary when its lower-application leaf is itself closed, which does
    not repair the invalid all-branches producer. *)
Goal standardFormulaScopedb 3
  dynamicTruthSigmaQFEx8BranchFormula = true.
Proof. vm_compute. reflexivity. Qed.

Goal standardFormulaScopedb 3
  dynamicTruthSigmaImpFalseLeftEx8BranchFormula = false.
Proof. vm_compute. reflexivity. Qed.

Goal standardFormulaScopedb 3
  dynamicTruthSigmaImpTrueRightEx8BranchFormula = false.
Proof. vm_compute. reflexivity. Qed.

Goal standardFormulaScopedb 3
  dynamicTruthSigmaAndEx8BranchFormula = false.
Proof. vm_compute. reflexivity. Qed.

Goal standardFormulaScopedb 3
  dynamicTruthSigmaOrEx8BranchFormula = false.
Proof. vm_compute. reflexivity. Qed.

Goal standardFormulaScopedb 3
  dynamicTruthSigmaEx8BranchFormula = false.
Proof. vm_compute. reflexivity. Qed.

Goal standardFormulaScopedb 3
  (dynamicTruthSigmaUniversalEx8BranchFormula (pEq tZero tZero)) = true.
Proof. vm_compute. reflexivity. Qed.

Check coqRestrictedPASelectedSigmaBottomAppliedGlobalSource.
Check coqRestrictedPASelectedSigmaBottomAppliedRootRowReplacements.
Check coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalDeepContextOn.
Check coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn.
Check coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch.
Check RawRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseSupportAt.
Check RawRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseCompiler.

Check raw_codedTemplateTernaryApplication_selectedSigmaBottom_global.
Check raw_codedPALocalProofOf_selectedSigmaBottom_applied_root_row_selected.
Check raw_codedPALocalProofOf_selectedSigmaBottom_native_opened_or7.
Check raw_codedPALocalProofOf_selectedSigmaBottom_native_global_deep_bottom.
Check raw_codedPALocalProofOf_selectedSigmaBottom_native_applied_refutation.
Check
  raw_codedPALocalProofOf_selectedSigmaBottom_native_applied_refutation_growing.

Print Assumptions
  raw_codedTemplateTernaryApplication_selectedSigmaBottom_global.
Print Assumptions
  raw_codedPALocalProofOf_selectedSigmaBottom_applied_root_row_selected.
Print Assumptions
  raw_codedPALocalProofOf_selectedSigmaBottom_native_opened_or7.
Print Assumptions
  raw_codedPALocalProofOf_selectedSigmaBottom_native_global_deep_bottom.
Print Assumptions
  raw_codedPALocalProofOf_selectedSigmaBottom_native_applied_refutation.
Print Assumptions
  raw_codedPALocalProofOf_selectedSigmaBottom_native_applied_refutation_growing.
