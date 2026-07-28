(**
  Kernel-facing audit for the dependency-aware native substitution stage.

  This audit fixes the exact cumulative antecedent, checks both directions
  of the structural body/leaf interface, and reports assumptions for the
  carried-context ordinary proof of the graph-selected substitution field.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedDynamicTruthNativeCrossLevelGuardRootCompilation
  RawCodedDynamicTruthNativeSubstitutionStagedRootCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeSubstitutionStagedRootCompilationAudit.

Import PA.
Import PAHierarchyReduction.
Import PABoundedRawCodedSyntaxConstructors.
Import
  PABoundedRawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeSubstitutionStagedRootCompilation.

(** The antecedent is literally Lean's substitution-stage [shiftContext]:
    current master, then local, then cross-level, then shift. *)
Check rawDynamicTruthNativeSubstitutionStagedAntecedentCode.
Check RawDynamicTruthNativeSubstitutionStagedPrerequisitesAt.

Goal forall (M : RawPAModel)
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal nextCrossLevel nextShift,
  rawDynamicTruthNativeSubstitutionStagedAntecedentCode M
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel nextShift =
  rawFormulaAndCode M
    (rawFormulaAndCode M
      (rawDynamicTruthNativeCrossLevelStagedAntecedentCode M
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal nextLocal)
      nextCrossLevel)
    nextShift.
Proof. reflexivity. Qed.

(** One synchronized implication, in the same witnessed context, is the
    complete remaining arithmetic seam. *)
Check
  RawDynamicTruthNativeSubstitutionStagedBodyImplicationRootOn.
Check
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler.
Check
  raw_dynamicTruthNativeSubstitutionStagedBodyRoot_of_implication.

(** The body is decomposed only with checked insertion, assumptions, Imp-E,
    and And-E.  Trace adequacy supplies every inserted source formula. *)
Check raw_dynamicTruthNativeSubstitutionAntecedent_atomically_adequate.
Check raw_dynamicTruthNativeSubstitutionLocalRootsOn_of_body_root.
Check raw_dynamicTruthNativeSubstitutionDirectionalLeaf_of_local_root.
Check
  raw_dynamicTruthNativeSubstitutionDirectionalLeavesOn_of_local_roots.
Check
  raw_dynamicTruthNativeSubstitutionStagedResources_of_body_implication.
Check
  raw_dynamicTruthNativeSubstitutionStagedLocalRoots_via_directional_leaves.

(** Seven All-I constructors retain the original witnessed PA context; the
    endpoint is the exact field code selected by the transform trace. *)
Check rawDynamicTruthNativeSubstitutionCarriedProofCertificate.
Check
  raw_codedPAProofOf_dynamicTruthNativeSubstitutionField_of_body_root_on.
Check
  raw_dynamicTruthNativeSubstitutionStagedTraceFieldProof_of_body_implication.
Check
  raw_dynamicTruthNativeSubstitutionStagedFieldProof_of_body_implication.

Print Assumptions
  raw_dynamicTruthNativeSubstitutionStagedBodyRoot_of_implication.
Print Assumptions
  raw_dynamicTruthNativeSubstitutionLocalRootsOn_of_body_root.
Print Assumptions
  raw_dynamicTruthNativeSubstitutionDirectionalLeavesOn_of_local_roots.
Print Assumptions
  raw_dynamicTruthNativeSubstitutionStagedResources_of_body_implication.
Print Assumptions
  raw_dynamicTruthNativeSubstitutionStagedLocalRoots_via_directional_leaves.
Print Assumptions
  raw_codedPAProofOf_dynamicTruthNativeSubstitutionField_of_body_root_on.
Print Assumptions
  raw_dynamicTruthNativeSubstitutionStagedTraceFieldProof_of_body_implication.
Print Assumptions
  raw_dynamicTruthNativeSubstitutionStagedFieldProof_of_body_implication.

End
  PABoundedRawCodedDynamicTruthNativeSubstitutionStagedRootCompilationAudit.
