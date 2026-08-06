(**
  Feed the fixed guarded row residue directly into native branch evidence.

  The two preceding modules deliberately expose different honest seams:

  - fixed-production identification turns one selected mode pair at the
    fixed deep prefix into synchronized append payloads for every caller;
  - canonical-append integration turns such a payload pair into native
    guarded evidence, and optionally combines it with parent roots.

  Their composition below removes the intermediate payload premise without
  changing translations.  In particular, [inputs] is shared literally by
  evidence identification, the fixed mode pair, the append traversal, and
  every conclusion.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAProof
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateDirectStructuralTranslation
  RawCodedDynamicTruthNativeZeroGuardedEvidenceIdentification
  RawCodedDynamicTruthNativeZeroGuardedPredecessorCompilation
  RawCodedDynamicTruthNativeZeroGuardedFixedProductionBoundary
  RawCodedDynamicTruthNativeZeroGuardedCanonicalAppendIntegration.

Module
  PABoundedRawCodedDynamicTruthNativeZeroGuardedFixedProductionIntegration.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedEvidenceIdentification.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedPredecessorCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedFixedProductionBoundary.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedCanonicalAppendIntegration.

(** The fixed two-mode residue is sufficient for evidence at every caller
    prefix.  Witness growth is still explicit in the conclusion. *)
Theorem
    raw_dynamicTruthImpGuardedEvidenceRoots_on_witnessed_extension_of_identified_fixed_productions_or_refutations :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      inputs sourceWitnessList sourceContext callerPrefix,
  RawDynamicTruthZeroGuardedEvidenceIdentification M inputs ->
  RawDynamicTruthZeroCanonicalIdentifiedGuardedFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
    M hPA inputs ->
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawDynamicTruthImpGuardedEvidenceRootsAt M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      targetContext callerPrefix.
Proof.
  intros M hPA inputs sourceWitnessList sourceContext callerPrefix
    hidentification hfixed hsource.
  apply
    (raw_dynamicTruthImpGuardedEvidenceRoots_on_witnessed_extension_of_canonical_append_kernel_payload_pair
      M hPA inputs sourceWitnessList sourceContext callerPrefix
      hidentification hsource).
  exact
    (raw_dynamicTruthZeroCanonicalIdentified_guardedDeepAppendRowKernelPayloadPairForAllCallers_of_fixed
      M hPA inputs hidentification hfixed callerPrefix).
Qed.

(** If the caller already has the three parent roots, the same fixed mode
    pair yields all five guarded branch roots on one common extension. *)
Theorem
    raw_dynamicTruthImpGuardedBranchRoots_on_witnessed_extension_of_parent_and_identified_fixed_productions_or_refutations :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      inputs sourceWitnessList sourceContext callerPrefix,
  RawDynamicTruthZeroGuardedEvidenceIdentification M inputs ->
  RawDynamicTruthZeroCanonicalIdentifiedGuardedFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
    M hPA inputs ->
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawDynamicTruthImpGuardedParentBranchRootsAt M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    sourceContext callerPrefix ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawDynamicTruthImpGuardedBranchRootsAt M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      targetContext callerPrefix.
Proof.
  intros M hPA inputs sourceWitnessList sourceContext callerPrefix
    hidentification hfixed hsource hparent.
  apply
    (raw_dynamicTruthImpGuardedBranchRoots_on_witnessed_extension_of_parent_and_canonical_append_kernel_payload_pair
      M hPA inputs sourceWitnessList sourceContext callerPrefix
      hidentification hsource hparent).
  exact
    (raw_dynamicTruthZeroCanonicalIdentified_guardedDeepAppendRowKernelPayloadPairForAllCallers_of_fixed
      M hPA inputs hidentification hfixed callerPrefix).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroGuardedFixedProductionIntegration.
