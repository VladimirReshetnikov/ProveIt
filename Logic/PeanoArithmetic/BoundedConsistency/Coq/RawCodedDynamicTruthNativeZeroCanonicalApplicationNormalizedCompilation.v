(**
  Canonical application-root boundary for the normalized rank-zero callback.

  Normalization retains the represented local resources and the complete
  canonical trace.  A proof-producing traversal may extend the witnessed PA
  tail while compiling the two first-successor applications.  This module
  states that exact residual and shows that it is sufficient for the older
  native direct-evidence callback by composing the reusable predecessor-state
  transport.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPAGrowingTemplateConjunction
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedDynamicTruthLocalAdmissibilityCompilation
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation
  RawCodedDynamicTruthNativeZeroCanonicalTraceExactification
  RawCodedDynamicTruthNativeZeroCanonicalAppendSourceIdentification
  RawCodedDynamicTruthNativeZeroCanonicalApplicationDirectEvidence.

Module
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalApplicationNormalizedCompilation.

Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPAGrowingTemplateConjunction.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedDynamicTruthLocalAdmissibilityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import
  PABoundedRawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalTraceExactification.
Import
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalAppendSourceIdentification.
Import
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalApplicationDirectEvidence.

(** Producer-facing split of the canonical application package.  Arithmetic
    endpoint compilation may first choose a witnessed context carrying
    atomic adequacy and the domain disjunction.  Global traversal is then
    allowed to grow once more while returning the two canonical applications
    through the standard growing-pair interface. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingCanonicalGlobalApplicationResourcesCompilerOnCanonicalNormalizedResources
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M translation
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists endpointWitnessList endpointContext atomicRoot domainRoot,
      RawCodedPAAxiomWitnessContext M endpointWitnessList endpointContext /\
      RawContextListIncluded M baseContext endpointContext /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M endpointContext)
        (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M endpointContext)
        (rawFormulaOrCode M
          (rawDynamicTruthZeroSigmaDomainCode M)
          (rawDynamicTruthZeroPiDomainCode M)) domainRoot /\
      RawDynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom M
        endpointContext
        (rawQuotedFormulaCode M
          dynamicTruthZeroInputGlobalSigmaApplicationFormula)
        (rawQuotedFormulaCode M
          dynamicTruthZeroInputGlobalPiApplicationFormula).

Arguments
  RawDynamicTruthNativeLocalZeroGrowingCanonicalGlobalApplicationResourcesCompilerOnCanonicalNormalizedResources
  M translation : clear implicits.

(** Append-facing form of the same residual.  Unlike an empty-prefix pair,
    these applications are compiled with the two predecessor-state formulas
    already present.  This is essential: the canonical Sigma application is
    not itself an open theorem of PA. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerOnCanonicalNormalizedResources
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M translation
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists endpointWitnessList endpointContext atomicRoot domainRoot,
      RawCodedPAAxiomWitnessContext M endpointWitnessList endpointContext /\
      RawContextListIncluded M baseContext endpointContext /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M endpointContext)
        (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M endpointContext)
        (rawFormulaOrCode M
          (rawDynamicTruthZeroSigmaDomainCode M)
          (rawDynamicTruthZeroPiDomainCode M)) domainRoot /\
      RawCodedPAGrowingTemplateLocalProofPairAt M translation
        endpointContext coqDynamicTruthPredecessorStateTemplateContext
        (rawQuotedFormulaCode M
          dynamicTruthZeroInputGlobalSigmaApplicationFormula)
        (rawQuotedFormulaCode M
          dynamicTruthZeroInputGlobalPiApplicationFormula).

Arguments
  RawDynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerOnCanonicalNormalizedResources
  M translation : clear implicits.

(** Concrete append-facing residue.  Arithmetic normalization first chooses
    one witnessed endpoint carrying atomic adequacy and the rank-domain
    disjunction.  The remaining traversal producer supplies both canonical
    row-implication packages under the literal predecessor-state prefix, at
    one standard helper batch.  The five row binders and seventh-field
    normalization are compiled by the adapter below.  Packaging both
    polarities together records the synchronization required by the
    downstream growing pair and avoids two independently chosen append
    contexts. *)
Definition
    RawDynamicTruthNativeLocalZeroCanonicalPermutedAppendInputResourcesCompilerOnCanonicalNormalizedResources
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M translation
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists endpointWitnessList endpointContext atomicRoot domainRoot,
    exists appendWitnesses : StandardPAAxiomWitnessPrefix,
      RawCodedPAAxiomWitnessContext M endpointWitnessList endpointContext /\
      RawContextListIncluded M baseContext endpointContext /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M endpointContext)
        (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M endpointContext)
        (rawFormulaOrCode M
          (rawDynamicTruthZeroSigmaDomainCode M)
          (rawDynamicTruthZeroPiDomainCode M)) domainRoot /\
      RawDynamicTruthZeroCanonicalPermutedAppendRowImplicationInputsUnderPrefixAt
        M translation 0 coqDynamicTruthPredecessorStateTemplateContext
          appendWitnesses /\
      RawDynamicTruthZeroCanonicalPermutedAppendRowImplicationInputsUnderPrefixAt
        M translation 1 coqDynamicTruthPredecessorStateTemplateContext
          appendWitnesses.

Arguments
  RawDynamicTruthNativeLocalZeroCanonicalPermutedAppendInputResourcesCompilerOnCanonicalNormalizedResources
  M translation : clear implicits.

(** Compile the concrete synchronized row-implication packages into the abstract
    state-application resource interface used by the existing normalized
    callback.  No represented proof is moved back to the normalized base:
    the arithmetic endpoint is retained as the source of the growing pair,
    and append traversal may extend it further. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerOnCanonicalNormalizedResources_of_permuted_append_input_resources
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalZeroCanonicalPermutedAppendInputResourcesCompilerOnCanonicalNormalizedResources
    M translation ->
  RawDynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerOnCanonicalNormalizedResources
    M translation.
Proof.
  intros M hPA translation hagreement hcompiler tail witnessList
    baseContext helperRoots sigmaDomain piDomain sigmaEvidence piEvidence
    hresources htrace.
  destruct
    (hcompiler tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (endpointWitnessList & endpointContext & atomicRoot & domainRoot &
      appendWitnesses & hendpointWitnessed & hbaseEndpointIncluded &
      hatomic & hdomain & hsigmaRows & hpiRows).
  pose proof
    (raw_dynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt_of_row_implication_inputs
      M hPA translation 0 coqDynamicTruthPredecessorStateTemplateContext
      appendWitnesses hsigmaRows) as hsigmaInputs.
  pose proof
    (raw_dynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt_of_row_implication_inputs
      M hPA translation 1 coqDynamicTruthPredecessorStateTemplateContext
      appendWitnesses hpiRows) as hpiInputs.
  exists endpointWitnessList, endpointContext, atomicRoot, domainRoot.
  split; [exact hendpointWitnessed |].
  split; [exact hbaseEndpointIncluded |].
  split; [exact hatomic |].
  split; [exact hdomain |].
  exact
    (raw_dynamicTruthZeroCanonicalStateApplicationPair_of_permuted_append_inputs
      M hPA translation hagreement appendWitnesses
      endpointWitnessList endpointContext hendpointWitnessed
      hsigmaInputs hpiInputs).
Qed.

(** Interpret the shared template prefix as the literal joint state context.
    The growing pair already records the final witnessed tail and inclusion,
    so no post-hoc assumption insertion occurs. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingCanonicalGlobalApplicationResourcesCompilerOnCanonicalNormalizedResources_of_state_application_resources
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerOnCanonicalNormalizedResources
    M translation ->
  RawDynamicTruthNativeLocalZeroGrowingCanonicalGlobalApplicationResourcesCompilerOnCanonicalNormalizedResources
    M translation.
Proof.
  intros M hPA translation hagreement hcompiler tail witnessList
    baseContext helperRoots sigmaDomain piDomain sigmaEvidence piEvidence
    hresources htrace.
  destruct
    (hcompiler tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (endpointWitnessList & endpointContext & atomicRoot & domainRoot &
      hendpointWitnessed & hbaseEndpointIncluded & hatomic & hdomain &
      applicationWitnessList & applicationContext &
      sigmaApplicationRoot & piApplicationRoot &
      happlicationWitnessed & hendpointApplicationIncluded &
      hsigmaApplication & hpiApplication).
  rewrite (raw_dynamicTruthPredecessorStateTemplateContextCode
    M translation hagreement applicationContext) in
    hsigmaApplication, hpiApplication.
  exists endpointWitnessList, endpointContext, atomicRoot, domainRoot.
  split; [exact hendpointWitnessed |].
  split; [exact hbaseEndpointIncluded |].
  split; [exact hatomic |].
  split; [exact hdomain |].
  exists applicationWitnessList, applicationContext.
  split; [exact happlicationWitnessed |].
  split; [exact hendpointApplicationIncluded |].
  constructor.
  - exists sigmaApplicationRoot. exact hsigmaApplication.
  - exists piApplicationRoot. exact hpiApplication.
Qed.

(** Conversely, expose any concrete joint-state global-root package through
    the structurally named state prefix.  Thus the append-facing form is an
    exact reformulation, not an additional compiler assumption. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerOnCanonicalNormalizedResources_of_global_application_resources
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalZeroGrowingCanonicalGlobalApplicationResourcesCompilerOnCanonicalNormalizedResources
    M translation ->
  RawDynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerOnCanonicalNormalizedResources
    M translation.
Proof.
  intros M _hPA translation hagreement hcompiler tail witnessList
    baseContext helperRoots sigmaDomain piDomain sigmaEvidence piEvidence
    hresources htrace.
  destruct
    (hcompiler tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (endpointWitnessList & endpointContext & atomicRoot & domainRoot &
      hendpointWitnessed & hbaseEndpointIncluded & hatomic & hdomain &
      applicationWitnessList & applicationContext &
      happlicationWitnessed & hendpointApplicationIncluded &
      happlications).
  destruct happlications as
    [(sigmaApplicationRoot & hsigmaApplication)
      (piApplicationRoot & hpiApplication)].
  exists endpointWitnessList, endpointContext, atomicRoot, domainRoot.
  split; [exact hendpointWitnessed |].
  split; [exact hbaseEndpointIncluded |].
  split; [exact hatomic |].
  split; [exact hdomain |].
  exists applicationWitnessList, applicationContext,
    sigmaApplicationRoot, piApplicationRoot.
  split; [exact happlicationWitnessed |].
  split; [exact hendpointApplicationIncluded |].
  rewrite (raw_dynamicTruthPredecessorStateTemplateContextCode
    M translation hagreement applicationContext).
  split; assumption.
Qed.

Theorem
    raw_dynamicTruthNativeLocalZeroGrowingCanonicalApplicationResourceCompilers_equivalent
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  (RawDynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerOnCanonicalNormalizedResources
      M translation <->
   RawDynamicTruthNativeLocalZeroGrowingCanonicalGlobalApplicationResourcesCompilerOnCanonicalNormalizedResources
      M translation).
Proof.
  intros M hPA translation hagreement. split.
  - exact
      (raw_dynamicTruthNativeLocalZeroGrowingCanonicalGlobalApplicationResourcesCompilerOnCanonicalNormalizedResources_of_state_application_resources
        M hPA translation hagreement).
  - exact
      (raw_dynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerOnCanonicalNormalizedResources_of_global_application_resources
        M hPA translation hagreement).
Qed.

(** Exact proof-producing residue after rank-zero normalization.  The output
    may grow the witnessed tail and concludes canonical applications, not
    native truth evidence.  Atomic adequacy and the domain disjunction travel
    with those applications so the subsequent evidence handoff is closed. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsCompilerOnCanonicalNormalizedResources
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M translation
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists applicationWitnessList applicationContext,
      RawCodedPAAxiomWitnessContext M
        applicationWitnessList applicationContext /\
      RawContextListIncluded M baseContext applicationContext /\
      RawDynamicTruthZeroCanonicalApplicationRootsAt M applicationContext.

Arguments
  RawDynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsCompilerOnCanonicalNormalizedResources
  M translation : clear implicits.

(** Synchronize the split producer resources into the compact four-root
    application package.  Both possible context-growth steps are retained
    and their inclusions are composed, rather than requiring contraction to
    the normalized callback base. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsCompilerOnCanonicalNormalizedResources_of_global_application_resources
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalZeroGrowingCanonicalGlobalApplicationResourcesCompilerOnCanonicalNormalizedResources
    M translation ->
  RawDynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsCompilerOnCanonicalNormalizedResources
    M translation.
Proof.
  intros M hPA translation hagreement hcompiler tail witnessList
    baseContext helperRoots sigmaDomain piDomain sigmaEvidence piEvidence
    hresources htrace.
  destruct
    (hcompiler tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (endpointWitnessList & endpointContext & atomicRoot & domainRoot &
      hendpointWitnessed & hbaseEndpointIncluded & hatomic & hdomain &
      hglobals).
  destruct
    (raw_dynamicTruthZeroCanonicalApplicationRootsAt_of_growing_global_roots
      M hPA translation hagreement endpointWitnessList endpointContext
      atomicRoot domainRoot hendpointWitnessed hatomic hdomain hglobals)
    as (applicationWitnessList & applicationContext &
      happlicationWitnessed & hendpointApplicationIncluded &
      happlications).
  exists applicationWitnessList, applicationContext.
  split; [exact happlicationWitnessed |].
  split.
  - intros member hmember.
    exact (hendpointApplicationIncluded member
      (hbaseEndpointIncluded member hmember)).
  - exact happlications.
Qed.

(** Canonical application production suffices for native direct evidence.
    The two possible context extensions are composed explicitly, keeping the
    residual compiler free to select whatever finite PA witness prefix its
    traversal needs. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCanonicalNormalizedResources_of_canonicalApplicationRoots
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsCompilerOnCanonicalNormalizedResources
    M translation ->
  RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCanonicalNormalizedResources
    M translation.
Proof.
  intros M hPA translation hagreement hcompiler tail witnessList
    baseContext helperRoots sigmaDomain piDomain sigmaEvidence piEvidence
    hresources htrace.
  destruct
    (hcompiler tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (applicationWitnessList & applicationContext &
      happlicationWitnessed & hbaseApplicationIncluded & happlications).
  destruct
    (raw_dynamicTruthZeroDirectEvidenceRoots_of_canonicalApplicationRoots
      M hPA translation hagreement applicationWitnessList applicationContext
      happlicationWitnessed happlications)
    as (evidenceWitnessList & evidenceContext & hevidenceWitnessed &
      happlicationEvidenceIncluded & hevidence).
  exists evidenceWitnessList, evidenceContext.
  split; [exact hevidenceWitnessed |].
  split.
  - intros member hmember.
    exact (happlicationEvidenceIncluded member
      (hbaseApplicationIncluded member hmember)).
  - exact hevidence.
Qed.

(** Converse compiler adapter.  The normalized traversal may therefore stop
    at either the native evidence pair or the canonical global-application
    pair; the two resource boundaries differ only by PA-provable formulas
    and finite standard-axiom witness growth. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsCompilerOnCanonicalNormalizedResources_of_directEvidence
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCanonicalNormalizedResources
    M translation ->
  RawDynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsCompilerOnCanonicalNormalizedResources
    M translation.
Proof.
  intros M hPA translation hagreement hcompiler tail witnessList
    baseContext helperRoots sigmaDomain piDomain sigmaEvidence piEvidence
    hresources htrace.
  destruct
    (hcompiler tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (evidenceWitnessList & evidenceContext & hevidenceWitnessed &
      hbaseEvidenceIncluded & hevidence).
  destruct
    (raw_dynamicTruthZeroCanonicalApplicationRoots_of_directEvidenceRoots
      M hPA translation hagreement evidenceWitnessList evidenceContext
      hevidenceWitnessed hevidence)
    as (applicationWitnessList & applicationContext &
      happlicationWitnessed & hevidenceApplicationIncluded &
      happlications).
  exists applicationWitnessList, applicationContext.
  split; [exact happlicationWitnessed |].
  split.
  - intros member hmember.
    exact (hevidenceApplicationIncluded member
      (hbaseEvidenceIncluded member hmember)).
  - exact happlications.
Qed.

Theorem
    raw_dynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsAndDirectEvidenceCompilers_equivalent
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  (RawDynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsCompilerOnCanonicalNormalizedResources
      M translation <->
   RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCanonicalNormalizedResources
      M translation).
Proof.
  intros M hPA translation hagreement. split.
  - exact
      (raw_dynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCanonicalNormalizedResources_of_canonicalApplicationRoots
        M hPA translation hagreement).
  - exact
      (raw_dynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsCompilerOnCanonicalNormalizedResources_of_directEvidence
        M hPA translation hagreement).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalApplicationNormalizedCompilation.
