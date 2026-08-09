(**
  Close the arithmetic-root boundary of the aligned Imp-I decision step.

  The literal Imp-I ready context proves atomic adequacy and rank-domain
  totality for its antecedent, but that compiler may first prepend a finite
  batch of standard PA-axiom witnesses.  The aligned native decision source,
  on the other hand, is carried by the original native base.  It would be
  unsound to contract the newly compiled child roots back to that base.

  We therefore make the context growth explicit.  The rebased kernel below
  transports only the old aligned decision projection forward to an already
  witnessed extension, where it can be combined with the two child roots.
  The composite theorem then runs the strict ready-child compiler followed
  by this kernel.  Its two finite witness batches are finally flattened with
  the literal append equations for standard witness prefixes.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedNumeralTermCode
  RawCodedProofAndIConstructor
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofComposition
  RawCodedPALocalProofAndIntroduction
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateTripleUniversalOpening
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedAssignmentUniversalDefinednessProofCompilation
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation
  RawCodedDynamicTruthNativeAlignedRootApplicationIdentification
  RawCodedDynamicTruthNativeAlignedArbitraryRootReadyDecision
  RawCodedRestrictedPADirectImpIntroductionReadyChildAtomicDomainCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeAlignedImpIntroductionReadyChildDecisionCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedProofAndIConstructor.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofAndIntroduction.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateTripleUniversalOpening.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedAssignmentUniversalDefinednessProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import
  PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAlignedRootApplicationIdentification.
Import
  PABoundedRawCodedDynamicTruthNativeAlignedArbitraryRootReadyDecision.
Import
  PABoundedRawCodedRestrictedPADirectImpIntroductionReadyChildAtomicDomainCompilation.

(** ------------------------------------------------------------------
    Exact syntax shared by the two independently checked compilers. *)

(** Opening the aligned atomic guard at [#6,#9,#8] discards the assignment
    coordinates and leaves precisely the ready-child atomic leaf. *)
Lemma
    coqRestrictedPADirectImpIntroductionReadyChildAtomic_aligned_view :
  coqRestrictedPADirectImpIntroductionReadyChildAtomicTemplate =
  coqDynamicTruthNativeAlignedImpIntroductionOpenedAtomicTemplate.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** The opened Sigma/Pi rank disjunction is exactly the child-domain leaf
    returned by the direct Imp-I arithmetic compiler. *)
Lemma
    coqRestrictedPADirectImpIntroductionReadyChildDomain_aligned_view :
  coqRestrictedPADirectImpIntroductionReadyChildDomainTemplate =
  coqDynamicTruthNativeAlignedImpIntroductionOpenedDomainTemplate.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** The represented conclusion selected after the opened admissibility law. *)
Definition coqDynamicTruthNativeAlignedImpIntroductionReadyDecisionTemplate
    : TemplateFormula :=
  tfOr
    (coqDynamicTruthNativeAlignedSigmaEvidenceAtRootTerms
      (ttVar 6) (ttVar 9) (ttVar 8))
    (coqDynamicTruthNativeAlignedPiEvidenceAtRootTerms
      (ttVar 6) (ttVar 9) (ttVar 8)).

(** ------------------------------------------------------------------
    Rebase the checked arbitrary-opening decision construction.

    [nativeBaseContext] remains the base stored in the aligned trace.
    [proofBaseContext] is an arbitrary witnessed extension on which the
    caller has already compiled the atomic and domain roots.  The explicit
    inclusion is exactly what licenses forward transport of the native
    decision projection; no equality or context contraction is assumed. *)

Theorem
    raw_dynamicTruthNativeAligned_impIntroduction_readyEvidenceDecision_rebased_of_atomic_and_domain_roots :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (tail : nat -> M) predecessorLevel nativeBaseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel nativeBaseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    inputLevelNumeral
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    nativeWitnessList proofWitnessList proofBaseContext
    atomicRoot domainRoot,
  RawNumeralTermCodeAt M (raw_succ M predecessorLevel)
    inputLevelNumeral ->
  RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
      M hPA tail predecessorLevel nativeBaseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs ->
  RawCodedPAAxiomWitnessContext M
    nativeWitnessList nativeBaseContext ->
  RawCodedPAAxiomWitnessContext M
    proofWitnessList proofBaseContext ->
  RawContextListIncluded M nativeBaseContext proofBaseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      proofBaseContext
      coqRestrictedPADirectImpIntroductionReadyPrefix)
    (rawDirectTemplateFormula inputs
      coqDynamicTruthNativeAlignedImpIntroductionOpenedAtomicTemplate)
    atomicRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      proofBaseContext
      coqRestrictedPADirectImpIntroductionReadyPrefix)
    (rawDirectTemplateFormula inputs
      coqDynamicTruthNativeAlignedImpIntroductionOpenedDomainTemplate)
    domainRoot ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) decisionRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses proofWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses proofBaseContext) /\
    RawContextListIncluded M proofBaseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses proofBaseContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses proofBaseContext)
        coqRestrictedPADirectImpIntroductionReadyPrefix)
      (rawDirectTemplateFormula inputs
        coqDynamicTruthNativeAlignedImpIntroductionReadyDecisionTemplate)
      decisionRoot.
Proof.
  intros M hPA tail predecessorLevel nativeBaseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs nativeWitnessList proofWitnessList proofBaseContext
    atomicRoot domainRoot hinputNumeral hstructural hnativeBase
    hproofBase hnativeIncluded hatomic hdomain.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (readyPrefix :=
    coqRestrictedPADirectImpIntroductionReadyPrefix).
  assert (hprefix : RawCodedTemplatePrefixAtomicallyAdequate
      M translation readyPrefix).
  {
    exact (raw_restrictedPADirectImpIntroductionReadyPrefix_atomically_adequate
      M hPA inputs).
  }

  (** Assignment coverage is the only additional arithmetic root needed
      after atomic adequacy and the domain disjunction are available. *)
  destruct
    (raw_codedPALocalProofOf_assignmentUniversalDefinedness_instance_on_witnessed_tail_under_prefix
      M hPA translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      proofWitnessList proofBaseContext readyPrefix
      (ttVar 9) (ttVar 8) (ttVar 6)
      hprefix hproofBase)
    as (decisionWitnesses & assignmentRoot & hextended & hassignment).
  rewrite <-
    coqDynamicTruthNativeAlignedImpIntroductionOpenedAssignmentTemplate_view
    in hassignment.
  set (extendedWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      decisionWitnesses proofWitnessList).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      decisionWitnesses proofBaseContext).
  assert (hproofIncluded :
      RawContextListIncluded M proofBaseContext extendedContext).
  {
    unfold extendedContext.
    exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
      M hPA decisionWitnesses proofBaseContext).
  }

  (** Move the two caller-supplied roots to the assignment compiler's exact
      extension before forming the opened admissibility conjunction. *)
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      proofWitnessList proofBaseContext extendedWitnessList extendedContext
      readyPrefix
      (rawDirectTemplateFormula inputs
        coqDynamicTruthNativeAlignedImpIntroductionOpenedAtomicTemplate)
      atomicRoot hproofBase hextended hproofIncluded hatomic)
    as [transportedAtomicRoot htransportedAtomic].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      proofWitnessList proofBaseContext extendedWitnessList extendedContext
      readyPrefix
      (rawDirectTemplateFormula inputs
        coqDynamicTruthNativeAlignedImpIntroductionOpenedDomainTemplate)
      domainRoot hproofBase hextended hproofIncluded hdomain)
    as [transportedDomainRoot htransportedDomain].
  set (decisionContext :=
    rawTemplateContextCodeOnTail translation extendedContext readyPrefix).
  set (openedAtomic := rawDirectTemplateFormula inputs
    coqDynamicTruthNativeAlignedImpIntroductionOpenedAtomicTemplate).
  set (openedAssignment := rawDirectTemplateFormula inputs
    coqDynamicTruthNativeAlignedImpIntroductionOpenedAssignmentTemplate).
  set (openedDomain := rawDirectTemplateFormula inputs
    coqDynamicTruthNativeAlignedImpIntroductionOpenedDomainTemplate).
  set (assignmentDomainRoot := rawProofAndIRoot M decisionContext
    openedAssignment openedDomain assignmentRoot transportedDomainRoot).
  assert (hassignmentDomain : RawCodedPALocalProofOf M decisionContext
      (rawFormulaAndCode M openedAssignment openedDomain)
      assignmentDomainRoot).
  {
    unfold assignmentDomainRoot.
    exact (raw_codedPALocalProofOf_andI M hPA decisionContext
      openedAssignment openedDomain assignmentRoot transportedDomainRoot
      hassignment htransportedDomain).
  }
  set (admissibleRoot := rawProofAndIRoot M decisionContext
    openedAtomic (rawFormulaAndCode M openedAssignment openedDomain)
    transportedAtomicRoot assignmentDomainRoot).
  assert (hadmissibleRaw : RawCodedPALocalProofOf M decisionContext
      (rawFormulaAndCode M openedAtomic
        (rawFormulaAndCode M openedAssignment openedDomain))
      admissibleRoot).
  {
    unfold admissibleRoot.
    exact (raw_codedPALocalProofOf_andI M hPA decisionContext
      openedAtomic (rawFormulaAndCode M openedAssignment openedDomain)
      transportedAtomicRoot assignmentDomainRoot
      htransportedAtomic hassignmentDomain).
  }
  assert (hadmissible : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        translation extendedContext readyPrefix)
      (rawDirectTemplateFormula inputs
        coqDynamicTruthNativeAlignedImpIntroductionOpenedAdmissibleTemplate)
      admissibleRoot).
  {
    rewrite
      coqDynamicTruthNativeAlignedImpIntroductionOpenedAdmissibleTemplate_shape.
    change (RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        translation extendedContext readyPrefix)
      (rawFormulaAndCode M
        (rawDirectTemplateFormula inputs
          coqDynamicTruthNativeAlignedImpIntroductionOpenedAtomicTemplate)
        (rawFormulaAndCode M
          (rawDirectTemplateFormula inputs
            coqDynamicTruthNativeAlignedImpIntroductionOpenedAssignmentTemplate)
          (rawDirectTemplateFormula inputs
            coqDynamicTruthNativeAlignedImpIntroductionOpenedDomainTemplate)))
      admissibleRoot).
    unfold openedAtomic, openedAssignment, openedDomain,
      decisionContext in *.
    exact hadmissibleRaw.
  }

  (** Identify and open the aligned source at the Imp-I coordinates. *)
  pose proof hstructural as hstructuralForSource.
  pose proof (raw_template_all3_elimination_chain M translation
    coqDynamicTruthNativeAlignedDecisionBodyTemplate
    (ttVar 6) (ttVar 9) (ttVar 8)) as hchain.
  change (RawCodedUniversalEliminationChain M
    (rawDirectTemplateFormula inputs
      (tfAll (tfAll (tfAll
        coqDynamicTruthNativeAlignedDecisionBodyTemplate))))
    (rawDirectTemplateFormula inputs
      (templateAll3Open coqDynamicTruthNativeAlignedDecisionBodyTemplate
        (ttVar 6) (ttVar 9) (ttVar 8)))) in hchain.
  rewrite
    (raw_dynamicTruthNativeAlignedDecisionSource_identified
      M hPA tail predecessorLevel nativeBaseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hinputNumeral hstructuralForSource) in hchain.
  rewrite
    coqDynamicTruthNativeAlignedImpIntroductionDecisionOpening_shape
    in hchain.
  change (RawCodedUniversalEliminationChain M
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalDecisionCode M
        (rawDynamicTruthNativeLocalAligned_currentSigmaDomain M tail
          predecessorLevel nativeBaseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned)
        (rawDynamicTruthNativeLocalAligned_currentPiDomain M tail
          predecessorLevel nativeBaseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned)
        (rawDynamicTruthNativeLocalAligned_currentSigmaEvidence M tail
          predecessorLevel nativeBaseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned)
        (rawDynamicTruthNativeLocalAligned_currentPiEvidence M tail
          predecessorLevel nativeBaseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned)))
    (rawFormulaImpCode M
      (rawDirectTemplateFormula inputs
        coqDynamicTruthNativeAlignedImpIntroductionOpenedAdmissibleTemplate)
      (rawFormulaOrCode M
        (rawDirectTemplateFormula inputs
          (coqDynamicTruthNativeAlignedSigmaEvidenceAtRootTerms
            (ttVar 6) (ttVar 9) (ttVar 8)))
        (rawDirectTemplateFormula inputs
          (coqDynamicTruthNativeAlignedPiEvidenceAtRootTerms
            (ttVar 6) (ttVar 9) (ttVar 8)))))) in hchain.
  pose proof
    (rawDynamicTruthNativeLocalAligned_decisionProjection M tail
      predecessorLevel nativeBaseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned) as hdecisionSource.

  (** This is the essential rebasing step: the native source moves forward
      to [proofBaseContext], never backward from the child extension. *)
  lazymatch type of hdecisionSource with
  | RawCodedPALocalProofOf _ _ ?sourceCode ?decisionSourceRoot =>
    destruct
      (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
        M hPA translation
        nativeWitnessList nativeBaseContext
        proofWitnessList proofBaseContext
        [] sourceCode decisionSourceRoot
        hnativeBase hproofBase hnativeIncluded hdecisionSource)
      as [rebasedDecisionSourceRoot hrebasedDecisionSource];
    cbn [rawTemplateContextCodeOnTail] in hrebasedDecisionSource;
    destruct
      (raw_codedPALocalProofOf_openedEvidenceDecision_on_standard_witness_extension_under_prefix
        M hPA translation proofWitnessList proofBaseContext readyPrefix
        decisionWitnesses
        (rawDynamicTruthLocalFormulaAll3Code M
          (rawDynamicTruthLocalDecisionCode M
            (rawDynamicTruthNativeLocalAligned_currentSigmaDomain M tail
              predecessorLevel nativeBaseContext currentLocal
              nextInputGlobalSigma nextInputGlobalPi aligned)
            (rawDynamicTruthNativeLocalAligned_currentPiDomain M tail
              predecessorLevel nativeBaseContext currentLocal
              nextInputGlobalSigma nextInputGlobalPi aligned)
            (rawDynamicTruthNativeLocalAligned_currentSigmaEvidence M tail
              predecessorLevel nativeBaseContext currentLocal
              nextInputGlobalSigma nextInputGlobalPi aligned)
            (rawDynamicTruthNativeLocalAligned_currentPiEvidence M tail
              predecessorLevel nativeBaseContext currentLocal
              nextInputGlobalSigma nextInputGlobalPi aligned)))
        (rawDirectTemplateFormula inputs
          coqDynamicTruthNativeAlignedImpIntroductionOpenedAdmissibleTemplate)
        (rawDirectTemplateFormula inputs
          (coqDynamicTruthNativeAlignedSigmaEvidenceAtRootTerms
            (ttVar 6) (ttVar 9) (ttVar 8)))
        (rawDirectTemplateFormula inputs
          (coqDynamicTruthNativeAlignedPiEvidenceAtRootTerms
            (ttVar 6) (ttVar 9) (ttVar 8)))
        rebasedDecisionSourceRoot admissibleRoot
        hprefix hproofBase hextended hchain
        hrebasedDecisionSource hadmissible)
      as [decisionRoot [_hincludedAgain hdecision]];
    exists decisionWitnesses, decisionRoot;
    split; [exact hextended |];
    split; [exact hproofIncluded |];
    exact hdecision
  end.
Qed.

(** ------------------------------------------------------------------
    Strict ready-child producer followed by the rebased decision kernel. *)

(** Honest nested form.  [childWitnesses] are allocated by the arithmetic
    child compiler and [decisionWitnesses] by assignment coverage.  The
    final inclusion is composed extensionally from the two checked inclusion
    proofs. *)
Theorem
    raw_dynamicTruthNativeAligned_impIntroduction_readyChild_evidenceDecision_nested :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (tail : nat -> M) predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    inputLevelNumeral
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList,
  RawNumeralTermCodeAt M (raw_succ M predecessorLevel)
    inputLevelNumeral ->
  RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (childWitnesses decisionWitnesses :
      StandardPAAxiomWitnessPrefix) decisionRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        decisionWitnesses
        (rawStandardPAAxiomWitnessPrefixWitnessListCode M
          childWitnesses baseWitnessList))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        decisionWitnesses
        (rawStandardPAAxiomWitnessPrefixContextCode M
          childWitnesses baseContext)) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M
        decisionWitnesses
        (rawStandardPAAxiomWitnessPrefixContextCode M
          childWitnesses baseContext)) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          decisionWitnesses
          (rawStandardPAAxiomWitnessPrefixContextCode M
            childWitnesses baseContext))
        coqRestrictedPADirectImpIntroductionReadyPrefix)
      (rawDirectTemplateFormula inputs
        coqDynamicTruthNativeAlignedImpIntroductionReadyDecisionTemplate)
      decisionRoot.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs baseWitnessList hinputNumeral hstructural hbase.
  destruct
    (raw_restrictedPADirectImpIntroduction_readyChild_atomic_and_domain_on_standard_witness_extension
      M hPA inputs baseWitnessList baseContext hbase)
    as (childWitnesses & atomicRoot & domainRoot & hchildWitnessed &
      hchildIncluded & hchildAtomic & hchildDomain).
  assert (hchildAtomicAligned : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          childWitnesses baseContext)
        coqRestrictedPADirectImpIntroductionReadyPrefix)
      (rawDirectTemplateFormula inputs
        coqDynamicTruthNativeAlignedImpIntroductionOpenedAtomicTemplate)
      atomicRoot).
  {
    rewrite <-
      coqRestrictedPADirectImpIntroductionReadyChildAtomic_aligned_view.
    exact hchildAtomic.
  }
  assert (hchildDomainAligned : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          childWitnesses baseContext)
        coqRestrictedPADirectImpIntroductionReadyPrefix)
      (rawDirectTemplateFormula inputs
        coqDynamicTruthNativeAlignedImpIntroductionOpenedDomainTemplate)
      domainRoot).
  {
    rewrite <-
      coqRestrictedPADirectImpIntroductionReadyChildDomain_aligned_view.
    exact hchildDomain.
  }
  destruct
    (raw_dynamicTruthNativeAligned_impIntroduction_readyEvidenceDecision_rebased_of_atomic_and_domain_roots
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs baseWitnessList
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        childWitnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        childWitnesses baseContext)
      atomicRoot domainRoot hinputNumeral hstructural hbase
      hchildWitnessed hchildIncluded hchildAtomicAligned hchildDomainAligned)
    as (decisionWitnesses & decisionRoot & hdecisionWitnessed &
      hdecisionIncluded & hdecision).
  exists childWitnesses, decisionWitnesses, decisionRoot.
  split; [exact hdecisionWitnessed |].
  split.
  - intros formula hmember.
    exact (hdecisionIncluded formula
      (hchildIncluded formula hmember)).
  - exact hdecision.
Qed.

(** Public flattened endpoint.  Prefix append is oriented so the later
    decision batch is the list prefix and the earlier child batch is its
    tail; both witness-list and context folds then reduce definitionally to
    the nested extension above. *)
Corollary
    raw_dynamicTruthNativeAligned_impIntroduction_readyChild_evidenceDecision :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (tail : nat -> M) predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    inputLevelNumeral
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList,
  RawNumeralTermCodeAt M (raw_succ M predecessorLevel)
    inputLevelNumeral ->
  RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) decisionRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext)
        coqRestrictedPADirectImpIntroductionReadyPrefix)
      (rawDirectTemplateFormula inputs
        coqDynamicTruthNativeAlignedImpIntroductionReadyDecisionTemplate)
      decisionRoot.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs baseWitnessList hinputNumeral hstructural hbase.
  destruct
    (raw_dynamicTruthNativeAligned_impIntroduction_readyChild_evidenceDecision_nested
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs baseWitnessList hinputNumeral hstructural hbase)
    as (childWitnesses & decisionWitnesses & decisionRoot &
      hwitnessed & hincluded & hdecision).
  exists (decisionWitnesses ++ childWitnesses), decisionRoot.
  split.
  - rewrite rawStandardPAAxiomWitnessPrefixWitnessListCode_app.
    rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
    exact hwitnessed.
  - split.
    + rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
      exact hincluded.
    + rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
      exact hdecision.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeAlignedImpIntroductionReadyChildDecisionCompilation.
