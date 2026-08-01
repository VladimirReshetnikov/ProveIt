(**
  Identify canonical rank-zero append sources with canonical applications.

  The permuted append traversal reverses its three exposed argument slots.
  When its two local rows are the literal first-successor rows above the
  fixed global base predicates, the resulting template is exactly the
  standard ternary application isolated by canonical trace exactification.
  This is a syntax theorem; no semantic or proof-producing premise occurs.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedSyntaxConstructors
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedRestrictedPAProof
  RawCodedPAProofLeafCertificates
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedPALocalProofUniversalIntroductionChain
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedLtSuccCasesProofCompilation
  RawCodedPAGrowingTemplateConjunction
  RawCodedFourStateTableAppendSource
  RawCodedFourStateTableAppendProofCompilation
  RawCodedFourStateTableAppendExistentialElimination
  RawCodedFourStateTableAppendRowLtSuccCases
  RawCodedFourStateTableAppendGlobalTraversalAssembly
  RawCodedFourStateTableAppendTemplateGlobalTraversalAssembly
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthPredecessorAdmissibilityAssignmentCompilation
  RawCodedDynamicTruthPredecessorAtomicDomainGlobalRootsSynchronization
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthGlobalBaseRootClosure
  RawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly
  RawCodedDynamicTruthNativeZeroCanonicalTraceExactification.

Module
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalAppendSourceIdentification.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProofLeafCertificates.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedPAGrowingTemplateConjunction.
Import PABoundedRawCodedFourStateTableAppendSource.
Import PABoundedRawCodedFourStateTableAppendProofCompilation.
Import PABoundedRawCodedFourStateTableAppendExistentialElimination.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
Import PABoundedRawCodedFourStateTableAppendGlobalTraversalAssembly.
Import PABoundedRawCodedFourStateTableAppendTemplateGlobalTraversalAssembly.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import
  PABoundedRawCodedDynamicTruthPredecessorAdmissibilityAssignmentCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorAtomicDomainGlobalRootsSynchronization.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthGlobalBaseRootClosure.
Import
  PABoundedRawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly.
Import
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalTraceExactification.

(** Literal local rows used by the first global successor. *)
Definition dynamicTruthZeroCanonicalSigmaRowFormula : formula :=
  dynamicTruthSigmaSuccessorRowFormula (Term.numeral 1)
    dynamicTruthGlobalPiBaseFormula.

Definition dynamicTruthZeroCanonicalPiRowFormula : formula :=
  dynamicTruthPiSuccessorRowFormula (Term.numeral 1)
    dynamicTruthGlobalSigmaBaseFormula.

(** Reversing the exposed tuple is definitionally the protected three-open
    application at [#2,#1,#0].  Kernel computation is intentional here: it
    audits the complete binder-sensitive syntax tree. *)
Lemma coqFourStateTableAppendPermutedTemplateGlobalSource_zero_sigma :
  coqFourStateTableAppendPermutedTemplateGlobalSource 0
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula) =
  embedPAFormula dynamicTruthZeroInputGlobalSigmaApplicationFormula.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma coqFourStateTableAppendPermutedTemplateGlobalSource_zero_pi :
  coqFourStateTableAppendPermutedTemplateGlobalSource 1
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula) =
  embedPAFormula dynamicTruthZeroInputGlobalPiApplicationFormula.
Proof.
  vm_compute. reflexivity.
Qed.

(** Carrier-facing forms for arbitrary PA-agreeing translations. *)
Theorem rawTemplateFormula_zeroCanonicalPermutedGlobalSource_sigma : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource 0
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)) =
  rawQuotedFormulaCode M
    dynamicTruthZeroInputGlobalSigmaApplicationFormula.
Proof.
  intros M translation hagreement.
  rewrite coqFourStateTableAppendPermutedTemplateGlobalSource_zero_sigma.
  exact (rawTemplateFormula_embedPA hagreement
    dynamicTruthZeroInputGlobalSigmaApplicationFormula).
Qed.

Theorem rawTemplateFormula_zeroCanonicalPermutedGlobalSource_pi : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource 1
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)) =
  rawQuotedFormulaCode M
    dynamicTruthZeroInputGlobalPiApplicationFormula.
Proof.
  intros M translation hagreement.
  rewrite coqFourStateTableAppendPermutedTemplateGlobalSource_zero_pi.
  exact (rawTemplateFormula_embedPA hagreement
    dynamicTruthZeroInputGlobalPiApplicationFormula).
Qed.

(** Any append traversal which returns the two embedded-row permuted sources
    can be rebased directly onto a witnessed callback context.  The two raw
    conclusion rewrites happen before context merging, so no structural
    translation remains in the resulting global-root package. *)
Theorem
    raw_dynamicTruthZeroCanonicalGlobalApplicationRoots_of_permuted_append_pair :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall producerSourceContext sourceWitnessList sourceContext,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedPAGrowingTemplateLocalProofPairAtEmpty M producerSourceContext
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource 0
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)))
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource 1
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula))) ->
  RawDynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom M
    sourceContext
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalSigmaApplicationFormula)
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalPiApplicationFormula).
Proof.
  intros M hPA translation hagreement producerSourceContext
    sourceWitnessList sourceContext hsource hpair.
  rewrite (rawTemplateFormula_zeroCanonicalPermutedGlobalSource_sigma
    M translation hagreement) in hpair.
  rewrite (rawTemplateFormula_zeroCanonicalPermutedGlobalSource_pi
    M translation hagreement) in hpair.
  exact
    (raw_dynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom_of_rebased_growing_pair
      M hPA producerSourceContext sourceWitnessList sourceContext
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalSigmaApplicationFormula)
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalPiApplicationFormula)
      hsource hpair).
Qed.

(** Primitive inputs consumed by one polarity of the canonical reversed
    append traversal.  Compared with the shared-row package used by positive
    levels, the row formulas are literal embedded PA syntax, so no opaque
    selector or output-code equation is retained. *)
Definition RawDynamicTruthZeroCanonicalPermutedAppendInputsAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  exists modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep : TemplateTerm,
  exists appendRoot : M,
    (rootMode = 0 \/ rootMode = 1) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (rawTemplateFormula translation
        (coqFourStateTableAppendExistsTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter coqDynamicTruthAppendRowBoundParameterName)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 2) (ttVar 1) (ttVar 0))) appendRoot /\
    RawCodedPAGrowingTemplateLocalProofAt M translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (coqFourStateTableAppendWitnessContext
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter coqDynamicTruthAppendRowBoundParameterName)
        (embedPATerm (Term.numeral rootMode))
        (ttVar 2) (ttVar 1) (ttVar 0) nil)
      (rawTemplateFormula translation
        (templateAnd7Seventh
          (coqFourStateTableAppendOpenedPermutedTemplateGlobalFormula
            rootMode
            (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
            (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
            (ttParameter coqDynamicTruthAppendRowBoundParameterName)))).

Arguments RawDynamicTruthZeroCanonicalPermutedAppendInputsAt
  M translation rootMode witnesses : clear implicits.

(** Prefix-preserving primitive package.  The append-existence proof remains
    on the witnessed PA tail because it is independent of the predecessor
    assumptions; only the seventh-field traversal proof must genuinely live
    beneath the retained caller prefix. *)
Definition RawDynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  exists modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep : TemplateTerm,
  exists appendRoot : M,
    (rootMode = 0 \/ rootMode = 1) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (rawTemplateFormula translation
        (coqFourStateTableAppendExistsTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter coqDynamicTruthAppendRowBoundParameterName)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 2) (ttVar 1) (ttVar 0))) appendRoot /\
    RawCodedPAGrowingTemplateLocalProofAt M translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (coqFourStateTableAppendWitnessContext
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter coqDynamicTruthAppendRowBoundParameterName)
        (embedPATerm (Term.numeral rootMode))
        (ttVar 2) (ttVar 1) (ttVar 0) outerPrefix)
      (rawTemplateFormula translation
        (templateAnd7Seventh
          (coqFourStateTableAppendOpenedPermutedTemplateGlobalFormula
            rootMode
            (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
            (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
            (ttParameter coqDynamicTruthAppendRowBoundParameterName)))).

Arguments RawDynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt
  M translation rootMode outerPrefix witnesses : clear implicits.

(** Reversing the three exposed global arguments does not change the
    canonical row law.  Both installed local rows are closed with respect to
    those outer arguments; kernel normalization audits that fact for the two
    legal root modes. *)
Lemma coqFourStateTableAppendOpenedPermutedZeroCanonicalRows_eq : forall
    rootMode bound,
  rootMode = 0 \/ rootMode = 1 ->
  coqFourStateTableAppendOpenedPermutedTemplateGlobalRows rootMode
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula) bound =
  coqFourStateTableAppendOpenedTemplateGlobalRows rootMode
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula) bound.
Proof.
  intros rootMode bound [-> | ->]; vm_compute; reflexivity.
Qed.

(** The concrete canonical row pair is exactly the opened production selected
    by either legal root mode.  Keeping this small kernel-computed fact next
    to the canonical rows removes a redundant syntax equality from every
    proof-producing resource package. *)
Lemma coqFourStateTableAppendZeroCanonicalRowProduction_eq : forall
    rootMode bound,
  rootMode = 0 \/ rootMode = 1 ->
  coqFourStateTableAppendConcreteClosedRowProductionTemplate
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula) =
    coqFourStateTableAppendOpenedTemplateGlobalRowProduction rootMode
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula) bound.
Proof.
  intros rootMode bound [-> | ->]; vm_compute; reflexivity.
Qed.

(** Earlier, more primitive row boundary.  Instead of assuming the already
    universally closed seventh field, it asks only for the concrete
    two-premise row implication in the exact context obtained after the
    append witnesses and five row eigenvariables have shifted the caller
    prefix.  Universal closure and permutation normalization are compiled by
    the adapter below. *)
Definition
    RawDynamicTruthZeroCanonicalPermutedAppendRowImplicationInputsUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  exists modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep : TemplateTerm,
  exists appendRoot : M,
    (rootMode = 0 \/ rootMode = 1) /\
    coqFourStateTableAppendConcreteClosedRowProductionTemplate
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula) =
      coqFourStateTableAppendOpenedTemplateGlobalRowProduction rootMode
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
        (ttParameter coqDynamicTruthAppendRowBoundParameterName) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (rawTemplateFormula translation
        (coqFourStateTableAppendExistsTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter coqDynamicTruthAppendRowBoundParameterName)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 2) (ttVar 1) (ttVar 0))) appendRoot /\
    RawCodedPAGrowingTemplateLocalProofAt M translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (templateContextShiftMany 5
        (coqFourStateTableAppendWitnessContext
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter coqDynamicTruthAppendRowBoundParameterName)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 2) (ttVar 1) (ttVar 0) outerPrefix))
      (rawTemplateFormula translation
        (tfImp
          (coqLtSuccCasesAntecedentTemplate
            (ttVar 4)
            (ttParameter coqDynamicTruthAppendRowBoundParameterName))
          (tfImp
            (coqFourStateTableAppendEqualityRowLookupTemplate
              coqFourStateTableAppendRowModeParameterName
              coqFourStateTableAppendRowFormulaParameterName
              coqFourStateTableAppendRowAssignmentCodeParameterName
              coqFourStateTableAppendRowAssignmentStepParameterName
              (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0))
            (coqFourStateTableAppendConcreteClosedRowProductionTemplate
              (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
              (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula))))).

Arguments
  RawDynamicTruthZeroCanonicalPermutedAppendRowImplicationInputsUnderPrefixAt
  M translation rootMode outerPrefix witnesses : clear implicits.

(** Proof-producing kernel beneath the completed row implication.  Arithmetic
    case splitting and the two implication introductions are structural
    consequences; the caller only supplies append existence, the inherited
    traversal/lookup pair, and the fixed canonical production at the literal
    suffix-preserving row context. *)
Definition
    RawDynamicTruthZeroCanonicalPermutedAppendRowKernelInputsUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  exists appendRoot fixedProductionRoot : M,
  exists inheritedTraversal oldLookup : TemplateFormula,
    (rootMode = 0 \/ rootMode = 1) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (rawTemplateFormula translation
        (coqFourStateTableAppendExistsTemplate
          (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
          (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
          (ttParameter coqDynamicTruthAppendRowBoundParameterName)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 2) (ttVar 1) (ttVar 0))) appendRoot /\
    templateUniversalOpenMany inheritedTraversal
      coqFourStateTableAppendConcreteRowVariables =
      Some
        (tfImp
          (coqLtSuccCasesBelowTemplate
            (ttVar 4)
            (ttParameter coqDynamicTruthAppendRowBoundParameterName))
          (tfImp oldLookup
            (coqFourStateTableAppendConcreteClosedRowProductionTemplate
              (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
              (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)))) /\
    RawFourStateTableAppendInheritedLocalRootsAt M translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (templateContextShiftMany 5
        (coqFourStateTableAppendWitnessContext
          (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
          (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
          (ttParameter coqDynamicTruthAppendRowBoundParameterName)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 2) (ttVar 1) (ttVar 0) outerPrefix))
      inheritedTraversal oldLookup /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses (raw_zero M))
        (templateContextShiftMany 5
          (coqFourStateTableAppendWitnessContext
            (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
            (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
            (ttParameter coqDynamicTruthAppendRowBoundParameterName)
            (embedPATerm (Term.numeral rootMode))
            (ttVar 2) (ttVar 1) (ttVar 0) outerPrefix)))
      (rawTemplateFormula translation
        (templateFormulaOpen (embedPATerm (Term.numeral rootMode))
          (coqFourStateTableAppendEmbeddedModeProductionMotive
            dynamicTruthZeroCanonicalSigmaRowFormula
            dynamicTruthZeroCanonicalPiRowFormula)))
      fixedProductionRoot.

Arguments
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelInputsUnderPrefixAt
  M translation rootMode outerPrefix witnesses : clear implicits.

(** Proof-producing content of a canonical row kernel, separated from the
    finite legal-mode side condition.  Clients fixed at modes zero and one
    should expose this payload: the disjunction is then supplied once by the
    adapters below instead of being repeated in every model-local producer. *)
Definition
    RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  exists appendRoot fixedProductionRoot : M,
  exists inheritedTraversal oldLookup : TemplateFormula,
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (rawTemplateFormula translation
        (coqFourStateTableAppendExistsTemplate
          (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
          (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
          (ttParameter coqDynamicTruthAppendRowBoundParameterName)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 2) (ttVar 1) (ttVar 0))) appendRoot /\
    templateUniversalOpenMany inheritedTraversal
      coqFourStateTableAppendConcreteRowVariables =
      Some
        (tfImp
          (coqLtSuccCasesBelowTemplate
            (ttVar 4)
            (ttParameter coqDynamicTruthAppendRowBoundParameterName))
          (tfImp oldLookup
            (coqFourStateTableAppendConcreteClosedRowProductionTemplate
              (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
              (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)))) /\
    RawFourStateTableAppendInheritedLocalRootsAt M translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (templateContextShiftMany 5
        (coqFourStateTableAppendWitnessContext
          (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
          (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
          (ttParameter coqDynamicTruthAppendRowBoundParameterName)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 2) (ttVar 1) (ttVar 0) outerPrefix))
      inheritedTraversal oldLookup /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses (raw_zero M))
        (templateContextShiftMany 5
          (coqFourStateTableAppendWitnessContext
            (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
            (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
            (ttParameter coqDynamicTruthAppendRowBoundParameterName)
            (embedPATerm (Term.numeral rootMode))
            (ttVar 2) (ttVar 1) (ttVar 0) outerPrefix)))
      (rawTemplateFormula translation
        (templateFormulaOpen (embedPATerm (Term.numeral rootMode))
          (coqFourStateTableAppendEmbeddedModeProductionMotive
            dynamicTruthZeroCanonicalSigmaRowFormula
            dynamicTruthZeroCanonicalPiRowFormula)))
      fixedProductionRoot.

Arguments
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
  M translation rootMode outerPrefix witnesses : clear implicits.

(** The append coordinate of every canonical row payload is now produced
    internally.  Keeping the witnessed-context certificate in the result is
    stronger than the payload projection itself: subsequent compilers may
    select their own finite witness batches and use the standard surrounding
    transport theorem to synchronize all coordinates afterward. *)
Theorem
    raw_dynamicTruthZeroCanonicalPermutedAppendRoot_on_standardWitnessTail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall rootMode,
  exists (witnesses : StandardPAAxiomWitnessPrefix) (appendRoot : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (rawTemplateFormula translation
        (coqFourStateTableAppendExistsTemplate
          (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
          (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
          (ttParameter coqDynamicTruthAppendRowBoundParameterName)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 2) (ttVar 1) (ttVar 0))) appendRoot.
Proof.
  intros M hPA translation hagreement rootMode.
  exact
    (raw_codedPALocalProofOf_canonical_four_state_table_append_exists_on_witnessed_tail
      M hPA translation hagreement
      (raw_zero M) (raw_zero M)
      coqDynamicTruthAppendRowBoundParameterName rootMode
      (raw_codedPAAxiomWitnessContext_empty M hPA)).
Qed.

(** A canonical row payload is monotone in its finite batch of standard PA
    witnesses.  The caller may add witnesses on either side of the original
    batch; all four represented roots are transported while the local row
    prefix and its two syntactic formulas remain unchanged.  This is the
    useful general form for independently compiled Sigma and Pi branches,
    whose witness batches need not have been coordinated in advance. *)
Theorem
    raw_dynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt_standardWitnessTail_surround :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall
    rootMode outerPrefix witnesses prefix suffix,
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
    M translation rootMode outerPrefix witnesses ->
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
    M translation rootMode outerPrefix
      (prefix ++ (witnesses ++ suffix)).
Proof.
  intros M hPA translation hagreement
    rootMode outerPrefix witnesses prefix suffix
    (appendRoot & fixedProductionRoot & inheritedTraversal & oldLookup &
      happend & hopen &
      (traversalRoot & oldLookupRoot & htraversal & holdLookup) &
      hfixedProduction).
  set (rowPrefix :=
    templateContextShiftMany 5
      (coqFourStateTableAppendWitnessContext
        (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
        (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
        (ttParameter coqDynamicTruthAppendRowBoundParameterName)
        (embedPATerm (Term.numeral rootMode))
        (ttVar 2) (ttVar 1) (ttVar 0) outerPrefix)).
  assert (happendSource : RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (embedPAContext (map witnessedAxiom witnesses)))
      (rawTemplateFormula translation
        (coqFourStateTableAppendExistsTemplate
          (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
          (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
          (ttParameter coqDynamicTruthAppendRowBoundParameterName)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 2) (ttVar 1) (ttVar 0))) appendRoot).
  {
    rewrite (raw_templateContextCode_embedPAAxiomWitnesses
      M translation hagreement witnesses).
    exact happend.
  }
  destruct
    (raw_codedPALocalProof_standardWitnessTail_surround_under_prefix
      M hPA translation hagreement nil prefix witnesses suffix
      (rawTemplateFormula translation
        (coqFourStateTableAppendExistsTemplate
          (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
          (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
          (ttParameter coqDynamicTruthAppendRowBoundParameterName)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 2) (ttVar 1) (ttVar 0)))
      appendRoot happendSource)
    as [transportedAppendRoot htransportedAppend].
  cbn [List.app] in htransportedAppend.
  rewrite (raw_templateContextCode_embedPAAxiomWitnesses
    M translation hagreement (prefix ++ (witnesses ++ suffix)))
    in htransportedAppend.
  assert (hbase : RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))).
  {
    pose proof (raw_templateEmbeddedPAAxiomWitnessContext
      M hPA translation hagreement witnesses) as hwitnessed.
    rewrite (raw_templateContextCode_embedPAAxiomWitnesses
      M translation hagreement witnesses) in hwitnessed.
    exact hwitnessed.
  }
  assert (htarget : RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        (prefix ++ (witnesses ++ suffix)) (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        (prefix ++ (witnesses ++ suffix)) (raw_zero M))).
  {
    pose proof (raw_templateEmbeddedPAAxiomWitnessContext
      M hPA translation hagreement
      (prefix ++ (witnesses ++ suffix))) as hwitnessed.
    rewrite (raw_templateContextCode_embedPAAxiomWitnesses
      M translation hagreement (prefix ++ (witnesses ++ suffix)))
      in hwitnessed.
    exact hwitnessed.
  }
  assert (hincluded : RawContextListIncluded M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        (prefix ++ (witnesses ++ suffix)) (raw_zero M))).
  {
    pose proof
      (raw_templateEmbeddedPAAxiomWitnessContext_surrounded_included
        M hPA translation hagreement prefix witnesses suffix)
      as hsurrounded.
    rewrite (raw_templateContextCode_embedPAAxiomWitnesses
      M translation hagreement witnesses) in hsurrounded.
    rewrite (raw_templateContextCode_embedPAAxiomWitnesses
      M translation hagreement (prefix ++ (witnesses ++ suffix)))
      in hsurrounded.
    exact hsurrounded.
  }
  assert (hlocalRoots : RawFourStateTableAppendInheritedLocalRootsAt
      M translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      rowPrefix inheritedTraversal oldLookup).
  {
    exists traversalRoot, oldLookupRoot.
    fold rowPrefix in htraversal, holdLookup.
    exact (conj htraversal holdLookup).
  }
  pose proof
    (raw_fourStateTableAppendInheritedLocalRootsAt_transport
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        (prefix ++ (witnesses ++ suffix)) (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        (prefix ++ (witnesses ++ suffix)) (raw_zero M))
      rowPrefix inheritedTraversal oldLookup
      hbase htarget hincluded hlocalRoots)
    as htransportedLocalRoots.
  assert (hfixedProductionSource : RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (rowPrefix ++ embedPAContext (map witnessedAxiom witnesses)))
      (rawTemplateFormula translation
        (templateFormulaOpen (embedPATerm (Term.numeral rootMode))
          (coqFourStateTableAppendEmbeddedModeProductionMotive
            dynamicTruthZeroCanonicalSigmaRowFormula
            dynamicTruthZeroCanonicalPiRowFormula)))
      fixedProductionRoot).
  {
    rewrite raw_templateContextCode_app_on_tail_general.
    rewrite (raw_templateContextCode_embedPAAxiomWitnesses
      M translation hagreement witnesses).
    fold rowPrefix in hfixedProduction.
    exact hfixedProduction.
  }
  destruct
    (raw_codedPALocalProof_standardWitnessTail_surround_under_prefix
      M hPA translation hagreement rowPrefix prefix witnesses suffix
      (rawTemplateFormula translation
        (templateFormulaOpen (embedPATerm (Term.numeral rootMode))
          (coqFourStateTableAppendEmbeddedModeProductionMotive
            dynamicTruthZeroCanonicalSigmaRowFormula
            dynamicTruthZeroCanonicalPiRowFormula)))
      fixedProductionRoot hfixedProductionSource)
    as [transportedFixedProductionRoot htransportedFixedProduction].
  rewrite raw_templateContextCode_app_on_tail_general
    in htransportedFixedProduction.
  rewrite (raw_templateContextCode_embedPAAxiomWitnesses
    M translation hagreement (prefix ++ (witnesses ++ suffix)))
    in htransportedFixedProduction.
  exists transportedAppendRoot, transportedFixedProductionRoot,
    inheritedTraversal, oldLookup.
  split; [exact htransportedAppend |].
  split; [exact hopen |].
  split.
  - fold rowPrefix in htransportedLocalRoots.
    exact htransportedLocalRoots.
  - fold rowPrefix in htransportedFixedProduction.
    exact htransportedFixedProduction.
Qed.

Theorem
    raw_dynamicTruthZeroCanonicalPermutedAppendRowKernelInputsUnderPrefixAt_of_payload :
  forall (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    rootMode outerPrefix witnesses,
  rootMode = 0 \/ rootMode = 1 ->
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
    M translation rootMode outerPrefix witnesses ->
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelInputsUnderPrefixAt
    M translation rootMode outerPrefix witnesses.
Proof.
  intros M translation rootMode outerPrefix witnesses hrootMode
    (appendRoot & fixedProductionRoot & inheritedTraversal & oldLookup &
      happend & hopen & hinherited & hfixedProduction).
  exists appendRoot, fixedProductionRoot, inheritedTraversal, oldLookup.
  split; [exact hrootMode |].
  split; [exact happend |].
  split; [exact hopen |].
  split; [exact hinherited | exact hfixedProduction].
Qed.

Corollary
    raw_dynamicTruthZeroCanonicalSigmaPermutedAppendRowKernelInputsUnderPrefixAt_of_payload :
  forall (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    outerPrefix witnesses,
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
    M translation 0 outerPrefix witnesses ->
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelInputsUnderPrefixAt
    M translation 0 outerPrefix witnesses.
Proof.
  intros M translation outerPrefix witnesses hpayload.
  exact
    (raw_dynamicTruthZeroCanonicalPermutedAppendRowKernelInputsUnderPrefixAt_of_payload
      M translation 0 outerPrefix witnesses (or_introl eq_refl) hpayload).
Qed.

Corollary
    raw_dynamicTruthZeroCanonicalPiPermutedAppendRowKernelInputsUnderPrefixAt_of_payload :
  forall (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    outerPrefix witnesses,
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
    M translation 1 outerPrefix witnesses ->
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelInputsUnderPrefixAt
    M translation 1 outerPrefix witnesses.
Proof.
  intros M translation outerPrefix witnesses hpayload.
  exact
    (raw_dynamicTruthZeroCanonicalPermutedAppendRowKernelInputsUnderPrefixAt_of_payload
      M translation 1 outerPrefix witnesses (or_intror eq_refl) hpayload).
Qed.

(** Both canonical polarities share the same finite PA witness batch.  This
    package is independent of a particular normalized callback invocation;
    it can therefore be constructed once per model and reused at every
    rank-zero trace. *)
Definition
    RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadPairUnderPrefix
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (outerPrefix : TemplateContext) : Prop :=
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
      M translation 0 outerPrefix witnesses /\
    RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
      M translation 1 outerPrefix witnesses.

Arguments
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadPairUnderPrefix
  M translation outerPrefix : clear implicits.

(** Weak producer-facing form of the payload pair.  Each polarity may choose
    its own finite standard witness batch; synchronization is a consequence,
    not an obligation imposed on the two branch compilers. *)
Definition
    RawDynamicTruthZeroCanonicalIndependentPermutedAppendRowKernelPayloadsUnderPrefix
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (outerPrefix : TemplateContext) : Prop :=
  (exists sigmaWitnesses : StandardPAAxiomWitnessPrefix,
    RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
      M translation 0 outerPrefix sigmaWitnesses) /\
  (exists piWitnesses : StandardPAAxiomWitnessPrefix,
    RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
      M translation 1 outerPrefix piWitnesses).

Arguments
  RawDynamicTruthZeroCanonicalIndependentPermutedAppendRowKernelPayloadsUnderPrefix
  M translation outerPrefix : clear implicits.

(** Synchronize independently compiled canonical Sigma and Pi payloads by
    surrounding both standard witness batches with the other branch's
    witnesses.  The common batch is their concatenation; no equality between
    the original batches and no preselected common proof roots is required. *)
Theorem
    raw_dynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadPairUnderPrefix_of_independent_witnesses :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall
    outerPrefix sigmaWitnesses piWitnesses,
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
    M translation 0 outerPrefix sigmaWitnesses ->
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
    M translation 1 outerPrefix piWitnesses ->
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadPairUnderPrefix
    M translation outerPrefix.
Proof.
  intros M hPA translation hagreement outerPrefix
    sigmaWitnesses piWitnesses hsigma hpi.
  exists (sigmaWitnesses ++ piWitnesses).
  split.
  - change (RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
      M translation 0 outerPrefix
        (nil ++ (sigmaWitnesses ++ piWitnesses))).
    exact
      (raw_dynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt_standardWitnessTail_surround
        M hPA translation hagreement 0 outerPrefix sigmaWitnesses
        nil piWitnesses hsigma).
  - replace (sigmaWitnesses ++ piWitnesses) with
      (sigmaWitnesses ++ (piWitnesses ++ nil))
      by now rewrite List.app_nil_r.
    exact
      (raw_dynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt_standardWitnessTail_surround
        M hPA translation hagreement 1 outerPrefix piWitnesses
        sigmaWitnesses nil hpi).
Qed.

(** Eliminate the weak independent package into the synchronized payload
    pair used by the row compiler. *)
Corollary
    raw_dynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadPairUnderPrefix_of_independent_payloads :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall outerPrefix,
  RawDynamicTruthZeroCanonicalIndependentPermutedAppendRowKernelPayloadsUnderPrefix
    M translation outerPrefix ->
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadPairUnderPrefix
    M translation outerPrefix.
Proof.
  intros M hPA translation hagreement outerPrefix
    [[sigmaWitnesses hsigma] [piWitnesses hpi]].
  exact
    (raw_dynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadPairUnderPrefix_of_independent_witnesses
      M hPA translation hagreement outerPrefix
      sigmaWitnesses piWitnesses hsigma hpi).
Qed.

(** Compile the three-root canonical kernel through the suffix-preserving
    arithmetic case split. *)
Theorem
    raw_dynamicTruthZeroCanonicalPermutedAppendRowImplicationInputsUnderPrefixAt_of_kernel :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode outerPrefix witnesses,
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelInputsUnderPrefixAt
    M translation rootMode outerPrefix witnesses ->
  RawDynamicTruthZeroCanonicalPermutedAppendRowImplicationInputsUnderPrefixAt
    M translation rootMode outerPrefix witnesses.
Proof.
  intros M hPA translation hagreement rootMode outerPrefix witnesses
    (appendRoot & fixedProductionRoot & inheritedTraversal & oldLookup &
      hrootMode & happend & hopen & hinherited & hfixedProduction).
  exists (ttVar 7), (ttVar 6), (ttVar 5), (ttVar 4),
    (ttVar 3), (ttVar 2), (ttVar 1), (ttVar 0), appendRoot.
  split; [exact hrootMode |].
  split.
  - exact (coqFourStateTableAppendZeroCanonicalRowProduction_eq
      rootMode (ttParameter coqDynamicTruthAppendRowBoundParameterName)
      hrootMode).
  - split; [exact happend |].
    exact
      (raw_codedPALocalProofOf_four_state_table_append_concrete_global_closed_row_implications_on_literal_row_context_under_suffix
        M hPA translation hagreement
        rootMode coqDynamicTruthAppendRowBoundParameterName
        dynamicTruthZeroCanonicalSigmaRowFormula
        dynamicTruthZeroCanonicalPiRowFormula witnesses outerPrefix
        (ttVar 2) (ttVar 1) (ttVar 0)
        (ttParameter coqDynamicTruthAppendRowBoundParameterName)
        inheritedTraversal oldLookup fixedProductionRoot
        hrootMode hopen
        (raw_codedTemplatePrefix_atomically_adequate M hPA translation _)
        (raw_codedTemplateFormula_atomically_adequate M hPA translation _)
        (raw_codedTemplateFormula_atomically_adequate M hPA translation _)
        (raw_codedTemplateFormula_atomically_adequate M hPA translation _)
        eq_refl
        (raw_codedTemplateFormula_atomically_adequate M hPA translation _)
        hinherited hfixedProduction).
Qed.

(** Literal-tail form consumed directly by the low-level append constructors.
    The caller prefix and the closed PA witness formulas are supplied as one
    template tail.  Unlike the growing package above, this interface does not
    ask the caller to choose a second witnessed target, prove reflexive tail
    inclusion, or normalize the thirteen-shift context code. *)
Definition
    RawDynamicTruthZeroCanonicalPermutedAppendLiteralRowImplicationInputsUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  exists modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep : TemplateTerm,
  exists appendRoot rowRoot : M,
    (rootMode = 0 \/ rootMode = 1) /\
    coqFourStateTableAppendConcreteClosedRowProductionTemplate
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula) =
      coqFourStateTableAppendOpenedTemplateGlobalRowProduction rootMode
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
        (ttParameter coqDynamicTruthAppendRowBoundParameterName) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (rawTemplateFormula translation
        (coqFourStateTableAppendExistsTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter coqDynamicTruthAppendRowBoundParameterName)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 2) (ttVar 1) (ttVar 0))) appendRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (templateContextShiftMany 5
          (coqFourStateTableAppendWitnessContext
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            (ttParameter coqDynamicTruthAppendRowBoundParameterName)
            (embedPATerm (Term.numeral rootMode))
            (ttVar 2) (ttVar 1) (ttVar 0)
            (outerPrefix ++ embedPAContext
              (map witnessedAxiom witnesses)))))
      (rawTemplateFormula translation
        (tfImp
          (coqLtSuccCasesAntecedentTemplate
            (ttVar 4)
            (ttParameter coqDynamicTruthAppendRowBoundParameterName))
          (tfImp
            (coqFourStateTableAppendEqualityRowLookupTemplate
              coqFourStateTableAppendRowModeParameterName
              coqFourStateTableAppendRowFormulaParameterName
              coqFourStateTableAppendRowAssignmentCodeParameterName
              coqFourStateTableAppendRowAssignmentStepParameterName
              (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0))
            (coqFourStateTableAppendConcreteClosedRowProductionTemplate
              (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
              (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)))))
      rowRoot.

Arguments
  RawDynamicTruthZeroCanonicalPermutedAppendLiteralRowImplicationInputsUnderPrefixAt
  M translation rootMode outerPrefix witnesses : clear implicits.

(** Normalize a literal-tail row proof into the synchronized growing package.
    All proof-producing content is preserved verbatim; only its context
    presentation changes. *)
Theorem
    raw_dynamicTruthZeroCanonicalPermutedAppendRowImplicationInputsUnderPrefixAt_of_literal :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode outerPrefix witnesses,
  RawDynamicTruthZeroCanonicalPermutedAppendLiteralRowImplicationInputsUnderPrefixAt
    M translation rootMode outerPrefix witnesses ->
  RawDynamicTruthZeroCanonicalPermutedAppendRowImplicationInputsUnderPrefixAt
    M translation rootMode outerPrefix witnesses.
Proof.
  intros M hPA translation hagreement rootMode outerPrefix witnesses
    (modeCode & modeStep & formulaCode & formulaStep &
      assignmentCodeCode & assignmentCodeStep &
      assignmentStepCode & assignmentStepStep & appendRoot & rowRoot &
      hrootMode & hproduction & happend & hrow).
  exists modeCode, modeStep, formulaCode, formulaStep,
    assignmentCodeCode, assignmentCodeStep,
    assignmentStepCode, assignmentStepStep, appendRoot.
  split; [exact hrootMode |].
  split; [exact hproduction |].
  split; [exact happend |].
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_of_local_on_append_row_context_under_prefix
      M hPA translation hagreement
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter coqDynamicTruthAppendRowBoundParameterName)
      (embedPATerm (Term.numeral rootMode))
      (ttVar 2) (ttVar 1) (ttVar 0) outerPrefix witnesses
      (rawTemplateFormula translation
        (tfImp
          (coqLtSuccCasesAntecedentTemplate
            (ttVar 4)
            (ttParameter coqDynamicTruthAppendRowBoundParameterName))
          (tfImp
            (coqFourStateTableAppendEqualityRowLookupTemplate
              coqFourStateTableAppendRowModeParameterName
              coqFourStateTableAppendRowFormulaParameterName
              coqFourStateTableAppendRowAssignmentCodeParameterName
              coqFourStateTableAppendRowAssignmentStepParameterName
              (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0))
            (coqFourStateTableAppendConcreteClosedRowProductionTemplate
              (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
              (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)))))
      rowRoot hrow).
Qed.

(** Close the five row binders and identify the unchanged permuted seventh
    field.  This is pure structural proof compilation; the only genuinely
    proof-producing input remains the concrete row implication above. *)
Theorem
    raw_dynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt_of_row_implication_inputs :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  forall rootMode outerPrefix witnesses,
  RawDynamicTruthZeroCanonicalPermutedAppendRowImplicationInputsUnderPrefixAt
    M translation rootMode outerPrefix witnesses ->
  RawDynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt
    M translation rootMode outerPrefix witnesses.
Proof.
  intros M hPA translation rootMode outerPrefix witnesses
    (modeCode & modeStep & formulaCode & formulaStep &
      assignmentCodeCode & assignmentCodeStep &
      assignmentStepCode & assignmentStepStep & appendRoot &
      hrootMode & hproduction & happend & hrow).
  exists modeCode, modeStep, formulaCode, formulaStep,
    assignmentCodeCode, assignmentCodeStep,
    assignmentStepCode, assignmentStepStep, appendRoot.
  split; [exact hrootMode |].
  split; [exact happend |].
  pose proof
    (raw_codedPAGrowingTemplateLocalProofAt_opened_template_global_rows_of_concrete_row_at_root_terms_under_prefix
      M hPA translation rootMode
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
      coqDynamicTruthAppendRowBoundParameterName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttVar 2) (ttVar 1) (ttVar 0)
      outerPrefix witnesses
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
      hproduction hrow) as hclosedRows.
  change (RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (coqFourStateTableAppendWitnessContext
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter coqDynamicTruthAppendRowBoundParameterName)
      (embedPATerm (Term.numeral rootMode))
      (ttVar 2) (ttVar 1) (ttVar 0) outerPrefix)
    (rawTemplateFormula translation
      (coqFourStateTableAppendOpenedPermutedTemplateGlobalRows rootMode
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
        (ttParameter coqDynamicTruthAppendRowBoundParameterName)))).
  rewrite (coqFourStateTableAppendOpenedPermutedZeroCanonicalRows_eq
    rootMode (ttParameter coqDynamicTruthAppendRowBoundParameterName)
    hrootMode).
  exact hclosedRows.
Qed.

(** Close one polarity without discharging the caller prefix.  The generic
    prefix inserter places the append-existence proof beneath that prefix;
    the prefix-preserving eight-witness eliminator then returns the global
    application in the same state-dependent context. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_permuted_global_of_inputs_under_prefix :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode outerPrefix witnesses,
  RawCodedTemplatePrefixAtomicallyAdequate M translation outerPrefix ->
  RawDynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt
    M translation rootMode outerPrefix witnesses ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)) outerPrefix
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource rootMode
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula))).
Proof.
  intros M hPA translation hagreement rootMode outerPrefix witnesses
    hprefix
    (modeCode & modeStep & formulaCode & formulaStep &
      assignmentCodeCode & assignmentCodeStep &
      assignmentStepCode & assignmentStepStep & appendRoot &
      hrootMode & happend & hrows).
  assert (hbase : RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))).
  {
    pose proof (raw_templateEmbeddedPAAxiomWitnessContext
      M hPA translation hagreement witnesses) as hbaseTemplate.
    rewrite (raw_templateContextCode_embedPAAxiomWitnesses
      M translation hagreement witnesses) in hbaseTemplate.
    exact hbaseTemplate.
  }
  pose proof
    (raw_codedPAAxiomWitnessContext_context_realizable M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) hbase) as hbaseRealizable.
  destruct
    (raw_codedPALocalProof_templatePrefix M hPA translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) outerPrefix
      (rawTemplateFormula translation
        (coqFourStateTableAppendExistsTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter coqDynamicTruthAppendRowBoundParameterName)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 2) (ttVar 1) (ttVar 0)))
      appendRoot hbaseRealizable hprefix happend)
    as [prefixedAppendRoot hprefixedAppend].
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_permuted_template_global_of_append_rows_under_prefix
      M hPA translation hagreement rootMode
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
      coqDynamicTruthAppendRowBoundParameterName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep outerPrefix witnesses
      prefixedAppendRoot hrootMode hprefixedAppend hrows).
Qed.

(** Synchronize both state-dependent polarities without dropping their
    common prefix. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofPairAt_dynamic_truth_zero_canonical_permuted_globals_of_inputs_under_prefix :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall outerPrefix witnesses,
  RawCodedTemplatePrefixAtomicallyAdequate M translation outerPrefix ->
  RawDynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt
    M translation 0 outerPrefix witnesses ->
  RawDynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt
    M translation 1 outerPrefix witnesses ->
  RawCodedPAGrowingTemplateLocalProofPairAt M translation
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)) outerPrefix
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource 0
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)))
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource 1
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula))).
Proof.
  intros M hPA translation hagreement outerPrefix witnesses
    hprefix hsigma hpi.
  apply
    (raw_codedPAGrowingTemplateLocalProofAt_pair_at_prefix
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) outerPrefix).
  - exact
      (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_permuted_global_of_inputs_under_prefix
        M hPA translation hagreement 0 outerPrefix witnesses
        hprefix hsigma).
  - exact
      (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_permuted_global_of_inputs_under_prefix
        M hPA translation hagreement 1 outerPrefix witnesses
        hprefix hpi).
Qed.

(** Rebase the synchronized append result onto the caller's witnessed tail
    and normalize its two conclusions to the literal canonical application
    codes. *)
Theorem
    raw_dynamicTruthZeroCanonicalApplicationPair_of_permuted_append_inputs_under_prefix :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall outerPrefix witnesses sourceWitnessList sourceContext,
  RawCodedTemplatePrefixAtomicallyAdequate M translation outerPrefix ->
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawDynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt
    M translation 0 outerPrefix witnesses ->
  RawDynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt
    M translation 1 outerPrefix witnesses ->
  RawCodedPAGrowingTemplateLocalProofPairAt M translation
    sourceContext outerPrefix
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalSigmaApplicationFormula)
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalPiApplicationFormula).
Proof.
  intros M hPA translation hagreement outerPrefix witnesses
    sourceWitnessList sourceContext hprefix hsource hsigma hpi.
  pose proof
    (raw_codedPAGrowingTemplateLocalProofPairAt_dynamic_truth_zero_canonical_permuted_globals_of_inputs_under_prefix
      M hPA translation hagreement outerPrefix witnesses
      hprefix hsigma hpi) as hpair.
  rewrite (rawTemplateFormula_zeroCanonicalPermutedGlobalSource_sigma
    M translation hagreement) in hpair.
  rewrite (rawTemplateFormula_zeroCanonicalPermutedGlobalSource_pi
    M translation hagreement) in hpair.
  exact
    (raw_codedPAGrowingTemplateLocalProofPairAt_rebase
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) outerPrefix
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalSigmaApplicationFormula)
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalPiApplicationFormula)
      sourceWitnessList sourceContext hsource hpair).
Qed.

(** Canonical rank-zero client.  The only temporary assumptions retained by
    the append traversal are the two predecessor-state membership formulas.
    Their atomic adequacy follows uniformly from PA agreement, so callers do
    not need to repeat that structural side condition. *)
Theorem
    raw_dynamicTruthZeroCanonicalStateApplicationPair_of_permuted_append_inputs :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnesses sourceWitnessList sourceContext,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawDynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt
    M translation 0 coqDynamicTruthPredecessorStateTemplateContext
      witnesses ->
  RawDynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt
    M translation 1 coqDynamicTruthPredecessorStateTemplateContext
      witnesses ->
  RawCodedPAGrowingTemplateLocalProofPairAt M translation
    sourceContext coqDynamicTruthPredecessorStateTemplateContext
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalSigmaApplicationFormula)
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalPiApplicationFormula).
Proof.
  intros M hPA translation hagreement witnesses
    sourceWitnessList sourceContext hsource hsigma hpi.
  exact
    (raw_dynamicTruthZeroCanonicalApplicationPair_of_permuted_append_inputs_under_prefix
      M hPA translation hagreement
      coqDynamicTruthPredecessorStateTemplateContext witnesses
      sourceWitnessList sourceContext
      (raw_dynamicTruthPredecessorStateTemplateContext_atomically_adequate
        M hPA translation hagreement)
      hsource hsigma hpi).
Qed.

(** Close one canonical polarity from its primitive append package. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_permuted_global_of_inputs :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode witnesses,
  RawDynamicTruthZeroCanonicalPermutedAppendInputsAt M translation
    rootMode witnesses ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)) nil
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource rootMode
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula))).
Proof.
  intros M hPA translation hagreement rootMode witnesses
    (modeCode & modeStep & formulaCode & formulaStep &
      assignmentCodeCode & assignmentCodeStep &
      assignmentStepCode & assignmentStepStep & appendRoot &
      hrootMode & happend & hrows).
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_permuted_template_global_of_append_rows
      M hPA translation hagreement rootMode
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
      coqDynamicTruthAppendRowBoundParameterName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep witnesses appendRoot
      hrootMode happend hrows).
Qed.

(** Synchronize the two canonical append polarities at their shared standard
    witness-prefix source. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofPairAtEmpty_dynamic_truth_zero_canonical_permuted_globals_of_inputs :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnesses,
  RawDynamicTruthZeroCanonicalPermutedAppendInputsAt M translation
    0 witnesses ->
  RawDynamicTruthZeroCanonicalPermutedAppendInputsAt M translation
    1 witnesses ->
  RawCodedPAGrowingTemplateLocalProofPairAtEmpty M
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource 0
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)))
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource 1
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula))).
Proof.
  intros M hPA translation hagreement witnesses hsigma hpi.
  apply (raw_codedPAGrowingTemplateLocalProofAt_pair_at_empty
    M hPA translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))).
  - exact
      (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_permuted_global_of_inputs
        M hPA translation hagreement 0 witnesses hsigma).
  - exact
      (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_permuted_global_of_inputs
        M hPA translation hagreement 1 witnesses hpi).
Qed.

(** Public handoff from two primitive append packages to the exact canonical
    global roots beneath any witnessed predecessor callback base. *)
Theorem
    raw_dynamicTruthZeroCanonicalGlobalApplicationRoots_of_permuted_append_inputs :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnesses sourceWitnessList sourceContext,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawDynamicTruthZeroCanonicalPermutedAppendInputsAt M translation
    0 witnesses ->
  RawDynamicTruthZeroCanonicalPermutedAppendInputsAt M translation
    1 witnesses ->
  RawDynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom M
    sourceContext
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalSigmaApplicationFormula)
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalPiApplicationFormula).
Proof.
  intros M hPA translation hagreement witnesses sourceWitnessList
    sourceContext hsource hsigma hpi.
  exact
    (raw_dynamicTruthZeroCanonicalGlobalApplicationRoots_of_permuted_append_pair
      M hPA translation hagreement
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      sourceWitnessList sourceContext hsource
      (raw_codedPAGrowingTemplateLocalProofPairAtEmpty_dynamic_truth_zero_canonical_permuted_globals_of_inputs
        M hPA translation hagreement witnesses hsigma hpi)).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalAppendSourceIdentification.
