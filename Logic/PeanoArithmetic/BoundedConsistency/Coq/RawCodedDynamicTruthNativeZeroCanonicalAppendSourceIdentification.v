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
  RawCodedContextLists
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplateBottomDirectStructuralInputs
  RawCodedRestrictedPAProof
  RawCodedPAProofLeafCertificates
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedPALocalProofExistentialEliminationChain
  RawCodedPALocalProofUniversalIntroductionChain
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedLtSuccCasesProofCompilation
  RawCodedPAGrowingTemplateConjunction
  RawCodedPAGrowingTemplateRebase
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
  RawCodedDynamicTruthNativeZeroCanonicalTraceExactification
  RawCodedStrongStepPredecessorGlobalRowEvidenceCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalAppendSourceIdentification.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateBottomDirectStructuralInputs.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProofLeafCertificates.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedPAGrowingTemplateConjunction.
Import PABoundedRawCodedPAGrowingTemplateRebase.
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
Import PABoundedRawCodedStrongStepPredecessorGlobalRowEvidenceCompilation.

(** Literal local rows used by the first global successor. *)
Definition dynamicTruthZeroCanonicalSigmaRowFormula : formula :=
  dynamicTruthSigmaSuccessorRowFormula (Term.numeral 1)
    dynamicTruthGlobalPiBaseFormula.

Definition dynamicTruthZeroCanonicalPiRowFormula : formula :=
  dynamicTruthPiSuccessorRowFormula (Term.numeral 1)
    dynamicTruthGlobalSigmaBaseFormula.

(** Expose the fixed-production target as the named native closed-row
    formula.  This is the exact bridge between the template-facing append
    compiler and the formula-facing fixed-level truth API. *)
Lemma coqFourStateTableAppendZeroCanonicalFixedProduction_native : forall
    rootMode,
  templateFormulaOpen (embedPATerm (Term.numeral rootMode))
    (coqFourStateTableAppendEmbeddedModeProductionMotive
      dynamicTruthZeroCanonicalSigmaRowFormula
      dynamicTruthZeroCanonicalPiRowFormula) =
  embedPAFormula
    (dynamicTruthZeroClosedSuccessorRowFormula
      (Term.numeral rootMode)).
Proof.
  intro rootMode.
  rewrite coqFourStateTableAppendEmbeddedModeProductionMotive_open.
  unfold dynamicTruthZeroClosedSuccessorRowFormula,
    dynamicTruthZeroCanonicalSigmaRowFormula,
    dynamicTruthZeroCanonicalPiRowFormula.
  reflexivity.
Qed.

(** Carrier-level spelling for every PA-agreeing template translation. *)
Theorem rawTemplateFormula_zeroCanonicalFixedProduction_native : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall rootMode,
  rawTemplateFormula translation
    (templateFormulaOpen (embedPATerm (Term.numeral rootMode))
      (coqFourStateTableAppendEmbeddedModeProductionMotive
        dynamicTruthZeroCanonicalSigmaRowFormula
        dynamicTruthZeroCanonicalPiRowFormula)) =
  rawQuotedFormulaCode M
    (dynamicTruthZeroClosedSuccessorRowFormula
      (Term.numeral rootMode)).
Proof.
  intros M translation hagreement rootMode.
  rewrite coqFourStateTableAppendZeroCanonicalFixedProduction_native.
  exact (rawTemplateFormula_embedPA hagreement
    (dynamicTruthZeroClosedSuccessorRowFormula
      (Term.numeral rootMode))).
Qed.

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

(** The append-existence formula and the row context share the same thirteen
    temporary coordinates throughout this file.  Naming their root-term
    parametric forms keeps the guarded [#2,#6,#5] instance honest and avoids
    repeating the binder-sensitive context expression in every interface. *)
Definition coqDynamicTruthZeroCanonicalAppendExistsTemplateAtRootTerms
    (rootMode : nat)
    (rootFormula rootAssignmentCode rootAssignmentStep : TemplateTerm)
    : TemplateFormula :=
  coqFourStateTableAppendExistsTemplate
    (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
    (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
    (ttParameter coqDynamicTruthAppendRowBoundParameterName)
    (embedPATerm (Term.numeral rootMode))
    rootFormula rootAssignmentCode rootAssignmentStep.

Definition coqDynamicTruthZeroCanonicalAppendRowContextAtRootTerms
    (rootMode : nat)
    (rootFormula rootAssignmentCode rootAssignmentStep : TemplateTerm)
    (outerPrefix : TemplateContext) : TemplateContext :=
  templateContextShiftMany 5
    (coqFourStateTableAppendWitnessContext
      (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
      (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName)
      (embedPATerm (Term.numeral rootMode))
      rootFormula rootAssignmentCode rootAssignmentStep outerPrefix).

(** Primitive inputs consumed by one polarity of the canonical append
    traversal at arbitrary exposed root terms.  Compared with the shared-row
    package used by positive levels, the row formulas are literal embedded
    PA syntax, so no opaque selector or output-code equation is retained. *)
Definition RawDynamicTruthZeroCanonicalAppendInputsAtRootTermsAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat)
    (rootFormula rootAssignmentCode rootAssignmentStep : TemplateTerm)
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
          rootFormula rootAssignmentCode rootAssignmentStep)) appendRoot /\
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
        rootFormula rootAssignmentCode rootAssignmentStep nil)
      (rawTemplateFormula translation
        (coqFourStateTableAppendOpenedTemplateGlobalRowsAtRootTerms
          rootMode
          (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
          (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
          rootFormula rootAssignmentCode rootAssignmentStep
          (ttParameter coqDynamicTruthAppendRowBoundParameterName))).

Arguments RawDynamicTruthZeroCanonicalAppendInputsAtRootTermsAt
  M translation rootMode rootFormula rootAssignmentCode rootAssignmentStep
  witnesses : clear implicits.

(** Historical reversed-coordinate spelling.  Its surface type is retained
    verbatim rather than defined as a transparent alias: protected ternary
    application identifies the generic seventh field only propositionally
    when [rootMode] is still abstract.  Keeping this compatibility boundary
    avoids changing the reducible goal seen by existing clients. *)
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
Definition RawDynamicTruthZeroCanonicalAppendInputsAtRootTermsUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext)
    (rootFormula rootAssignmentCode rootAssignmentStep : TemplateTerm)
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
          rootFormula rootAssignmentCode rootAssignmentStep)) appendRoot /\
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
        rootFormula rootAssignmentCode rootAssignmentStep outerPrefix)
      (rawTemplateFormula translation
        (coqFourStateTableAppendOpenedTemplateGlobalRowsAtRootTerms
          rootMode
          (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
          (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
          rootFormula rootAssignmentCode rootAssignmentStep
          (ttParameter coqDynamicTruthAppendRowBoundParameterName))).

Arguments RawDynamicTruthZeroCanonicalAppendInputsAtRootTermsUnderPrefixAt
  M translation rootMode outerPrefix rootFormula rootAssignmentCode
  rootAssignmentStep witnesses : clear implicits.

(** Prefix-preserving historical compatibility boundary; see the empty-prefix
    spelling above for why this one deliberately repeats its old surface
    proposition instead of unfolding the protected generic application. *)
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

(** Protected ternary application leaves the two embedded canonical rows
    unchanged at the historical exposed tuple.  This finite syntax fact is
    deliberately concrete: unrestricted opaque local templates need not be
    stable under arbitrary root-term substitution. *)
Lemma
    coqFourStateTableAppendOpenedAtRootTermsZeroCanonicalRows_permuted_eq :
  forall rootMode bound,
  coqFourStateTableAppendOpenedTemplateGlobalRowsAtRootTerms rootMode
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
      (ttVar 2) (ttVar 1) (ttVar 0) bound =
  coqFourStateTableAppendOpenedTemplateGlobalRows rootMode
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula) bound.
Proof.
  intros [|[|rootMode]] bound; vm_compute; reflexivity.
Qed.

(** Guarded callbacks expose assignment code and assignment step at [#6]
    and [#5].  The same closed canonical row pair is stable at that layout,
    giving the exact bridge from the generic row compiler to the protected
    AtRootTerms seventh field consumed by guarded append reconstruction. *)
Lemma
    coqFourStateTableAppendOpenedAtRootTermsZeroCanonicalRows_guarded_eq :
  forall rootMode bound,
  coqFourStateTableAppendOpenedTemplateGlobalRowsAtRootTerms rootMode
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
      (ttVar 2) (ttVar 6) (ttVar 5) bound =
  coqFourStateTableAppendOpenedTemplateGlobalRows rootMode
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula) bound.
Proof.
  intros [|[|rootMode]] bound; vm_compute; reflexivity.
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
    RawDynamicTruthZeroCanonicalAppendRowImplicationInputsAtRootTermsUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext)
    (rootFormula rootAssignmentCode rootAssignmentStep : TemplateTerm)
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
          rootFormula rootAssignmentCode rootAssignmentStep)) appendRoot /\
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
          rootFormula rootAssignmentCode rootAssignmentStep outerPrefix))
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
  RawDynamicTruthZeroCanonicalAppendRowImplicationInputsAtRootTermsUnderPrefixAt
  M translation rootMode outerPrefix rootFormula rootAssignmentCode
  rootAssignmentStep witnesses : clear implicits.

Definition
    RawDynamicTruthZeroCanonicalPermutedAppendRowImplicationInputsUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawDynamicTruthZeroCanonicalAppendRowImplicationInputsAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    (ttVar 2) (ttVar 1) (ttVar 0) witnesses.

Arguments
  RawDynamicTruthZeroCanonicalPermutedAppendRowImplicationInputsUnderPrefixAt
  M translation rootMode outerPrefix witnesses : clear implicits.

(** Proof-producing kernel beneath the completed row implication.  Arithmetic
    case splitting and the two implication introductions are structural
    consequences; the caller only supplies append existence, the inherited
    traversal/lookup pair, and the fixed canonical production at the literal
    suffix-preserving row context. *)
Definition
    RawDynamicTruthZeroCanonicalAppendRowKernelInputsAtRootTermsUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext)
    (rootFormula rootAssignmentCode rootAssignmentStep : TemplateTerm)
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
          rootFormula rootAssignmentCode rootAssignmentStep)) appendRoot /\
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
          rootFormula rootAssignmentCode rootAssignmentStep outerPrefix))
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
            rootFormula rootAssignmentCode rootAssignmentStep outerPrefix)))
      (rawTemplateFormula translation
        (templateFormulaOpen (embedPATerm (Term.numeral rootMode))
          (coqFourStateTableAppendEmbeddedModeProductionMotive
            dynamicTruthZeroCanonicalSigmaRowFormula
            dynamicTruthZeroCanonicalPiRowFormula)))
      fixedProductionRoot.

Arguments
  RawDynamicTruthZeroCanonicalAppendRowKernelInputsAtRootTermsUnderPrefixAt
  M translation rootMode outerPrefix rootFormula rootAssignmentCode
  rootAssignmentStep witnesses : clear implicits.

Definition
    RawDynamicTruthZeroCanonicalPermutedAppendRowKernelInputsUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawDynamicTruthZeroCanonicalAppendRowKernelInputsAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    (ttVar 2) (ttVar 1) (ttVar 0) witnesses.

Arguments
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelInputsUnderPrefixAt
  M translation rootMode outerPrefix witnesses : clear implicits.

(** A harmless theorem is used as the old-row lookup in the rank-zero
    traversal.  The strict-lower premise is impossible when the bottom
    structural translation interprets the append bound as zero, so no
    semantic lookup fact is consumed.  Choosing [bottom -> bottom] keeps the
    lookup independently provable in every represented context. *)
Definition coqDynamicTruthZeroCanonicalVacuousOldLookupTemplate
    : TemplateFormula :=
  tfImp tfBot tfBot.

Definition coqDynamicTruthZeroCanonicalVacuousInheritedRowBodyTemplate
    : TemplateFormula :=
  tfImp
    (coqLtSuccCasesBelowTemplate
      (ttVar 4)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName))
    (tfImp coqDynamicTruthZeroCanonicalVacuousOldLookupTemplate
      (coqFourStateTableAppendConcreteClosedRowProductionTemplate
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula))).

(** The two fixed local-row formulas refer to variables outside the five
    traversal binders.  Protect precisely that production suffix by five
    shifts; the row-index and lookup spine intentionally remains bound. *)
Definition coqDynamicTruthZeroCanonicalVacuousInheritedBoundRowBodyTemplate
    : TemplateFormula :=
  tfImp
    (coqLtSuccCasesBelowTemplate
      (ttVar 4)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName))
    (tfImp coqDynamicTruthZeroCanonicalVacuousOldLookupTemplate
      (templateFormulaShiftMany 5
        (coqFourStateTableAppendConcreteClosedRowProductionTemplate
          (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
          (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)))).

Definition coqDynamicTruthZeroCanonicalVacuousInheritedTraversalTemplate
    : TemplateFormula :=
  templateFormulaAllMany 5
    coqDynamicTruthZeroCanonicalVacuousInheritedBoundRowBodyTemplate.

(** Opening the five binders at their canonical de Bruijn variables is the
    identity on the row body.  Keeping this calculation named prevents the
    payload constructor from hiding a binder-sensitive kernel reduction. *)
Lemma
    coqDynamicTruthZeroCanonicalVacuousInheritedTraversalTemplate_open :
  templateUniversalOpenMany
    coqDynamicTruthZeroCanonicalVacuousInheritedTraversalTemplate
    coqFourStateTableAppendConcreteRowVariables =
  Some coqDynamicTruthZeroCanonicalVacuousInheritedRowBodyTemplate.
Proof. reflexivity. Qed.

(** The no-less-than-zero antecedent compiled by the arithmetic helper is
    exactly the append below-branch when the latter's bound is literal zero. *)
Lemma coqNoLtZeroAntecedentTemplate_append_below_zero :
  coqNoLtZeroAntecedentTemplate (ttVar 4) =
  coqLtSuccCasesBelowTemplate (ttVar 4) ttZero.
Proof. reflexivity. Qed.

(** Under the bottom direct translation the reserved append-bound parameter
    denotes zero.  This carrier-level bridge is independent of the exposed
    root tuple and is therefore shared by canonical and guarded inherited-row
    producers. *)
Lemma
    raw_dynamicTruthZeroCanonicalBottom_append_below_parameter_zero_for_root_terms :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  rawTemplateFormula (rawBottomDirectStructuralTemplateTranslation M hPA)
    (coqLtSuccCasesBelowTemplate
      (ttVar 4)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName)) =
  rawTemplateFormula (rawBottomDirectStructuralTemplateTranslation M hPA)
    (coqNoLtZeroAntecedentTemplate (ttVar 4)).
Proof.
  intros M hPA.
  rewrite coqNoLtZeroAntecedentTemplate_append_below_zero.
  reflexivity.
Qed.

(** Intermediate row resource after append existence and inherited traversal
    have been compiled, but before the fixed-mode production is attached.
    This factors the two independent proof-producing phases and lets the
    second phase grow the witnessed PA tail without reconstructing either
    inherited root. *)
Definition
    RawDynamicTruthZeroCanonicalAppendInheritedRowResourcesAtRootTermsUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext)
    (rootFormula rootAssignmentCode rootAssignmentStep : TemplateTerm)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  exists appendRoot : M,
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
          rootFormula rootAssignmentCode rootAssignmentStep)) appendRoot /\
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
          rootFormula rootAssignmentCode rootAssignmentStep outerPrefix))
      inheritedTraversal oldLookup.

Arguments
  RawDynamicTruthZeroCanonicalAppendInheritedRowResourcesAtRootTermsUnderPrefixAt
  M translation rootMode outerPrefix rootFormula rootAssignmentCode
  rootAssignmentStep witnesses : clear implicits.

Definition
    RawDynamicTruthZeroCanonicalPermutedAppendInheritedRowResourcesUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawDynamicTruthZeroCanonicalAppendInheritedRowResourcesAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    (ttVar 2) (ttVar 1) (ttVar 0) witnesses.

Arguments
  RawDynamicTruthZeroCanonicalPermutedAppendInheritedRowResourcesUnderPrefixAt
  M translation rootMode outerPrefix witnesses : clear implicits.

(** The only proof-producing coordinate not contained in the inherited-row
    package is the row selected by the fixed root mode.  Its compiler starts
    from an arbitrary honestly witnessed PA tail and may prepend one further
    finite batch of standard PA helpers.  This growing form is deliberately
    weaker than asking a producer to predict the append compiler's witness
    batch or to reconstruct the append and inherited roots itself. *)
Definition
    RawDynamicTruthZeroCanonicalGrowingFixedProductionCompilerAtRootTermsUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext)
    (rootFormula rootAssignmentCode rootAssignmentStep : TemplateTerm) : Prop :=
  forall sourceWitnessList sourceContext,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix)
      (fixedProductionRoot : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses sourceWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses sourceContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses sourceContext)
        (templateContextShiftMany 5
          (coqFourStateTableAppendWitnessContext
            (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
            (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
            (ttParameter coqDynamicTruthAppendRowBoundParameterName)
            (embedPATerm (Term.numeral rootMode))
            rootFormula rootAssignmentCode rootAssignmentStep outerPrefix)))
      (rawTemplateFormula translation
        (templateFormulaOpen (embedPATerm (Term.numeral rootMode))
          (coqFourStateTableAppendEmbeddedModeProductionMotive
            dynamicTruthZeroCanonicalSigmaRowFormula
            dynamicTruthZeroCanonicalPiRowFormula)))
      fixedProductionRoot.

Arguments
  RawDynamicTruthZeroCanonicalGrowingFixedProductionCompilerAtRootTermsUnderPrefixAt
  M translation rootMode outerPrefix rootFormula rootAssignmentCode
  rootAssignmentStep : clear implicits.

Definition
    RawDynamicTruthZeroCanonicalGrowingFixedProductionCompilerUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext) : Prop :=
  RawDynamicTruthZeroCanonicalGrowingFixedProductionCompilerAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    (ttVar 2) (ttVar 1) (ttVar 0).

Arguments
  RawDynamicTruthZeroCanonicalGrowingFixedProductionCompilerUnderPrefixAt
  M translation rootMode outerPrefix : clear implicits.

(** A producer need not build the large selected successor row when the
    temporary append context is already contradictory.  This disjunctive
    interface is strictly weaker than the fixed-production compiler above:
    every old producer chooses the left branch, while a bottom-specific
    collision argument may choose the right branch and share one compact
    refutation across otherwise unrelated row conclusions. *)
Definition
    RawDynamicTruthZeroCanonicalGrowingFixedProductionOrRefutationCompilerAtRootTermsUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext)
    (rootFormula rootAssignmentCode rootAssignmentStep : TemplateTerm) : Prop :=
  forall sourceWitnessList sourceContext,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) (sourceRoot : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses sourceWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses sourceContext) /\
    (RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses sourceContext)
        (templateContextShiftMany 5
          (coqFourStateTableAppendWitnessContext
            (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
            (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
            (ttParameter coqDynamicTruthAppendRowBoundParameterName)
            (embedPATerm (Term.numeral rootMode))
            rootFormula rootAssignmentCode rootAssignmentStep outerPrefix)))
      (rawTemplateFormula translation
        (templateFormulaOpen (embedPATerm (Term.numeral rootMode))
          (coqFourStateTableAppendEmbeddedModeProductionMotive
            dynamicTruthZeroCanonicalSigmaRowFormula
            dynamicTruthZeroCanonicalPiRowFormula))) sourceRoot \/
     RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses sourceContext)
        (templateContextShiftMany 5
          (coqFourStateTableAppendWitnessContext
            (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
            (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
            (ttParameter coqDynamicTruthAppendRowBoundParameterName)
            (embedPATerm (Term.numeral rootMode))
            rootFormula rootAssignmentCode rootAssignmentStep outerPrefix)))
      (rawFormulaBotCode M) sourceRoot).

Arguments
  RawDynamicTruthZeroCanonicalGrowingFixedProductionOrRefutationCompilerAtRootTermsUnderPrefixAt
  M translation rootMode outerPrefix rootFormula rootAssignmentCode
  rootAssignmentStep : clear implicits.

Definition
    RawDynamicTruthZeroCanonicalGrowingFixedProductionOrRefutationCompilerUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext) : Prop :=
  RawDynamicTruthZeroCanonicalGrowingFixedProductionOrRefutationCompilerAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    (ttVar 2) (ttVar 1) (ttVar 0).

Arguments
  RawDynamicTruthZeroCanonicalGrowingFixedProductionOrRefutationCompilerUnderPrefixAt
  M translation rootMode outerPrefix : clear implicits.

(** Retain an additional caller suffix below the complete temporary append
    context.  The append eliminator introduces eight witnesses and the row
    proof introduces five binders, so the suffix is renamed thirteen times.
    The generic template-suffix lemma inserts those renamed assumptions at
    the exact represented depth and transports either disjunct uniformly.

    This specialization uses the canonical bottom direct translation, whose
    structural adequacy theorem covers every translated temporary formula.
    It therefore asks callers for no separate syntactic side condition. *)
Theorem
    raw_dynamicTruthZeroCanonicalGrowingFixedProductionOrRefutationCompilerAtRootTermsUnderPrefixAt_app
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      rootMode outerPrefix callerSuffix
      rootFormula rootAssignmentCode rootAssignmentStep,
  RawDynamicTruthZeroCanonicalGrowingFixedProductionOrRefutationCompilerAtRootTermsUnderPrefixAt
    M (rawBottomDirectStructuralTemplateTranslation M hPA)
      rootMode outerPrefix
      rootFormula rootAssignmentCode rootAssignmentStep ->
  RawDynamicTruthZeroCanonicalGrowingFixedProductionOrRefutationCompilerAtRootTermsUnderPrefixAt
    M (rawBottomDirectStructuralTemplateTranslation M hPA)
      rootMode (outerPrefix ++ callerSuffix)
      rootFormula rootAssignmentCode rootAssignmentStep.
Proof.
  intros M hPA rootMode outerPrefix callerSuffix
    rootFormula rootAssignmentCode rootAssignmentStep hcompiler
    sourceWitnessList sourceContext hsource.
  destruct (hcompiler sourceWitnessList sourceContext hsource) as
    (witnesses & sourceRoot & hextended & hsourceProof).
  set (translation := rawBottomDirectStructuralTemplateTranslation M hPA).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M witnesses sourceContext).
  set (oldPrefix := templateContextShiftMany 5
    (coqFourStateTableAppendWitnessContext
      (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
      (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName)
      (embedPATerm (Term.numeral rootMode))
      rootFormula rootAssignmentCode rootAssignmentStep outerPrefix)).
  set (newPrefix := templateContextShiftMany 5
    (coqFourStateTableAppendWitnessContext
      (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
      (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName)
      (embedPATerm (Term.numeral rootMode))
      rootFormula rootAssignmentCode rootAssignmentStep
      (outerPrefix ++ callerSuffix))).
  assert (hprefixShape :
      oldPrefix ++ templateContextShiftMany 13 callerSuffix = newPrefix).
  {
    unfold oldPrefix, newPrefix.
    rewrite !coqFourStateTableAppendRowContext_affine.
    rewrite templateContextShiftMany_app.
    rewrite <- app_assoc. reflexivity.
  }
  assert (hcombinedAdequate :
      RawCodedTemplatePrefixAtomicallyAdequate M translation
        (oldPrefix ++ templateContextShiftMany 13 callerSuffix)).
  {
    rewrite hprefixShape.
    exact (raw_directStructuralTemplatePrefix_atomically_adequate
      M hPA (rawBottomTemplateDirectStructuralInputs M hPA) newPrefix).
  }
  assert (hextendedRealizable : RawContextListRealizable M extendedContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses sourceWitnessList)
      extendedContext hextended).
  }
  destruct hsourceProof as [hproduction | hrefutation].
  - destruct
      (raw_codedPALocalProof_templateSuffix
        M hPA translation extendedContext oldPrefix
        (templateContextShiftMany 13 callerSuffix)
        (rawTemplateFormula translation
          (templateFormulaOpen (embedPATerm (Term.numeral rootMode))
            (coqFourStateTableAppendEmbeddedModeProductionMotive
              dynamicTruthZeroCanonicalSigmaRowFormula
              dynamicTruthZeroCanonicalPiRowFormula)))
        sourceRoot hextendedRealizable hcombinedAdequate hproduction)
      as [targetRoot htarget].
    exists witnesses, targetRoot. split; [exact hextended |].
    left. unfold translation, extendedContext in htarget |- *.
    rewrite hprefixShape in htarget. exact htarget.
  - destruct
      (raw_codedPALocalProof_templateSuffix
        M hPA translation extendedContext oldPrefix
        (templateContextShiftMany 13 callerSuffix)
        (rawFormulaBotCode M) sourceRoot
        hextendedRealizable hcombinedAdequate hrefutation)
      as [targetRoot htarget].
    exists witnesses, targetRoot. split; [exact hextended |].
    right. unfold translation, extendedContext in htarget |- *.
    rewrite hprefixShape in htarget. exact htarget.
Qed.

(** Backward-compatible reversed-coordinate specialization. *)
Corollary
    raw_dynamicTruthZeroCanonicalGrowingFixedProductionOrRefutationCompilerUnderPrefixAt_app
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      rootMode outerPrefix callerSuffix,
  RawDynamicTruthZeroCanonicalGrowingFixedProductionOrRefutationCompilerUnderPrefixAt
    M (rawBottomDirectStructuralTemplateTranslation M hPA)
      rootMode outerPrefix ->
  RawDynamicTruthZeroCanonicalGrowingFixedProductionOrRefutationCompilerUnderPrefixAt
    M (rawBottomDirectStructuralTemplateTranslation M hPA)
      rootMode (outerPrefix ++ callerSuffix).
Proof.
  intros M hPA rootMode outerPrefix callerSuffix hcompiler.
  exact
    (raw_dynamicTruthZeroCanonicalGrowingFixedProductionOrRefutationCompilerAtRootTermsUnderPrefixAt_app
      M hPA rootMode outerPrefix callerSuffix
      (ttVar 2) (ttVar 1) (ttVar 0) hcompiler).
Qed.

(** Represented bottom elimination is the only extra proof node needed to
    turn the relaxed source interface back into the exact fixed-production
    interface consumed by append synchronization. *)
Theorem
    raw_dynamicTruthZeroCanonicalGrowingFixedProductionCompilerAtRootTermsUnderPrefixAt_of_production_or_refutation
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M) rootMode outerPrefix
      rootFormula rootAssignmentCode rootAssignmentStep,
  RawDynamicTruthZeroCanonicalGrowingFixedProductionOrRefutationCompilerAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep ->
  RawDynamicTruthZeroCanonicalGrowingFixedProductionCompilerAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep.
Proof.
  intros M hPA translation rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep hcompiler
    sourceWitnessList sourceContext hsource.
  destruct (hcompiler sourceWitnessList sourceContext hsource) as
    (witnesses & sourceRoot & hextended & [hproduction | hrefutation]).
  - exists witnesses, sourceRoot. split; assumption.
  - exists witnesses. eexists.
    split; [exact hextended |].
    exact (raw_codedPALocalProofOf_botE M hPA
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses sourceContext)
        (templateContextShiftMany 5
          (coqFourStateTableAppendWitnessContext
            (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
            (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
            (ttParameter coqDynamicTruthAppendRowBoundParameterName)
            (embedPATerm (Term.numeral rootMode))
            rootFormula rootAssignmentCode rootAssignmentStep outerPrefix)))
      sourceRoot hrefutation
      (rawTemplateFormula translation
        (templateFormulaOpen (embedPATerm (Term.numeral rootMode))
          (coqFourStateTableAppendEmbeddedModeProductionMotive
            dynamicTruthZeroCanonicalSigmaRowFormula
            dynamicTruthZeroCanonicalPiRowFormula)))).
Qed.

Corollary
    raw_dynamicTruthZeroCanonicalGrowingFixedProductionCompilerUnderPrefixAt_of_production_or_refutation
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M) rootMode outerPrefix,
  RawDynamicTruthZeroCanonicalGrowingFixedProductionOrRefutationCompilerUnderPrefixAt
    M translation rootMode outerPrefix ->
  RawDynamicTruthZeroCanonicalGrowingFixedProductionCompilerUnderPrefixAt
    M translation rootMode outerPrefix.
Proof.
  intros M hPA translation rootMode outerPrefix hcompiler.
  exact
    (raw_dynamicTruthZeroCanonicalGrowingFixedProductionCompilerAtRootTermsUnderPrefixAt_of_production_or_refutation
      M hPA translation rootMode outerPrefix
      (ttVar 2) (ttVar 1) (ttVar 0) hcompiler).
Qed.

(** The two polarities may independently choose direct production or
    refutation and may still allocate unrelated helper batches. *)
Definition
    RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionOrRefutationCompilersAtRootTermsUnderPrefix
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (outerPrefix : TemplateContext)
    (rootFormula rootAssignmentCode rootAssignmentStep : TemplateTerm) : Prop :=
  RawDynamicTruthZeroCanonicalGrowingFixedProductionOrRefutationCompilerAtRootTermsUnderPrefixAt
    M translation 0 outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep /\
  RawDynamicTruthZeroCanonicalGrowingFixedProductionOrRefutationCompilerAtRootTermsUnderPrefixAt
    M translation 1 outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep.

Arguments
  RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionOrRefutationCompilersAtRootTermsUnderPrefix
  M translation outerPrefix rootFormula rootAssignmentCode
  rootAssignmentStep : clear implicits.

Definition
    RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionOrRefutationCompilersUnderPrefix
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (outerPrefix : TemplateContext) : Prop :=
  RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionOrRefutationCompilersAtRootTermsUnderPrefix
    M translation outerPrefix (ttVar 2) (ttVar 1) (ttVar 0).

Arguments
  RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionOrRefutationCompilersUnderPrefix
  M translation outerPrefix : clear implicits.

(** Extend both independent polarity compilers by the same retained caller
    suffix.  Their standard-witness batches remain independent; only the
    visible temporary context is enlarged. *)
Corollary
    raw_dynamicTruthZeroCanonicalIndependentGrowingFixedProductionOrRefutationCompilersAtRootTermsUnderPrefix_app
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      outerPrefix callerSuffix
      rootFormula rootAssignmentCode rootAssignmentStep,
  RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionOrRefutationCompilersAtRootTermsUnderPrefix
    M (rawBottomDirectStructuralTemplateTranslation M hPA) outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep ->
  RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionOrRefutationCompilersAtRootTermsUnderPrefix
    M (rawBottomDirectStructuralTemplateTranslation M hPA)
      (outerPrefix ++ callerSuffix)
      rootFormula rootAssignmentCode rootAssignmentStep.
Proof.
  intros M hPA outerPrefix callerSuffix
    rootFormula rootAssignmentCode rootAssignmentStep [hsigma hpi]. split.
  - exact
      (raw_dynamicTruthZeroCanonicalGrowingFixedProductionOrRefutationCompilerAtRootTermsUnderPrefixAt_app
        M hPA 0 outerPrefix callerSuffix
        rootFormula rootAssignmentCode rootAssignmentStep hsigma).
  - exact
      (raw_dynamicTruthZeroCanonicalGrowingFixedProductionOrRefutationCompilerAtRootTermsUnderPrefixAt_app
        M hPA 1 outerPrefix callerSuffix
        rootFormula rootAssignmentCode rootAssignmentStep hpi).
Qed.

Corollary
    raw_dynamicTruthZeroCanonicalIndependentGrowingFixedProductionOrRefutationCompilersUnderPrefix_app
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      outerPrefix callerSuffix,
  RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionOrRefutationCompilersUnderPrefix
    M (rawBottomDirectStructuralTemplateTranslation M hPA) outerPrefix ->
  RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionOrRefutationCompilersUnderPrefix
    M (rawBottomDirectStructuralTemplateTranslation M hPA)
      (outerPrefix ++ callerSuffix).
Proof.
  intros M hPA outerPrefix callerSuffix hcompilers.
  exact
    (raw_dynamicTruthZeroCanonicalIndependentGrowingFixedProductionOrRefutationCompilersAtRootTermsUnderPrefix_app
      M hPA outerPrefix callerSuffix
      (ttVar 2) (ttVar 1) (ttVar 0) hcompilers).
Qed.

(** Sigma and Pi row construction may use different finite PA-helper batches.
    The payload synchronizer handles those batches later, so the weakest
    model-local interface is simply the conjunction of the two growing
    fixed-production compilers. *)
Definition
    RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionCompilersAtRootTermsUnderPrefix
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (outerPrefix : TemplateContext)
    (rootFormula rootAssignmentCode rootAssignmentStep : TemplateTerm) : Prop :=
  RawDynamicTruthZeroCanonicalGrowingFixedProductionCompilerAtRootTermsUnderPrefixAt
    M translation 0 outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep /\
  RawDynamicTruthZeroCanonicalGrowingFixedProductionCompilerAtRootTermsUnderPrefixAt
    M translation 1 outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep.

Arguments
  RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionCompilersAtRootTermsUnderPrefix
  M translation outerPrefix rootFormula rootAssignmentCode
  rootAssignmentStep : clear implicits.

Definition
    RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionCompilersUnderPrefix
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (outerPrefix : TemplateContext) : Prop :=
  RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionCompilersAtRootTermsUnderPrefix
    M translation outerPrefix (ttVar 2) (ttVar 1) (ttVar 0).

Arguments
  RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionCompilersUnderPrefix
  M translation outerPrefix : clear implicits.

Theorem
    raw_dynamicTruthZeroCanonicalIndependentGrowingFixedProductionCompilersAtRootTermsUnderPrefix_of_production_or_refutation
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M) outerPrefix
      rootFormula rootAssignmentCode rootAssignmentStep,
  RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionOrRefutationCompilersAtRootTermsUnderPrefix
    M translation outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep ->
  RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionCompilersAtRootTermsUnderPrefix
    M translation outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep.
Proof.
  intros M hPA translation outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep [hsigma hpi]. split.
  - exact
      (raw_dynamicTruthZeroCanonicalGrowingFixedProductionCompilerAtRootTermsUnderPrefixAt_of_production_or_refutation
        M hPA translation 0 outerPrefix
        rootFormula rootAssignmentCode rootAssignmentStep hsigma).
  - exact
      (raw_dynamicTruthZeroCanonicalGrowingFixedProductionCompilerAtRootTermsUnderPrefixAt_of_production_or_refutation
        M hPA translation 1 outerPrefix
        rootFormula rootAssignmentCode rootAssignmentStep hpi).
Qed.

Theorem
    raw_dynamicTruthZeroCanonicalIndependentGrowingFixedProductionCompilersUnderPrefix_of_production_or_refutation
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M) outerPrefix,
  RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionOrRefutationCompilersUnderPrefix
    M translation outerPrefix ->
  RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionCompilersUnderPrefix
    M translation outerPrefix.
Proof.
  intros M hPA translation outerPrefix hcompilers.
  exact
    (raw_dynamicTruthZeroCanonicalIndependentGrowingFixedProductionCompilersAtRootTermsUnderPrefix_of_production_or_refutation
      M hPA translation outerPrefix
      (ttVar 2) (ttVar 1) (ttVar 0) hcompilers).
Qed.

(** Proof-producing content of a canonical row kernel, separated from the
    finite legal-mode side condition.  Clients fixed at modes zero and one
    should expose this payload: the disjunction is then supplied once by the
    adapters below instead of being repeated in every model-local producer. *)
Definition
    RawDynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTermsUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext)
    (rootFormula rootAssignmentCode rootAssignmentStep : TemplateTerm)
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
          rootFormula rootAssignmentCode rootAssignmentStep)) appendRoot /\
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
          rootFormula rootAssignmentCode rootAssignmentStep outerPrefix))
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
            rootFormula rootAssignmentCode rootAssignmentStep outerPrefix)))
      (rawTemplateFormula translation
        (templateFormulaOpen (embedPATerm (Term.numeral rootMode))
          (coqFourStateTableAppendEmbeddedModeProductionMotive
            dynamicTruthZeroCanonicalSigmaRowFormula
            dynamicTruthZeroCanonicalPiRowFormula)))
      fixedProductionRoot.

Arguments
  RawDynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTermsUnderPrefixAt
  M translation rootMode outerPrefix rootFormula rootAssignmentCode
  rootAssignmentStep witnesses : clear implicits.

Definition
    RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawDynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    (ttVar 2) (ttVar 1) (ttVar 0) witnesses.

Arguments
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
  M translation rootMode outerPrefix witnesses : clear implicits.

(** Guarded predecessor callbacks retain two additional outer variables for
    assignment code and assignment step.  These transparent aliases expose
    their exact [formula,assignmentCode,assignmentStep] tuple [#2,#6,#5]
    without duplicating any proof-producing contract. *)
Definition
    RawDynamicTruthZeroCanonicalGuardedAppendInputsUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawDynamicTruthZeroCanonicalAppendInputsAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    (ttVar 2) (ttVar 6) (ttVar 5) witnesses.

Definition
    RawDynamicTruthZeroCanonicalGuardedAppendRowImplicationInputsUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawDynamicTruthZeroCanonicalAppendRowImplicationInputsAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    (ttVar 2) (ttVar 6) (ttVar 5) witnesses.

Definition
    RawDynamicTruthZeroCanonicalGuardedAppendInheritedRowResourcesUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawDynamicTruthZeroCanonicalAppendInheritedRowResourcesAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    (ttVar 2) (ttVar 6) (ttVar 5) witnesses.

Definition
    RawDynamicTruthZeroCanonicalGuardedGrowingFixedProductionCompilerUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext) : Prop :=
  RawDynamicTruthZeroCanonicalGrowingFixedProductionCompilerAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    (ttVar 2) (ttVar 6) (ttVar 5).

Definition
    RawDynamicTruthZeroCanonicalGuardedGrowingFixedProductionOrRefutationCompilerUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext) : Prop :=
  RawDynamicTruthZeroCanonicalGrowingFixedProductionOrRefutationCompilerAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    (ttVar 2) (ttVar 6) (ttVar 5).

Definition
    RawDynamicTruthZeroCanonicalGuardedIndependentGrowingFixedProductionCompilersUnderPrefix
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (outerPrefix : TemplateContext) : Prop :=
  RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionCompilersAtRootTermsUnderPrefix
    M translation outerPrefix (ttVar 2) (ttVar 6) (ttVar 5).

Definition
    RawDynamicTruthZeroCanonicalGuardedIndependentGrowingFixedProductionOrRefutationCompilersUnderPrefix
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (outerPrefix : TemplateContext) : Prop :=
  RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionOrRefutationCompilersAtRootTermsUnderPrefix
    M translation outerPrefix (ttVar 2) (ttVar 6) (ttVar 5).

Definition
    RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawDynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    (ttVar 2) (ttVar 6) (ttVar 5) witnesses.

Definition
    RawDynamicTruthZeroCanonicalGuardedAppendRowKernelInputsUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawDynamicTruthZeroCanonicalAppendRowKernelInputsAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    (ttVar 2) (ttVar 6) (ttVar 5) witnesses.

Arguments
  RawDynamicTruthZeroCanonicalGuardedAppendInputsUnderPrefixAt
  M translation rootMode outerPrefix witnesses : clear implicits.
Arguments
  RawDynamicTruthZeroCanonicalGuardedAppendRowImplicationInputsUnderPrefixAt
  M translation rootMode outerPrefix witnesses : clear implicits.
Arguments
  RawDynamicTruthZeroCanonicalGuardedAppendInheritedRowResourcesUnderPrefixAt
  M translation rootMode outerPrefix witnesses : clear implicits.
Arguments
  RawDynamicTruthZeroCanonicalGuardedGrowingFixedProductionCompilerUnderPrefixAt
  M translation rootMode outerPrefix : clear implicits.
Arguments
  RawDynamicTruthZeroCanonicalGuardedGrowingFixedProductionOrRefutationCompilerUnderPrefixAt
  M translation rootMode outerPrefix : clear implicits.
Arguments
  RawDynamicTruthZeroCanonicalGuardedIndependentGrowingFixedProductionCompilersUnderPrefix
  M translation outerPrefix : clear implicits.
Arguments
  RawDynamicTruthZeroCanonicalGuardedIndependentGrowingFixedProductionOrRefutationCompilersUnderPrefix
  M translation outerPrefix : clear implicits.
Arguments
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadUnderPrefixAt
  M translation rootMode outerPrefix witnesses : clear implicits.
Arguments
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelInputsUnderPrefixAt
  M translation rootMode outerPrefix witnesses : clear implicits.

(** Attach an independently growing fixed-production compiler to the three
    roots already present in the inherited-row package.  The production's
    helper batch is prepended to the inherited batch, and the earlier append,
    traversal, and lookup proofs are transported to that exact common tail.
    Thus the caller supplies only the genuinely missing row proof; witness
    synchronization is a theorem rather than part of the compiler contract. *)
Theorem
    raw_dynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTerms_on_standardWitnessTail_of_inherited_and_growing_fixed_production :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall
    rootMode outerPrefix rootFormula rootAssignmentCode rootAssignmentStep
    inheritedWitnesses,
  RawCodedPAAxiomWitnessContext M
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      inheritedWitnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      inheritedWitnesses (raw_zero M)) ->
  RawDynamicTruthZeroCanonicalAppendInheritedRowResourcesAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep inheritedWitnesses ->
  RawDynamicTruthZeroCanonicalGrowingFixedProductionCompilerAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep ->
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) /\
    RawDynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTermsUnderPrefixAt
      M translation rootMode outerPrefix
      rootFormula rootAssignmentCode rootAssignmentStep witnesses.
Proof.
  intros M hPA translation hagreement rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep
    inheritedWitnesses hinheritedWitnessed
    (appendRoot & inheritedTraversal & oldLookup &
      happend & hopen & hinheritedRoots)
    hfixedCompiler.
  set (inheritedWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      inheritedWitnesses (raw_zero M)).
  set (inheritedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      inheritedWitnesses (raw_zero M)).
  set (rowPrefix :=
    templateContextShiftMany 5
      (coqFourStateTableAppendWitnessContext
        (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
        (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
        (ttParameter coqDynamicTruthAppendRowBoundParameterName)
        (embedPATerm (Term.numeral rootMode))
        rootFormula rootAssignmentCode rootAssignmentStep outerPrefix)).
  destruct
    (hfixedCompiler inheritedWitnessList inheritedContext
      hinheritedWitnessed) as
    (productionWitnesses & fixedProductionRoot &
      hfinalWitnessed & hfixedProduction).
  assert (hincluded : RawContextListIncluded M inheritedContext
      (rawStandardPAAxiomWitnessPrefixContextCode M
        productionWitnesses inheritedContext)).
  {
    exact
      (raw_standardPAAxiomWitnessPrefixContextCode_target_included
        M hPA productionWitnesses inheritedContext).
  }
  destruct
    (raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix
      M hPA productionWitnesses inheritedContext
      (rawTemplateFormula translation
        (coqFourStateTableAppendExistsTemplate
          (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
          (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
          (ttParameter coqDynamicTruthAppendRowBoundParameterName)
          (embedPATerm (Term.numeral rootMode))
          rootFormula rootAssignmentCode rootAssignmentStep)) appendRoot
      (raw_codedPAAxiomWitnessContext_context_realizable M
        inheritedWitnessList inheritedContext hinheritedWitnessed)
      happend) as [transportedAppendRoot htransportedAppend].
  pose proof
    (raw_fourStateTableAppendInheritedLocalRootsAt_transport
      M hPA translation inheritedWitnessList inheritedContext
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        productionWitnesses inheritedWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        productionWitnesses inheritedContext)
      rowPrefix inheritedTraversal oldLookup
      hinheritedWitnessed hfinalWitnessed hincluded hinheritedRoots)
    as htransportedInheritedRoots.
  exists (productionWitnesses ++ inheritedWitnesses).
  split.
  - rewrite rawStandardPAAxiomWitnessPrefixWitnessListCode_app.
    rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
    exact hfinalWitnessed.
  - unfold
      RawDynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTermsUnderPrefixAt.
    rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
    exists transportedAppendRoot, fixedProductionRoot,
      inheritedTraversal, oldLookup.
    split.
    + fold inheritedContext in htransportedAppend.
      exact htransportedAppend.
    + split; [exact hopen |].
      split.
      * fold rowPrefix in htransportedInheritedRoots.
        exact htransportedInheritedRoots.
      * fold rowPrefix in hfixedProduction.
        exact hfixedProduction.
Qed.

(** Preserve the established permuted theorem as a specialization of the
    single root-term-parametric synchronization proof. *)
Corollary
    raw_dynamicTruthZeroCanonicalPermutedAppendRowKernelPayload_on_standardWitnessTail_of_inherited_and_growing_fixed_production :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall
    rootMode outerPrefix inheritedWitnesses,
  RawCodedPAAxiomWitnessContext M
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      inheritedWitnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      inheritedWitnesses (raw_zero M)) ->
  RawDynamicTruthZeroCanonicalPermutedAppendInheritedRowResourcesUnderPrefixAt
    M translation rootMode outerPrefix inheritedWitnesses ->
  RawDynamicTruthZeroCanonicalGrowingFixedProductionCompilerUnderPrefixAt
    M translation rootMode outerPrefix ->
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) /\
    RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
      M translation rootMode outerPrefix witnesses.
Proof.
  intros M hPA translation hagreement rootMode outerPrefix
    inheritedWitnesses hinheritedWitnessed hinherited hfixed.
  exact
    (raw_dynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTerms_on_standardWitnessTail_of_inherited_and_growing_fixed_production
      M hPA translation hagreement rootMode outerPrefix
      (ttVar 2) (ttVar 1) (ttVar 0) inheritedWitnesses
      hinheritedWitnessed hinherited hfixed).
Qed.

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

(** Guarded-coordinate append existence is equally unconditional.  Keeping
    this endpoint next to the historical producer makes the true remaining
    guarded obligation explicit: inherited traversal and fixed production,
    not beta-definedness of the exposed tuple. *)
Theorem
    raw_dynamicTruthZeroCanonicalGuardedAppendRoot_on_standardWitnessTail :
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
          (ttVar 2) (ttVar 6) (ttVar 5))) appendRoot.
Proof.
  intros M hPA translation hagreement rootMode.
  exact
    (raw_codedPALocalProofOf_guarded_four_state_table_append_exists_on_witnessed_tail
      M hPA translation hagreement
      (raw_zero M) (raw_zero M)
      coqDynamicTruthAppendRowBoundParameterName rootMode
      (raw_codedPAAxiomWitnessContext_empty M hPA)).
Qed.

(** Compile the vacuous rank-zero inherited traversal after an arbitrary
    root-term append proof has selected its finite standard witness batch.
    The proof is shared by every exposed-coordinate layout: the impossible
    [rowIndex < 0] branch and the harmless [bottom -> bottom] lookup mention
    only the append row binders, while the root tuple occurs solely in the
    visible context and in the append-existence formula transported below. *)
Theorem
    raw_dynamicTruthZeroCanonicalBottom_appendInheritedRowResourcesAtRootTermsUnderPrefix_on_standardWitnessTail_of_append_root :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    rootMode outerPrefix rootFormula rootAssignmentCode rootAssignmentStep
    appendWitnesses appendRoot,
  RawCodedPAAxiomWitnessContext M
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      appendWitnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      appendWitnesses (raw_zero M)) ->
  RawCodedPALocalProofOf M
    (rawStandardPAAxiomWitnessPrefixContextCode M
      appendWitnesses (raw_zero M))
    (rawTemplateFormula
      (rawBottomDirectStructuralTemplateTranslation M hPA)
      (coqDynamicTruthZeroCanonicalAppendExistsTemplateAtRootTerms
        rootMode rootFormula rootAssignmentCode rootAssignmentStep))
    appendRoot ->
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) /\
    RawDynamicTruthZeroCanonicalAppendInheritedRowResourcesAtRootTermsUnderPrefixAt
      M (rawBottomDirectStructuralTemplateTranslation M hPA)
      rootMode outerPrefix
      rootFormula rootAssignmentCode rootAssignmentStep witnesses.
Proof.
  intros M hPA rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep
    appendWitnesses appendRoot happendWitnessed happend.
  set (translation := rawBottomDirectStructuralTemplateTranslation M hPA).
  set (inputs := rawBottomTemplateDirectStructuralInputs M hPA).
  set (rowPrefix :=
    coqDynamicTruthZeroCanonicalAppendRowContextAtRootTerms
      rootMode rootFormula rootAssignmentCode rootAssignmentStep outerPrefix).
  destruct
    (raw_codedPALocalProofOf_below_zero_imp_ignored_imp_on_witnessed_tail_under_prefix
      M hPA translation
      (rawBottomDirectStructuralTemplatePAAgreement M hPA)
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        appendWitnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        appendWitnesses (raw_zero M))
      (templateContextShiftMany 5 rowPrefix) (ttVar 4)
      coqDynamicTruthZeroCanonicalVacuousOldLookupTemplate
      (templateFormulaShiftMany 5
        (coqFourStateTableAppendConcreteClosedRowProductionTemplate
          (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
          (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)))
      (raw_directStructuralTemplatePrefix_atomically_adequate
        M hPA inputs (templateContextShiftMany 5 rowPrefix))
      ((raw_directStructuralTemplatePrefix_atomically_adequate
          M hPA inputs [coqNoLtZeroAntecedentTemplate (ttVar 4)])
        (coqNoLtZeroAntecedentTemplate (ttVar 4))
        (or_introl eq_refl))
      ((raw_directStructuralTemplatePrefix_atomically_adequate
          M hPA inputs
          [coqDynamicTruthZeroCanonicalVacuousOldLookupTemplate])
        coqDynamicTruthZeroCanonicalVacuousOldLookupTemplate
        (or_introl eq_refl))
      happendWitnessed)
    as (traversalWitnesses & bodyRoot & hfinalWitnessed & hbody).
  set (finalWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      traversalWitnesses
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        appendWitnesses (raw_zero M))).
  set (finalContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      traversalWitnesses
      (rawStandardPAAxiomWitnessPrefixContextCode M
        appendWitnesses (raw_zero M))).
  assert (hboundBody : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation finalContext
        (templateContextShiftMany 5 rowPrefix))
      (rawTemplateFormula translation
        coqDynamicTruthZeroCanonicalVacuousInheritedBoundRowBodyTemplate)
      bodyRoot).
  {
    unfold coqDynamicTruthZeroCanonicalVacuousInheritedBoundRowBodyTemplate.
    rewrite !rawTemplateFormula_imp.
    unfold translation in hbody |- *.
    rewrite
      raw_dynamicTruthZeroCanonicalBottom_append_below_parameter_zero_for_root_terms.
    exact hbody.
  }
  destruct
    (raw_codedPALocalProofOf_universal_introduction_chain_on_witnessed_tail
      M hPA translation finalWitnessList finalContext 5
      rowPrefix
      coqDynamicTruthZeroCanonicalVacuousInheritedBoundRowBodyTemplate
      bodyRoot hfinalWitnessed hboundBody)
    as [traversalRoot htraversal].
  set (visibleRowContext :=
    rawTemplateContextCodeOnTail translation finalContext rowPrefix).
  assert (hvisibleRowContext : RawContextListRealizable M visibleRowContext).
  {
    unfold visibleRowContext.
    exact (raw_templateContextOnTail_realizable M hPA translation
      finalContext rowPrefix
      (raw_codedPAAxiomWitnessContext_context_realizable M
        finalWitnessList finalContext hfinalWitnessed)).
  }
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    visibleRowContext (rawFormulaBotCode M) hvisibleRowContext)
    as holdLookupBody.
  pose proof (raw_codedPALocalProofOf_impI M hPA
    visibleRowContext (rawFormulaBotCode M) (rawFormulaBotCode M)
    _ holdLookupBody) as holdLookup.
  lazymatch type of holdLookup with
  | RawCodedPALocalProofOf _ _ _ ?oldLookupRoot =>
      assert (holdLookupTemplate : RawCodedPALocalProofOf M
        visibleRowContext
        (rawTemplateFormula translation
          coqDynamicTruthZeroCanonicalVacuousOldLookupTemplate)
        oldLookupRoot)
  end.
  {
    unfold coqDynamicTruthZeroCanonicalVacuousOldLookupTemplate.
    rewrite rawTemplateFormula_imp, rawTemplateFormula_bot.
    exact holdLookup.
  }
  destruct
    (raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix
      M hPA traversalWitnesses
      (rawStandardPAAxiomWitnessPrefixContextCode M
        appendWitnesses (raw_zero M))
      (rawTemplateFormula translation
        (coqDynamicTruthZeroCanonicalAppendExistsTemplateAtRootTerms
          rootMode rootFormula rootAssignmentCode rootAssignmentStep))
      appendRoot
      (raw_codedPAAxiomWitnessContext_context_realizable M
        (rawStandardPAAxiomWitnessPrefixWitnessListCode M
          appendWitnesses (raw_zero M))
        (rawStandardPAAxiomWitnessPrefixContextCode M
          appendWitnesses (raw_zero M)) happendWitnessed)
      happend)
    as [transportedAppendRoot htransportedAppend].
  exists (traversalWitnesses ++ appendWitnesses).
  rewrite rawStandardPAAxiomWitnessPrefixWitnessListCode_app.
  rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
  split; [exact hfinalWitnessed |].
  exists transportedAppendRoot,
    coqDynamicTruthZeroCanonicalVacuousInheritedTraversalTemplate,
    coqDynamicTruthZeroCanonicalVacuousOldLookupTemplate.
  split.
  - rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
    exact htransportedAppend.
  - split.
    + exact
        coqDynamicTruthZeroCanonicalVacuousInheritedTraversalTemplate_open.
    + exists traversalRoot.
      lazymatch type of holdLookupTemplate with
      | RawCodedPALocalProofOf _ _ _ ?oldLookupRoot =>
          exists oldLookupRoot
      end.
      split.
      * fold finalContext in htraversal.
        rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
        unfold rowPrefix,
          coqDynamicTruthZeroCanonicalAppendRowContextAtRootTerms
          in htraversal |- *.
        exact htraversal.
      * unfold visibleRowContext in holdLookupTemplate.
        rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
        unfold rowPrefix,
          coqDynamicTruthZeroCanonicalAppendRowContextAtRootTerms
          in holdLookupTemplate |- *.
        exact holdLookupTemplate.
Qed.

(** Fully internal guarded inherited-row producer.  Append beta-definedness
    is discharged by the guarded endpoint above; the generic theorem then
    adds the vacuous traversal and old lookup on one synchronized PA tail. *)
Theorem
    raw_dynamicTruthZeroCanonicalBottom_guardedAppendInheritedRowResourcesUnderPrefix_on_standardWitnessTail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    rootMode outerPrefix,
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) /\
    RawDynamicTruthZeroCanonicalGuardedAppendInheritedRowResourcesUnderPrefixAt
      M (rawBottomDirectStructuralTemplateTranslation M hPA)
      rootMode outerPrefix witnesses.
Proof.
  intros M hPA rootMode outerPrefix.
  destruct
    (raw_dynamicTruthZeroCanonicalGuardedAppendRoot_on_standardWitnessTail
      M hPA (rawBottomDirectStructuralTemplateTranslation M hPA)
      (rawBottomDirectStructuralTemplatePAAgreement M hPA) rootMode)
    as (appendWitnesses & appendRoot & happendWitnessed & happend).
  exact
    (raw_dynamicTruthZeroCanonicalBottom_appendInheritedRowResourcesAtRootTermsUnderPrefix_on_standardWitnessTail_of_append_root
      M hPA rootMode outerPrefix (ttVar 2) (ttVar 6) (ttVar 5)
      appendWitnesses appendRoot happendWitnessed happend).
Qed.

(** Once a guarded fixed-production compiler is available, all remaining
    coordinates of its row payload are now internal: guarded append
    existence, vacuous inherited traversal, old lookup, and witness-tail
    synchronization are assembled by the two generic theorems above. *)
Theorem
    raw_dynamicTruthZeroCanonicalBottom_guardedAppendRowKernelPayload_on_standardWitnessTail_of_growing_fixed_production :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    rootMode outerPrefix,
  RawDynamicTruthZeroCanonicalGuardedGrowingFixedProductionCompilerUnderPrefixAt
    M (rawBottomDirectStructuralTemplateTranslation M hPA)
    rootMode outerPrefix ->
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) /\
    RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadUnderPrefixAt
      M (rawBottomDirectStructuralTemplateTranslation M hPA)
      rootMode outerPrefix witnesses.
Proof.
  intros M hPA rootMode outerPrefix hfixedCompiler.
  destruct
    (raw_dynamicTruthZeroCanonicalBottom_guardedAppendInheritedRowResourcesUnderPrefix_on_standardWitnessTail
      M hPA rootMode outerPrefix)
    as (inheritedWitnesses & hinheritedWitnessed & hinheritedResources).
  exact
    (raw_dynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTerms_on_standardWitnessTail_of_inherited_and_growing_fixed_production
      M hPA (rawBottomDirectStructuralTemplateTranslation M hPA)
      (rawBottomDirectStructuralTemplatePAAgreement M hPA)
      rootMode outerPrefix (ttVar 2) (ttVar 6) (ttVar 5)
      inheritedWitnesses hinheritedWitnessed
      hinheritedResources hfixedCompiler).
Qed.

(** A canonical row payload is monotone in its finite batch of standard PA
    witnesses.  The caller may add witnesses on either side of the original
    batch; all four represented roots are transported while the local row
    prefix and its two syntactic formulas remain unchanged.  This is the
    useful general form for independently compiled Sigma and Pi branches,
    whose witness batches need not have been coordinated in advance. *)
Theorem
    raw_dynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTermsUnderPrefixAt_standardWitnessTail_surround :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall
    rootMode outerPrefix rootFormula rootAssignmentCode rootAssignmentStep
    witnesses prefix suffix,
  RawDynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
      rootFormula rootAssignmentCode rootAssignmentStep witnesses ->
  RawDynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
      rootFormula rootAssignmentCode rootAssignmentStep
      (prefix ++ (witnesses ++ suffix)).
Proof.
  intros M hPA translation hagreement
    rootMode outerPrefix rootFormula rootAssignmentCode rootAssignmentStep
    witnesses prefix suffix
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
        rootFormula rootAssignmentCode rootAssignmentStep outerPrefix)).
  assert (happendSource : RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (embedPAContext (map witnessedAxiom witnesses)))
      (rawTemplateFormula translation
        (coqFourStateTableAppendExistsTemplate
          (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
          (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
          (ttParameter coqDynamicTruthAppendRowBoundParameterName)
          (embedPATerm (Term.numeral rootMode))
          rootFormula rootAssignmentCode rootAssignmentStep)) appendRoot).
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
          rootFormula rootAssignmentCode rootAssignmentStep))
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

Corollary
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
  intros M hPA translation hagreement rootMode outerPrefix
    witnesses prefix suffix hpayload.
  exact
    (raw_dynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTermsUnderPrefixAt_standardWitnessTail_surround
      M hPA translation hagreement rootMode outerPrefix
      (ttVar 2) (ttVar 1) (ttVar 0)
      witnesses prefix suffix hpayload).
Qed.

Theorem
    raw_dynamicTruthZeroCanonicalAppendRowKernelInputsAtRootTermsUnderPrefixAt_of_payload :
  forall (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    rootMode outerPrefix rootFormula rootAssignmentCode rootAssignmentStep
    witnesses,
  rootMode = 0 \/ rootMode = 1 ->
  RawDynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep witnesses ->
  RawDynamicTruthZeroCanonicalAppendRowKernelInputsAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep witnesses.
Proof.
  intros M translation rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep witnesses hrootMode
    (appendRoot & fixedProductionRoot & inheritedTraversal & oldLookup &
      happend & hopen & hinherited & hfixedProduction).
  exists appendRoot, fixedProductionRoot, inheritedTraversal, oldLookup.
  split; [exact hrootMode |].
  split; [exact happend |].
  split; [exact hopen |].
  split; [exact hinherited | exact hfixedProduction].
Qed.

Corollary
    raw_dynamicTruthZeroCanonicalPermutedAppendRowKernelInputsUnderPrefixAt_of_payload :
  forall (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    rootMode outerPrefix witnesses,
  rootMode = 0 \/ rootMode = 1 ->
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
    M translation rootMode outerPrefix witnesses ->
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelInputsUnderPrefixAt
    M translation rootMode outerPrefix witnesses.
Proof.
  intros M translation rootMode outerPrefix witnesses hrootMode hpayload.
  exact
    (raw_dynamicTruthZeroCanonicalAppendRowKernelInputsAtRootTermsUnderPrefixAt_of_payload
      M translation rootMode outerPrefix
      (ttVar 2) (ttVar 1) (ttVar 0) witnesses hrootMode hpayload).
Qed.

Corollary
    raw_dynamicTruthZeroCanonicalGuardedAppendRowKernelInputsUnderPrefixAt_of_payload :
  forall (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    rootMode outerPrefix witnesses,
  rootMode = 0 \/ rootMode = 1 ->
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadUnderPrefixAt
    M translation rootMode outerPrefix witnesses ->
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelInputsUnderPrefixAt
    M translation rootMode outerPrefix witnesses.
Proof.
  intros M translation rootMode outerPrefix witnesses hrootMode hpayload.
  exact
    (raw_dynamicTruthZeroCanonicalAppendRowKernelInputsAtRootTermsUnderPrefixAt_of_payload
      M translation rootMode outerPrefix
      (ttVar 2) (ttVar 6) (ttVar 5) witnesses hrootMode hpayload).
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
    RawDynamicTruthZeroCanonicalAppendRowKernelPayloadPairAtRootTermsUnderPrefix
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (outerPrefix : TemplateContext)
    (rootFormula rootAssignmentCode rootAssignmentStep : TemplateTerm) : Prop :=
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawDynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTermsUnderPrefixAt
      M translation 0 outerPrefix
      rootFormula rootAssignmentCode rootAssignmentStep witnesses /\
    RawDynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTermsUnderPrefixAt
      M translation 1 outerPrefix
      rootFormula rootAssignmentCode rootAssignmentStep witnesses.

Arguments
  RawDynamicTruthZeroCanonicalAppendRowKernelPayloadPairAtRootTermsUnderPrefix
  M translation outerPrefix rootFormula rootAssignmentCode
  rootAssignmentStep : clear implicits.

Definition
    RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadPairUnderPrefix
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (outerPrefix : TemplateContext) : Prop :=
  RawDynamicTruthZeroCanonicalAppendRowKernelPayloadPairAtRootTermsUnderPrefix
    M translation outerPrefix (ttVar 2) (ttVar 1) (ttVar 0).

Arguments
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadPairUnderPrefix
  M translation outerPrefix : clear implicits.

(** Weak producer-facing form of the payload pair.  Each polarity may choose
    its own finite standard witness batch; synchronization is a consequence,
    not an obligation imposed on the two branch compilers. *)
Definition
    RawDynamicTruthZeroCanonicalIndependentAppendRowKernelPayloadsAtRootTermsUnderPrefix
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (outerPrefix : TemplateContext)
    (rootFormula rootAssignmentCode rootAssignmentStep : TemplateTerm) : Prop :=
  (exists sigmaWitnesses : StandardPAAxiomWitnessPrefix,
    RawDynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTermsUnderPrefixAt
      M translation 0 outerPrefix
      rootFormula rootAssignmentCode rootAssignmentStep sigmaWitnesses) /\
  (exists piWitnesses : StandardPAAxiomWitnessPrefix,
    RawDynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTermsUnderPrefixAt
      M translation 1 outerPrefix
      rootFormula rootAssignmentCode rootAssignmentStep piWitnesses).

Arguments
  RawDynamicTruthZeroCanonicalIndependentAppendRowKernelPayloadsAtRootTermsUnderPrefix
  M translation outerPrefix rootFormula rootAssignmentCode
  rootAssignmentStep : clear implicits.

Definition
    RawDynamicTruthZeroCanonicalIndependentPermutedAppendRowKernelPayloadsUnderPrefix
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (outerPrefix : TemplateContext) : Prop :=
  RawDynamicTruthZeroCanonicalIndependentAppendRowKernelPayloadsAtRootTermsUnderPrefix
    M translation outerPrefix (ttVar 2) (ttVar 1) (ttVar 0).

Arguments
  RawDynamicTruthZeroCanonicalIndependentPermutedAppendRowKernelPayloadsUnderPrefix
  M translation outerPrefix : clear implicits.

Definition
    RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (outerPrefix : TemplateContext) : Prop :=
  RawDynamicTruthZeroCanonicalAppendRowKernelPayloadPairAtRootTermsUnderPrefix
    M translation outerPrefix (ttVar 2) (ttVar 6) (ttVar 5).

Definition
    RawDynamicTruthZeroCanonicalIndependentGuardedAppendRowKernelPayloadsUnderPrefix
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (outerPrefix : TemplateContext) : Prop :=
  RawDynamicTruthZeroCanonicalIndependentAppendRowKernelPayloadsAtRootTermsUnderPrefix
    M translation outerPrefix (ttVar 2) (ttVar 6) (ttVar 5).

Arguments
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix
  M translation outerPrefix : clear implicits.
Arguments
  RawDynamicTruthZeroCanonicalIndependentGuardedAppendRowKernelPayloadsUnderPrefix
  M translation outerPrefix : clear implicits.

(** Sigma and Pi may allocate unrelated finite helper batches.  Keep that
    weak producer-facing form; the generic pair synchronizer combines their
    batches only at the later consumer boundary. *)
Theorem
    raw_dynamicTruthZeroCanonicalBottom_independentGuardedAppendRowKernelPayloadsUnderPrefix_of_independent_growing_fixed_productions :
  forall (M : RawPAModel) (hPA : RawPASatisfies M) outerPrefix,
  RawDynamicTruthZeroCanonicalGuardedIndependentGrowingFixedProductionCompilersUnderPrefix
    M (rawBottomDirectStructuralTemplateTranslation M hPA) outerPrefix ->
  RawDynamicTruthZeroCanonicalIndependentGuardedAppendRowKernelPayloadsUnderPrefix
    M (rawBottomDirectStructuralTemplateTranslation M hPA) outerPrefix.
Proof.
  intros M hPA outerPrefix [hsigmaFixed hpiFixed].
  split.
  - destruct
      (raw_dynamicTruthZeroCanonicalBottom_guardedAppendRowKernelPayload_on_standardWitnessTail_of_growing_fixed_production
        M hPA 0 outerPrefix hsigmaFixed)
      as (sigmaWitnesses & _ & hsigmaPayload).
    exact (ex_intro _ sigmaWitnesses hsigmaPayload).
  - destruct
      (raw_dynamicTruthZeroCanonicalBottom_guardedAppendRowKernelPayload_on_standardWitnessTail_of_growing_fixed_production
        M hPA 1 outerPrefix hpiFixed)
      as (piWitnesses & _ & hpiPayload).
    exact (ex_intro _ piWitnesses hpiPayload).
Qed.

(** Relaxed guarded producers may instead refute the temporary row context.
    Represented bottom elimination converts both branches before invoking
    the shared payload constructor. *)
Theorem
    raw_dynamicTruthZeroCanonicalBottom_independentGuardedAppendRowKernelPayloadsUnderPrefix_of_independent_growing_fixed_productions_or_refutations :
  forall (M : RawPAModel) (hPA : RawPASatisfies M) outerPrefix,
  RawDynamicTruthZeroCanonicalGuardedIndependentGrowingFixedProductionOrRefutationCompilersUnderPrefix
    M (rawBottomDirectStructuralTemplateTranslation M hPA) outerPrefix ->
  RawDynamicTruthZeroCanonicalIndependentGuardedAppendRowKernelPayloadsUnderPrefix
    M (rawBottomDirectStructuralTemplateTranslation M hPA) outerPrefix.
Proof.
  intros M hPA outerPrefix hcompilers.
  apply
    (raw_dynamicTruthZeroCanonicalBottom_independentGuardedAppendRowKernelPayloadsUnderPrefix_of_independent_growing_fixed_productions
      M hPA outerPrefix).
  exact
    (raw_dynamicTruthZeroCanonicalIndependentGrowingFixedProductionCompilersAtRootTermsUnderPrefix_of_production_or_refutation
      M hPA (rawBottomDirectStructuralTemplateTranslation M hPA)
      outerPrefix (ttVar 2) (ttVar 6) (ttVar 5) hcompilers).
Qed.

(** Synchronize independently compiled canonical Sigma and Pi payloads by
    surrounding both standard witness batches with the other branch's
    witnesses.  The common batch is their concatenation; no equality between
    the original batches and no preselected common proof roots is required. *)
Theorem
    raw_dynamicTruthZeroCanonicalAppendRowKernelPayloadPairAtRootTermsUnderPrefix_of_independent_witnesses :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall
    outerPrefix rootFormula rootAssignmentCode rootAssignmentStep
    sigmaWitnesses piWitnesses,
  RawDynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTermsUnderPrefixAt
    M translation 0 outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep sigmaWitnesses ->
  RawDynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTermsUnderPrefixAt
    M translation 1 outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep piWitnesses ->
  RawDynamicTruthZeroCanonicalAppendRowKernelPayloadPairAtRootTermsUnderPrefix
    M translation outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep.
Proof.
  intros M hPA translation hagreement outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep
    sigmaWitnesses piWitnesses hsigma hpi.
  exists (sigmaWitnesses ++ piWitnesses).
  split.
  - change (RawDynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTermsUnderPrefixAt
      M translation 0 outerPrefix
        rootFormula rootAssignmentCode rootAssignmentStep
        (nil ++ (sigmaWitnesses ++ piWitnesses))).
    exact
      (raw_dynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTermsUnderPrefixAt_standardWitnessTail_surround
        M hPA translation hagreement 0 outerPrefix
        rootFormula rootAssignmentCode rootAssignmentStep sigmaWitnesses
        nil piWitnesses hsigma).
  - replace (sigmaWitnesses ++ piWitnesses) with
      (sigmaWitnesses ++ (piWitnesses ++ nil))
      by now rewrite List.app_nil_r.
    exact
      (raw_dynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTermsUnderPrefixAt_standardWitnessTail_surround
        M hPA translation hagreement 1 outerPrefix
        rootFormula rootAssignmentCode rootAssignmentStep piWitnesses
        sigmaWitnesses nil hpi).
Qed.

Corollary
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
  exact
    (raw_dynamicTruthZeroCanonicalAppendRowKernelPayloadPairAtRootTermsUnderPrefix_of_independent_witnesses
      M hPA translation hagreement outerPrefix
      (ttVar 2) (ttVar 1) (ttVar 0)
      sigmaWitnesses piWitnesses hsigma hpi).
Qed.

(** Eliminate the weak independent package into the synchronized payload
    pair used by the row compiler. *)
Corollary
    raw_dynamicTruthZeroCanonicalAppendRowKernelPayloadPairAtRootTermsUnderPrefix_of_independent_payloads :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep,
  RawDynamicTruthZeroCanonicalIndependentAppendRowKernelPayloadsAtRootTermsUnderPrefix
    M translation outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep ->
  RawDynamicTruthZeroCanonicalAppendRowKernelPayloadPairAtRootTermsUnderPrefix
    M translation outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep.
Proof.
  intros M hPA translation hagreement outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep
    [[sigmaWitnesses hsigma] [piWitnesses hpi]].
  exact
    (raw_dynamicTruthZeroCanonicalAppendRowKernelPayloadPairAtRootTermsUnderPrefix_of_independent_witnesses
      M hPA translation hagreement outerPrefix
      rootFormula rootAssignmentCode rootAssignmentStep
      sigmaWitnesses piWitnesses hsigma hpi).
Qed.

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
  intros M hPA translation hagreement outerPrefix hpayloads.
  exact
    (raw_dynamicTruthZeroCanonicalAppendRowKernelPayloadPairAtRootTermsUnderPrefix_of_independent_payloads
      M hPA translation hagreement outerPrefix
      (ttVar 2) (ttVar 1) (ttVar 0) hpayloads).
Qed.

Corollary
    raw_dynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix_of_independent_payloads :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall outerPrefix,
  RawDynamicTruthZeroCanonicalIndependentGuardedAppendRowKernelPayloadsUnderPrefix
    M translation outerPrefix ->
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix
    M translation outerPrefix.
Proof.
  intros M hPA translation hagreement outerPrefix hpayloads.
  exact
    (raw_dynamicTruthZeroCanonicalAppendRowKernelPayloadPairAtRootTermsUnderPrefix_of_independent_payloads
      M hPA translation hagreement outerPrefix
      (ttVar 2) (ttVar 6) (ttVar 5) hpayloads).
Qed.

(** Compile the three-root canonical kernel through the suffix-preserving
    arithmetic case split. *)
Theorem
    raw_dynamicTruthZeroCanonicalAppendRowImplicationInputsAtRootTermsUnderPrefixAt_of_kernel :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode outerPrefix rootFormula rootAssignmentCode
    rootAssignmentStep witnesses,
  RawDynamicTruthZeroCanonicalAppendRowKernelInputsAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep witnesses ->
  RawDynamicTruthZeroCanonicalAppendRowImplicationInputsAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep witnesses.
Proof.
  intros M hPA translation hagreement rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep witnesses
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
        rootFormula rootAssignmentCode rootAssignmentStep
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

Corollary
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
  intros M hPA translation hagreement rootMode outerPrefix witnesses hkernel.
  exact
    (raw_dynamicTruthZeroCanonicalAppendRowImplicationInputsAtRootTermsUnderPrefixAt_of_kernel
      M hPA translation hagreement rootMode outerPrefix
      (ttVar 2) (ttVar 1) (ttVar 0) witnesses hkernel).
Qed.

(** Literal-tail form consumed directly by the low-level append constructors.
    The caller prefix and the closed PA witness formulas are supplied as one
    template tail.  Unlike the growing package above, this interface does not
    ask the caller to choose a second witnessed target, prove reflexive tail
    inclusion, or normalize the thirteen-shift context code. *)
Definition
    RawDynamicTruthZeroCanonicalAppendLiteralRowImplicationInputsAtRootTermsUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext)
    (rootFormula rootAssignmentCode rootAssignmentStep : TemplateTerm)
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
          rootFormula rootAssignmentCode rootAssignmentStep)) appendRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (templateContextShiftMany 5
          (coqFourStateTableAppendWitnessContext
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            (ttParameter coqDynamicTruthAppendRowBoundParameterName)
            (embedPATerm (Term.numeral rootMode))
            rootFormula rootAssignmentCode rootAssignmentStep
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
  RawDynamicTruthZeroCanonicalAppendLiteralRowImplicationInputsAtRootTermsUnderPrefixAt
  M translation rootMode outerPrefix rootFormula rootAssignmentCode
  rootAssignmentStep witnesses : clear implicits.

Definition
    RawDynamicTruthZeroCanonicalPermutedAppendLiteralRowImplicationInputsUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawDynamicTruthZeroCanonicalAppendLiteralRowImplicationInputsAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    (ttVar 2) (ttVar 1) (ttVar 0) witnesses.

Arguments
  RawDynamicTruthZeroCanonicalPermutedAppendLiteralRowImplicationInputsUnderPrefixAt
  M translation rootMode outerPrefix witnesses : clear implicits.

(** Normalize a literal-tail row proof into the synchronized growing package.
    All proof-producing content is preserved verbatim; only its context
    presentation changes. *)
Theorem
    raw_dynamicTruthZeroCanonicalAppendRowImplicationInputsAtRootTermsUnderPrefixAt_of_literal :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode outerPrefix rootFormula rootAssignmentCode
    rootAssignmentStep witnesses,
  RawDynamicTruthZeroCanonicalAppendLiteralRowImplicationInputsAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep witnesses ->
  RawDynamicTruthZeroCanonicalAppendRowImplicationInputsAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep witnesses.
Proof.
  intros M hPA translation hagreement rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep witnesses
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
      rootFormula rootAssignmentCode rootAssignmentStep outerPrefix witnesses
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

Corollary
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
  intros M hPA translation hagreement rootMode outerPrefix witnesses hliteral.
  exact
    (raw_dynamicTruthZeroCanonicalAppendRowImplicationInputsAtRootTermsUnderPrefixAt_of_literal
      M hPA translation hagreement rootMode outerPrefix
      (ttVar 2) (ttVar 1) (ttVar 0) witnesses hliteral).
Qed.

(** Close the five row binders at arbitrary exposed root terms.  The explicit
    row-stability equality is syntactic, not proof-producing: it prevents an
    unsound claim for unrestricted opaque local rows while letting scoped or
    concrete row pairs discharge the condition independently. *)
Theorem
    raw_dynamicTruthZeroCanonicalAppendInputsAtRootTermsUnderPrefixAt_of_row_implication_inputs :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  forall rootMode outerPrefix rootFormula rootAssignmentCode
    rootAssignmentStep witnesses,
  coqFourStateTableAppendOpenedTemplateGlobalRowsAtRootTerms rootMode
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
      rootFormula rootAssignmentCode rootAssignmentStep
      (ttParameter coqDynamicTruthAppendRowBoundParameterName) =
    coqFourStateTableAppendOpenedTemplateGlobalRows rootMode
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName) ->
  RawDynamicTruthZeroCanonicalAppendRowImplicationInputsAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep witnesses ->
  RawDynamicTruthZeroCanonicalAppendInputsAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep witnesses.
Proof.
  intros M hPA translation rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep witnesses hrowStable
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
      rootFormula rootAssignmentCode rootAssignmentStep
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
      rootFormula rootAssignmentCode rootAssignmentStep outerPrefix)
    (rawTemplateFormula translation
      (coqFourStateTableAppendOpenedTemplateGlobalRowsAtRootTerms rootMode
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
        rootFormula rootAssignmentCode rootAssignmentStep
        (ttParameter coqDynamicTruthAppendRowBoundParameterName)))).
  rewrite hrowStable.
  exact hclosedRows.
Qed.

Corollary
    raw_dynamicTruthZeroCanonicalGuardedAppendInputsUnderPrefixAt_of_row_implication_inputs :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  forall rootMode outerPrefix witnesses,
  RawDynamicTruthZeroCanonicalGuardedAppendRowImplicationInputsUnderPrefixAt
    M translation rootMode outerPrefix witnesses ->
  RawDynamicTruthZeroCanonicalGuardedAppendInputsUnderPrefixAt
    M translation rootMode outerPrefix witnesses.
Proof.
  intros M hPA translation rootMode outerPrefix witnesses hrows.
  exact
    (raw_dynamicTruthZeroCanonicalAppendInputsAtRootTermsUnderPrefixAt_of_row_implication_inputs
      M hPA translation rootMode outerPrefix
      (ttVar 2) (ttVar 6) (ttVar 5) witnesses
      (coqFourStateTableAppendOpenedAtRootTermsZeroCanonicalRows_guarded_eq
        rootMode (ttParameter coqDynamicTruthAppendRowBoundParameterName))
      hrows).
Qed.

Corollary
    raw_dynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt_of_row_implication_inputs :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  forall rootMode outerPrefix witnesses,
  RawDynamicTruthZeroCanonicalPermutedAppendRowImplicationInputsUnderPrefixAt
    M translation rootMode outerPrefix witnesses ->
  RawDynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt
    M translation rootMode outerPrefix witnesses.
Proof.
  intros M hPA translation rootMode outerPrefix witnesses hrows.
  pose proof
    (raw_dynamicTruthZeroCanonicalAppendInputsAtRootTermsUnderPrefixAt_of_row_implication_inputs
      M hPA translation rootMode outerPrefix
      (ttVar 2) (ttVar 1) (ttVar 0) witnesses
      (coqFourStateTableAppendOpenedAtRootTermsZeroCanonicalRows_permuted_eq
        rootMode (ttParameter coqDynamicTruthAppendRowBoundParameterName))
      hrows) as hgeneric.
  destruct hgeneric as
    (modeCode & modeStep & formulaCode & formulaStep &
      assignmentCodeCode & assignmentCodeStep &
      assignmentStepCode & assignmentStepStep & appendRoot &
      hrootMode & happend & hrowsAtRootTerms).
  exists modeCode, modeStep, formulaCode, formulaStep,
    assignmentCodeCode, assignmentCodeStep,
    assignmentStepCode, assignmentStepStep, appendRoot.
  split; [exact hrootMode |].
  split; [exact happend |].
  rewrite
    (coqFourStateTableAppendOpenedAtRootTermsZeroCanonicalRows_permuted_eq
      rootMode (ttParameter coqDynamicTruthAppendRowBoundParameterName))
    in hrowsAtRootTerms.
  fold
    (coqFourStateTableAppendOpenedPermutedTemplateGlobalRows rootMode
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName)).
  rewrite
    (coqFourStateTableAppendOpenedPermutedZeroCanonicalRows_eq
      rootMode (ttParameter coqDynamicTruthAppendRowBoundParameterName)
      hrootMode).
  exact hrowsAtRootTerms.
Qed.

(** Shared payload-to-input pipeline.  The sole syntactic premise records
    that the selected local row pair is stable under the requested exposed
    root-term application; concrete permuted and guarded layouts discharge
    it by the finite lemmas above. *)
Theorem
    raw_dynamicTruthZeroCanonicalAppendInputsAtRootTermsUnderPrefixAt_of_kernel_payload :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall
    rootMode outerPrefix rootFormula rootAssignmentCode rootAssignmentStep
    witnesses,
  rootMode = 0 \/ rootMode = 1 ->
  coqFourStateTableAppendOpenedTemplateGlobalRowsAtRootTerms rootMode
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
      rootFormula rootAssignmentCode rootAssignmentStep
      (ttParameter coqDynamicTruthAppendRowBoundParameterName) =
    coqFourStateTableAppendOpenedTemplateGlobalRows rootMode
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName) ->
  RawDynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep witnesses ->
  RawDynamicTruthZeroCanonicalAppendInputsAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep witnesses.
Proof.
  intros M hPA translation hagreement rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep witnesses
    hrootMode hrowStable hpayload.
  pose proof
    (raw_dynamicTruthZeroCanonicalAppendRowKernelInputsAtRootTermsUnderPrefixAt_of_payload
      M translation rootMode outerPrefix
      rootFormula rootAssignmentCode rootAssignmentStep witnesses
      hrootMode hpayload) as hkernel.
  pose proof
    (raw_dynamicTruthZeroCanonicalAppendRowImplicationInputsAtRootTermsUnderPrefixAt_of_kernel
      M hPA translation hagreement rootMode outerPrefix
      rootFormula rootAssignmentCode rootAssignmentStep witnesses hkernel)
    as hrows.
  exact
    (raw_dynamicTruthZeroCanonicalAppendInputsAtRootTermsUnderPrefixAt_of_row_implication_inputs
      M hPA translation rootMode outerPrefix
      rootFormula rootAssignmentCode rootAssignmentStep witnesses
      hrowStable hrows).
Qed.

Corollary
    raw_dynamicTruthZeroCanonicalGuardedAppendInputsUnderPrefixAt_of_kernel_payload :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall
    rootMode outerPrefix witnesses,
  rootMode = 0 \/ rootMode = 1 ->
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadUnderPrefixAt
    M translation rootMode outerPrefix witnesses ->
  RawDynamicTruthZeroCanonicalGuardedAppendInputsUnderPrefixAt
    M translation rootMode outerPrefix witnesses.
Proof.
  intros M hPA translation hagreement rootMode outerPrefix witnesses
    hrootMode hpayload.
  exact
    (raw_dynamicTruthZeroCanonicalAppendInputsAtRootTermsUnderPrefixAt_of_kernel_payload
      M hPA translation hagreement rootMode outerPrefix
      (ttVar 2) (ttVar 6) (ttVar 5) witnesses hrootMode
      (coqFourStateTableAppendOpenedAtRootTermsZeroCanonicalRows_guarded_eq
        rootMode (ttParameter coqDynamicTruthAppendRowBoundParameterName))
      hpayload).
Qed.

(** Close one zero-canonical polarity at an arbitrary exposed root tuple,
    without discharging the caller prefix.  The append-existence certificate
    initially lives on the witnessed PA tail; atomic adequacy inserts it
    below [outerPrefix], after which the root-term-parametric global append
    reconstruction consumes the seventh traversal field and removes the
    eight temporary append witnesses. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_global_at_root_terms_of_inputs_under_prefix :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep witnesses,
  RawCodedTemplatePrefixAtomicallyAdequate M translation outerPrefix ->
  RawDynamicTruthZeroCanonicalAppendInputsAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep witnesses ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)) outerPrefix
    (rawTemplateFormula translation
      (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms rootMode
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
        rootFormula rootAssignmentCode rootAssignmentStep)).
Proof.
  intros M hPA translation hagreement rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep witnesses hprefix
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
          rootFormula rootAssignmentCode rootAssignmentStep))
      appendRoot hbaseRealizable hprefix happend)
    as [prefixedAppendRoot hprefixedAppend].
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_template_global_at_root_terms_of_append_rows_under_prefix
      M hPA translation hagreement rootMode
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
      coqDynamicTruthAppendRowBoundParameterName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      rootFormula rootAssignmentCode rootAssignmentStep
      outerPrefix witnesses prefixedAppendRoot
      hrootMode hprefixedAppend hrows).
Qed.

(** Named guarded specialization of the primitive-input endpoint.  Keeping
    this corollary alongside the payload endpoint makes the public guarded
    API usable by clients which already assembled the complete seventh-field
    package and do not need to expose its lower kernel decomposition. *)
Corollary
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_guarded_global_of_inputs_under_prefix :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode outerPrefix witnesses,
  RawCodedTemplatePrefixAtomicallyAdequate M translation outerPrefix ->
  RawDynamicTruthZeroCanonicalGuardedAppendInputsUnderPrefixAt
    M translation rootMode outerPrefix witnesses ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)) outerPrefix
    (rawTemplateFormula translation
      (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms rootMode
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
        (ttVar 2) (ttVar 6) (ttVar 5))).
Proof.
  intros M hPA translation hagreement rootMode outerPrefix witnesses
    hprefix hinputs.
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_global_at_root_terms_of_inputs_under_prefix
      M hPA translation hagreement rootMode outerPrefix
      (ttVar 2) (ttVar 6) (ttVar 5) witnesses hprefix hinputs).
Qed.

(** One legal arbitrary-root source can be closed directly from its compact
    row-kernel payload.  The explicit row-stability equality is the only
    syntactic obligation: it identifies the protected root-term seventh
    field with the ordinary canonical row formula consumed by the existing
    literal row compiler. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_global_at_root_terms_of_kernel_payload_under_prefix :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep witnesses,
  rootMode = 0 \/ rootMode = 1 ->
  coqFourStateTableAppendOpenedTemplateGlobalRowsAtRootTerms rootMode
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
      rootFormula rootAssignmentCode rootAssignmentStep
      (ttParameter coqDynamicTruthAppendRowBoundParameterName) =
    coqFourStateTableAppendOpenedTemplateGlobalRows rootMode
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName) ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation outerPrefix ->
  RawDynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTermsUnderPrefixAt
    M translation rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep witnesses ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)) outerPrefix
    (rawTemplateFormula translation
      (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms rootMode
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
        rootFormula rootAssignmentCode rootAssignmentStep)).
Proof.
  intros M hPA translation hagreement rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep witnesses
    hrootMode hrowStable hprefix hpayload.
  pose proof
    (raw_dynamicTruthZeroCanonicalAppendInputsAtRootTermsUnderPrefixAt_of_kernel_payload
      M hPA translation hagreement rootMode outerPrefix
      rootFormula rootAssignmentCode rootAssignmentStep witnesses
      hrootMode hrowStable hpayload) as hinputs.
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_global_at_root_terms_of_inputs_under_prefix
      M hPA translation hagreement rootMode outerPrefix
      rootFormula rootAssignmentCode rootAssignmentStep witnesses
      hprefix hinputs).
Qed.

(** Guarded predecessor callbacks expose the tuple [#2,#6,#5].  Its finite
    row-stability calculation was proved above, so no additional syntactic
    premise remains at this public specialization. *)
Corollary
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_guarded_global_of_kernel_payload_under_prefix :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode outerPrefix witnesses,
  rootMode = 0 \/ rootMode = 1 ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation outerPrefix ->
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadUnderPrefixAt
    M translation rootMode outerPrefix witnesses ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)) outerPrefix
    (rawTemplateFormula translation
      (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms rootMode
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
        (ttVar 2) (ttVar 6) (ttVar 5))).
Proof.
  intros M hPA translation hagreement rootMode outerPrefix witnesses
    hrootMode hprefix hpayload.
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_global_at_root_terms_of_kernel_payload_under_prefix
      M hPA translation hagreement rootMode outerPrefix
      (ttVar 2) (ttVar 6) (ttVar 5) witnesses
      hrootMode
      (coqFourStateTableAppendOpenedAtRootTermsZeroCanonicalRows_guarded_eq
        rootMode (ttParameter coqDynamicTruthAppendRowBoundParameterName))
      hprefix hpayload).
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

(** Compile one legal canonical mode directly from its row-kernel payload.
    This packages the otherwise repetitive payload-to-kernel, row-closing,
    and append-elimination pipeline.  Crucially, it has no premise for the
    opposite polarity, so it can be invoked inside a disjunction branch
    whose head already supplies that other application. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_permuted_global_of_kernel_payload_under_prefix :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode outerPrefix witnesses,
  rootMode = 0 \/ rootMode = 1 ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation outerPrefix ->
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
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
    hrootMode hprefix hpayload.
  pose proof
    (raw_dynamicTruthZeroCanonicalPermutedAppendRowKernelInputsUnderPrefixAt_of_payload
      M translation rootMode outerPrefix witnesses hrootMode hpayload)
    as hkernel.
  pose proof
    (raw_dynamicTruthZeroCanonicalPermutedAppendRowImplicationInputsUnderPrefixAt_of_kernel
      M hPA translation hagreement rootMode outerPrefix witnesses hkernel)
    as hrows.
  pose proof
    (raw_dynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt_of_row_implication_inputs
      M hPA translation rootMode outerPrefix witnesses hrows)
    as hinputs.
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_permuted_global_of_inputs_under_prefix
      M hPA translation hagreement rootMode outerPrefix witnesses
      hprefix hinputs).
Qed.

(** Rebase the unary Sigma traversal onto a caller-selected witnessed tail
    and expose the literal canonical application code. *)
Corollary
    raw_dynamicTruthZeroCanonicalSigmaApplication_of_permuted_append_kernel_payload_under_prefix :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall outerPrefix witnesses sourceWitnessList sourceContext,
  RawCodedTemplatePrefixAtomicallyAdequate M translation outerPrefix ->
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
    M translation 0 outerPrefix witnesses ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext outerPrefix
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalSigmaApplicationFormula).
Proof.
  intros M hPA translation hagreement outerPrefix witnesses
    sourceWitnessList sourceContext hprefix hsource hpayload.
  pose proof
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_permuted_global_of_kernel_payload_under_prefix
      M hPA translation hagreement 0 outerPrefix witnesses
      (or_introl eq_refl) hprefix hpayload) as hglobal.
  rewrite (rawTemplateFormula_zeroCanonicalPermutedGlobalSource_sigma
    M translation hagreement) in hglobal.
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_rebase
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) outerPrefix
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalSigmaApplicationFormula)
      sourceWitnessList sourceContext hsource hglobal).
Qed.

(** Pi counterpart of the unary rebased application compiler. *)
Corollary
    raw_dynamicTruthZeroCanonicalPiApplication_of_permuted_append_kernel_payload_under_prefix :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall outerPrefix witnesses sourceWitnessList sourceContext,
  RawCodedTemplatePrefixAtomicallyAdequate M translation outerPrefix ->
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
    M translation 1 outerPrefix witnesses ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext outerPrefix
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalPiApplicationFormula).
Proof.
  intros M hPA translation hagreement outerPrefix witnesses
    sourceWitnessList sourceContext hprefix hsource hpayload.
  pose proof
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_permuted_global_of_kernel_payload_under_prefix
      M hPA translation hagreement 1 outerPrefix witnesses
      (or_intror eq_refl) hprefix hpayload) as hglobal.
  rewrite (rawTemplateFormula_zeroCanonicalPermutedGlobalSource_pi
    M translation hagreement) in hglobal.
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_rebase
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) outerPrefix
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalPiApplicationFormula)
      sourceWitnessList sourceContext hsource hglobal).
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
