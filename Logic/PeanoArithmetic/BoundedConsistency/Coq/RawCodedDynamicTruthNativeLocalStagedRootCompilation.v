(**
  Dependency-aware compilation of the native positive local field.

  The earlier native leaf compiler deliberately ended at an empty-context
  interface.  That interface is too strong for the staged master successor:
  the current six master roots already inhabit one witnessed PA context, and
  compiling the forty fixed collision helpers may grow that context by a
  further standard PA-axiom prefix.  The useful invariant is therefore one
  *visible* witnessed context shared by the current master, the helpers, and
  the next local-field root.

  This module performs the context-safe part of that construction.  It

  - derives every atomic-adequacy fact carried by one native successor trace;
  - constructs the finite Or7-by-Or6 elimination resources from the two
    linked lower applications;
  - recovers the sixteen fixed-constructor cells from the ordered helper
    sub-batch without proof irrelevance;
  - reduces the collision-matrix input record to seven genuinely dynamic
    current-field kernel roots;
  - assembles the decision and exclusivity leaves, and closes them into the
    next local field over the same witnessed base.

  The residual interface remains honest.  In particular it still asks for
  the two domain-case decision roots, the two row roots extracted from the
  linked global evidence, the current-field kernel roots, the two direct row
  projection packages, and the three exact temporary-context self-shifts.
  No semantic truth-to-proof conversion, empty-context erasure, unlinked row
  choice, or arbitrary-context weakening is used.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruthTotality
  RawCodedFormulaOperations
  RawCodedFormulaShiftTreeRealization
  RawCodedNumeralTermCode
  RawCodedProofAtomicAdequacyStandard
  RawCodedRestrictedPAProof
  RawCodedContextLists
  RawCodedContextShift
  RawCodedPAAxiomContextSelfShift
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedProofImpIConstructor
  RawCodedProofAllIConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofAndIntroduction
  RawCodedPALocalProofFiniteDisjunction
  RawCodedPALocalProofFiniteDisjunctionDerivedCases
  RawCodedPALocalProofFiniteDisjunctionMatrix
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplateNumeralParameters
  RawCodedTruthCertificateMasterBaseBridge
  RawCodedTruthCertificateMasterCollisionHelperBatch
  RawCodedTruthCertificateMasterFixedHelperBatchExtension
  RawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation
  RawCodedDynamicTruthGlobalSuccessorRootClosure
  RawCodedDynamicTruthQFBranchExclusivity
  RawCodedDynamicTruthImpBranchExclusivity
  RawCodedDynamicTruthBooleanBranchExclusivity
  RawCodedDynamicTruthQuantifierBranchExclusivity
  RawCodedDynamicTruthQuantifierConditionalCellCompilation
  RawCodedDynamicTruthMixedQFBranchExclusivity
  RawCodedDynamicTruthConstructorBranchDisjointness
  RawCodedDynamicTruthBinderOffDiagonalExclusivity
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthPiUniversalLeafSourceTemplate
  RawCodedDynamicTruthPairedSuccessorAdequacy
  RawCodedDynamicTruthSuccessorRowBranchDisjunctionCompilation
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthLocalCollisionMatrixAssembly
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeLocalLeafRootCompiler
  RawCodedDynamicTruthNativeGlobalEvidenceRootCompilation
  RawCodedDynamicTruthNativeLocalDecisionRootCompilation
  RawCodedDynamicTruthNativeCrossLevelLeafRootCompilation.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthNativeLocalStagedRootCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofAllIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofAndIntroduction.
Import PABoundedRawCodedPALocalProofFiniteDisjunction.
Import PABoundedRawCodedPALocalProofFiniteDisjunctionDerivedCases.
Import PABoundedRawCodedPALocalProofFiniteDisjunctionMatrix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTruthCertificateMasterBaseBridge.
Import PABoundedRawCodedTruthCertificateMasterCollisionHelperBatch.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import
  PABoundedRawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation.
Import PABoundedRawCodedDynamicTruthGlobalSuccessorRootClosure.
Import PABoundedRawCodedDynamicTruthQFBranchExclusivity.
Import PABoundedRawCodedDynamicTruthImpBranchExclusivity.
Import PABoundedRawCodedDynamicTruthBooleanBranchExclusivity.
Import PABoundedRawCodedDynamicTruthQuantifierBranchExclusivity.
Import PABoundedRawCodedDynamicTruthQuantifierConditionalCellCompilation.
Import PABoundedRawCodedDynamicTruthMixedQFBranchExclusivity.
Import PABoundedRawCodedDynamicTruthConstructorBranchDisjointness.
Import PABoundedRawCodedDynamicTruthBinderOffDiagonalExclusivity.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthPiUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
Import
  PABoundedRawCodedDynamicTruthSuccessorRowBranchDisjunctionCompilation.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalLeafRootCompiler.
Import PABoundedRawCodedDynamicTruthNativeGlobalEvidenceRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalDecisionRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelLeafRootCompilation.

(** ------------------------------------------------------------------
    Closing the local connective shell over a visible witnessed base. *)

Definition rawDynamicTruthNativeLocalClose3RootOn
    (M : RawPAModel) (baseContext body child : M) : M :=
  rawProofAllIRoot M baseContext
    (rawFormulaAllCode M (rawFormulaAllCode M body))
    (rawProofAllIRoot M baseContext
      (rawFormulaAllCode M body)
      (rawProofAllIRoot M baseContext body child)).

Arguments rawDynamicTruthNativeLocalClose3RootOn
  M baseContext body child : clear implicits.

Theorem raw_codedPALocalProofOf_dynamicTruthNativeLocal_close3_on : forall
    (M : RawPAModel), RawPASatisfies M -> forall baseContext body child,
  RawContextShift M baseContext baseContext ->
  RawCodedPALocalProofOf M baseContext body child ->
  RawCodedPALocalProofOf M baseContext
    (rawDynamicTruthLocalFormulaAll3Code M body)
    (rawDynamicTruthNativeLocalClose3RootOn
      M baseContext body child).
Proof.
  intros M hPA baseContext body child hshift [hcoverage hendpoint].
  pose proof (raw_proofAllI_ruleCoverage M hPA
    baseContext baseContext body child hshift hcoverage hendpoint)
    as hcoverage1.
  pose proof (raw_proofAllI_endpoint M baseContext body child)
    as hendpoint1.
  pose proof (raw_proofAllI_ruleCoverage M hPA
    baseContext baseContext (rawFormulaAllCode M body)
    (rawProofAllIRoot M baseContext body child)
    hshift hcoverage1 hendpoint1) as hcoverage2.
  pose proof (raw_proofAllI_endpoint M baseContext
    (rawFormulaAllCode M body)
    (rawProofAllIRoot M baseContext body child)) as hendpoint2.
  pose proof (raw_proofAllI_ruleCoverage M hPA
    baseContext baseContext
    (rawFormulaAllCode M (rawFormulaAllCode M body))
    (rawProofAllIRoot M baseContext
      (rawFormulaAllCode M body)
      (rawProofAllIRoot M baseContext body child))
    hshift hcoverage2 hendpoint2) as hcoverage3.
  pose proof (raw_proofAllI_endpoint M baseContext
    (rawFormulaAllCode M (rawFormulaAllCode M body))
    (rawProofAllIRoot M baseContext
      (rawFormulaAllCode M body)
      (rawProofAllIRoot M baseContext body child))) as hendpoint3.
  split; assumption.
Qed.

Definition RawDynamicTruthNativeLocalFieldRootOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain sigmaEvidence piEvidence : M)
    : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M baseContext
      (rawDynamicTruthLocalDecisionExclusiveFieldCode M
        sigmaDomain piDomain sigmaEvidence piEvidence) root.

Arguments RawDynamicTruthNativeLocalFieldRootOn
  M baseContext sigmaDomain piDomain sigmaEvidence piEvidence
  : clear implicits.

(** The only context shifted by the three All-I nodes is [baseContext].
    Admissibility and the two evidence assumptions have already been
    discharged by Imp-I, so no false self-shift claim about their open codes
    is needed here. *)
Theorem raw_dynamicTruthNativeLocalFieldRootOn_of_leaf_roots : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence,
  RawContextShift M baseContext baseContext ->
  RawDynamicTruthNativeLocalLeafRootsOn M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  RawDynamicTruthNativeLocalFieldRootOn M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
    hbaseShift [[decisionChild hdecision] [exclusiveChild hexclusive]].
  pose proof (raw_codedPALocalProofOf_impI M hPA baseContext
    (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
    (rawFormulaOrCode M sigmaEvidence piEvidence)
    decisionChild hdecision) as hdecisionImp.
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthNativeLocal_close3_on
      M hPA baseContext
      (rawDynamicTruthLocalDecisionCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)
      (rawProofImpIRoot M baseContext
        (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
        (rawFormulaOrCode M sigmaEvidence piEvidence)
        decisionChild)
      hbaseShift hdecisionImp) as hdecisionClosed.

  pose proof (raw_codedPALocalProofOf_impI M hPA
    (rawDynamicTruthNativeLocalExclusiveSigmaContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence)
    piEvidence (rawFormulaBotCode M)
    exclusiveChild hexclusive) as hpiImp.
  pose proof (raw_codedPALocalProofOf_impI M hPA
    (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
      sigmaDomain piDomain)
    sigmaEvidence
    (rawFormulaImpCode M piEvidence (rawFormulaBotCode M))
    (rawProofImpIRoot M
      (rawDynamicTruthNativeLocalExclusiveSigmaContextOn M baseContext
        sigmaDomain piDomain sigmaEvidence)
      piEvidence (rawFormulaBotCode M) exclusiveChild)
    hpiImp) as hsigmaImp.
  pose proof (raw_codedPALocalProofOf_impI M hPA baseContext
    (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
    (rawFormulaImpCode M sigmaEvidence
      (rawFormulaImpCode M piEvidence (rawFormulaBotCode M)))
    (rawProofImpIRoot M
      (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
        sigmaDomain piDomain)
      sigmaEvidence
      (rawFormulaImpCode M piEvidence (rawFormulaBotCode M))
      (rawProofImpIRoot M
        (rawDynamicTruthNativeLocalExclusiveSigmaContextOn M baseContext
          sigmaDomain piDomain sigmaEvidence)
        piEvidence (rawFormulaBotCode M) exclusiveChild))
    hsigmaImp) as hexclusiveImp.
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthNativeLocal_close3_on
      M hPA baseContext
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)
      (rawProofImpIRoot M baseContext
        (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
        (rawFormulaImpCode M sigmaEvidence
          (rawFormulaImpCode M piEvidence (rawFormulaBotCode M)))
        (rawProofImpIRoot M
          (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
            sigmaDomain piDomain)
          sigmaEvidence
          (rawFormulaImpCode M piEvidence (rawFormulaBotCode M))
          (rawProofImpIRoot M
            (rawDynamicTruthNativeLocalExclusiveSigmaContextOn M
              baseContext sigmaDomain piDomain sigmaEvidence)
            piEvidence (rawFormulaBotCode M) exclusiveChild)))
      hbaseShift hexclusiveImp) as hexclusiveClosed.
  pose proof (raw_codedPALocalProofOf_andI M hPA baseContext
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalDecisionCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    _ _ hdecisionClosed hexclusiveClosed) as hfield.
  eexists. exact hfield.
Qed.

(** ------------------------------------------------------------------
    Adequacy of the exact trace-linked parameters. *)

Lemma raw_dynamicTruthCoqLowerApplication_target_atomically_adequate :
    forall (M : RawPAModel), RawPASatisfies M -> forall input output,
  RawDynamicTruthCoqLowerApplication M input output ->
  RawCodedFormulaAtomicallyAdequate M output.
Proof.
  intros M hPA input output (first & second & _ & _ & hthird).
  exact (raw_fixedReplacement_substitution_target_atomically_adequate
    M hPA dynamicTruthCoqLowerThirdReplacement second output hthird).
Qed.

Lemma raw_dynamicTruthPiCoqLowerApplication_target_atomically_adequate :
    forall (M : RawPAModel), RawPASatisfies M -> forall input output,
  RawDynamicTruthPiCoqLowerApplication M input output ->
  RawCodedFormulaAtomicallyAdequate M output.
Proof.
  intros M hPA input output (first & second & _ & _ & hthird).
  exact (raw_fixedReplacement_substitution_target_atomically_adequate
    M hPA dynamicTruthPiCoqLowerThirdReplacement second output hthird).
Qed.

(** The earlier lightweight linkage relation retained only equalities between
    the selected row *codes*.  That is enough to prevent completely unrelated
    rows, but not enough to recover the operation traces of its four exposed
    parameters without first proving injectivity of the large row
    polynomial.  The staged compiler needs those traces, so this stronger
    relation keeps the actual witnesses produced by the paired successor. *)
Definition RawDynamicTruthNativeLocalExactRowParametersAt
    (M : RawPAModel)
    (predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication : M) : Prop :=
  exists inputLevel evidenceGlobalSigma evidenceGlobalPi
      localSigmaRow localPiRow sigmaUpperNumeral piUpperNumeral : M,
    inputLevel = raw_succ M predecessorLevel /\
    RawNumeralTermCodeAt M (raw_succ M inputLevel) sigmaUpperNumeral /\
    RawCodedFormulaSingleSubstitution M sigmaUpperNumeral
      (rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode)
      sigmaRowDomain /\
    RawDynamicTruthCoqLowerApplication M
      inputGlobalPi lowerPiApplication /\
    localSigmaRow = rawDynamicTruthSigmaSuccessorRowCode M
      sigmaRowDomain lowerPiApplication /\
    RawNumeralTermCodeAt M (raw_succ M inputLevel) piUpperNumeral /\
    RawCodedFormulaSingleSubstitution M piUpperNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthPiRowDomainTemplate))
      piRowDomain /\
    RawDynamicTruthPiCoqLowerApplication M
      inputGlobalSigma lowerSigmaApplication /\
    localPiRow = rawDynamicTruthPiSuccessorRowCode M
      piRowDomain lowerSigmaApplication /\
    RawDynamicTruthPairedGlobalWrapperAt M
      localSigmaRow localPiRow evidenceGlobalSigma evidenceGlobalPi /\
    RawDynamicTruthLocalTernaryApplication M
      evidenceGlobalSigma sigmaEvidence /\
    RawDynamicTruthLocalTernaryApplication M
      evidenceGlobalPi piEvidence.

Arguments RawDynamicTruthNativeLocalExactRowParametersAt
  M predecessorLevel inputGlobalSigma inputGlobalPi
  sigmaEvidence piEvidence sigmaRowDomain piRowDomain
  lowerPiApplication lowerSigmaApplication : clear implicits.

Theorem raw_dynamicTruthNativeLocalProofTraceAt_exposes_exact_rows : forall
    (M : RawPAModel) (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
  RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  exists sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication : M,
    RawDynamicTruthNativeLocalExactRowParametersAt M predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication.
Proof.
  intros M tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence
    (_ & inputLevel & evidenceGlobalSigma & evidenceGlobalPi &
      inputLevelNumeral & hlevel & hsuccessor & _ & _ & _ &
      hsigmaEvidence & hpiEvidence).
  destruct hsuccessor as
    (localSigmaRow & localPiRow & [hsigmaRow hpiRow] & hwrapper).
  destruct hsigmaRow as
    (sigmaUpperNumeral & sigmaRowDomain & lowerPiApplication &
      hsigmaNumeral & hsigmaDomain & hlowerPi & hsigmaRowCode).
  destruct hpiRow as
    (piUpperNumeral & piRowDomain & lowerSigmaApplication &
      hpiNumeral & hpiDomain & hlowerSigma & hpiRowCode).
  destruct hwrapper as (hsigmaWrapper & hpiWrapper).
  exists sigmaRowDomain, piRowDomain,
    lowerPiApplication, lowerSigmaApplication.
  exists inputLevel, evidenceGlobalSigma, evidenceGlobalPi,
    localSigmaRow, localPiRow, sigmaUpperNumeral, piUpperNumeral.
  repeat split; assumption.
Qed.

Theorem raw_dynamicTruthNativeLocalExactRows_linked : forall
    (M : RawPAModel) predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthNativeLocalExactRowParametersAt M predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthNativeTraceRowParametersAt M predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication.
Proof.
  intros M predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaEvidence piEvidence sigmaRowDomain piRowDomain lowerPi lowerSigma
    (inputLevel & evidenceGlobalSigma & evidenceGlobalPi &
      localSigmaRow & localPiRow & sigmaNumeral & piNumeral &
      hlevel & hsigmaNumeral & hsigmaDomain & hlowerPi & hsigmaRow &
      hpiNumeral & hpiDomain & hlowerSigma & hpiRow & hwrapper &
      hsigmaEvidence & hpiEvidence).
  exists inputLevel, evidenceGlobalSigma, evidenceGlobalPi,
    localSigmaRow, localPiRow.
  split; [exact hlevel |].
  split.
  - split.
    + exists sigmaNumeral, sigmaRowDomain, lowerPi.
      repeat split; assumption.
    + exists piNumeral, piRowDomain, lowerSigma.
      repeat split; assumption.
  - split; [exact hwrapper |].
    split; [exact hsigmaEvidence |].
    split; [exact hpiEvidence |].
    split; assumption.
Qed.

Record RawDynamicTruthNativeLocalTraceAdequacyAt
    (M : RawPAModel)
    (sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication : M) : Prop := {
  rawDynamicTruthNativeLocalTrace_sigmaDomain_adequate :
    RawCodedFormulaAtomicallyAdequate M sigmaDomain;
  rawDynamicTruthNativeLocalTrace_piDomain_adequate :
    RawCodedFormulaAtomicallyAdequate M piDomain;
  rawDynamicTruthNativeLocalTrace_sigmaEvidence_adequate :
    RawCodedFormulaAtomicallyAdequate M sigmaEvidence;
  rawDynamicTruthNativeLocalTrace_piEvidence_adequate :
    RawCodedFormulaAtomicallyAdequate M piEvidence;
  rawDynamicTruthNativeLocalTrace_admissible_adequate :
    RawCodedFormulaAtomicallyAdequate M
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain);
  rawDynamicTruthNativeLocalTrace_sigmaRowDomain_adequate :
    RawCodedFormulaAtomicallyAdequate M sigmaRowDomain;
  rawDynamicTruthNativeLocalTrace_piRowDomain_adequate :
    RawCodedFormulaAtomicallyAdequate M piRowDomain;
  rawDynamicTruthNativeLocalTrace_lowerPi_adequate :
    RawCodedFormulaAtomicallyAdequate M lowerPiApplication;
  rawDynamicTruthNativeLocalTrace_lowerSigma_adequate :
    RawCodedFormulaAtomicallyAdequate M lowerSigmaApplication
}.

Arguments RawDynamicTruthNativeLocalTraceAdequacyAt
  M sigmaDomain piDomain sigmaEvidence piEvidence
  sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
  : clear implicits.

Theorem raw_dynamicTruthNativeLocalProofTraceAt_linked_adequacy : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  RawDynamicTruthNativeLocalExactRowParametersAt M predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthNativeLocalTraceAdequacyAt M
    sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma htrace hlinked.
  destruct htrace as
    (horbit & inputLevel & evidenceGlobalSigma & evidenceGlobalPi &
      inputLevelNumeral & hlevel & hsuccessor & hinputNumeral &
      hsigmaDomain & hpiDomain & hsigmaEvidence & hpiEvidence).
  destruct hlinked as
    (linkedInputLevel & linkedEvidenceSigma & linkedEvidencePi &
      localSigmaRow & localPiRow & sigmaUpperNumeral & piUpperNumeral &
      hlinkedLevel & hsigmaNumeral & hlinkedSigmaDomain &
      hlinkedLowerPi & hsigmaRowCode & hpiNumeral & hlinkedPiDomain &
      hlinkedLowerSigma & hpiRowCode & hwrapper &
      hlinkedSigmaEvidence & hlinkedPiEvidence).
  assert (hsigmaDomainAdequate :
      RawCodedFormulaAtomicallyAdequate M sigmaDomain).
  { exact (raw_dynamicTruthDomain_target_atomically_adequate
      M hPA inputLevel inputLevelNumeral
      (formulaCode dynamicTruthLocalSigmaInputDomainTemplate)
      sigmaDomain hinputNumeral hsigmaDomain). }
  assert (hpiDomainAdequate :
      RawCodedFormulaAtomicallyAdequate M piDomain).
  { exact (raw_dynamicTruthDomain_target_atomically_adequate
      M hPA inputLevel inputLevelNumeral
      (formulaCode dynamicTruthLocalPiInputDomainTemplate)
      piDomain hinputNumeral hpiDomain). }
  assert (hsigmaRowDomainAdequate :
      RawCodedFormulaAtomicallyAdequate M sigmaRowDomain).
  { exact (raw_dynamicTruthDomain_target_atomically_adequate
      M hPA (raw_succ M linkedInputLevel) sigmaUpperNumeral
      dynamicTruthSigmaRowDomainTemplateCode sigmaRowDomain
      hsigmaNumeral hlinkedSigmaDomain). }
  assert (hpiRowDomainAdequate :
      RawCodedFormulaAtomicallyAdequate M piRowDomain).
  { exact (raw_dynamicTruthDomain_target_atomically_adequate
      M hPA (raw_succ M linkedInputLevel) piUpperNumeral
      (formulaCode dynamicTruthPiRowDomainTemplate) piRowDomain
      hpiNumeral hlinkedPiDomain). }
  refine
    {| rawDynamicTruthNativeLocalTrace_sigmaDomain_adequate :=
         hsigmaDomainAdequate;
       rawDynamicTruthNativeLocalTrace_piDomain_adequate :=
         hpiDomainAdequate;
       rawDynamicTruthNativeLocalTrace_sigmaEvidence_adequate :=
         raw_dynamicTruthLocalTernaryApplication_target_atomically_adequate
           M hPA evidenceGlobalSigma sigmaEvidence hsigmaEvidence;
       rawDynamicTruthNativeLocalTrace_piEvidence_adequate :=
         raw_dynamicTruthLocalTernaryApplication_target_atomically_adequate
           M hPA evidenceGlobalPi piEvidence hpiEvidence;
       rawDynamicTruthNativeLocalTrace_admissible_adequate :=
         raw_dynamicTruthLocalAdmissibleCode_atomically_adequate
           M hPA sigmaDomain piDomain
           hsigmaDomainAdequate hpiDomainAdequate;
       rawDynamicTruthNativeLocalTrace_sigmaRowDomain_adequate :=
         hsigmaRowDomainAdequate;
       rawDynamicTruthNativeLocalTrace_piRowDomain_adequate :=
         hpiRowDomainAdequate;
       rawDynamicTruthNativeLocalTrace_lowerPi_adequate :=
         raw_dynamicTruthCoqLowerApplication_target_atomically_adequate
           M hPA inputGlobalPi lowerPi hlinkedLowerPi;
       rawDynamicTruthNativeLocalTrace_lowerSigma_adequate :=
         raw_dynamicTruthPiCoqLowerApplication_target_atomically_adequate
           M hPA inputGlobalSigma lowerSigma hlinkedLowerSigma |}.
Qed.

(** ------------------------------------------------------------------
    Finite case resources are determined by syntax adequacy. *)

Lemma raw_finiteRightDisjunctionCode_atomically_adequate_of_members :
    forall (M : RawPAModel), RawPASatisfies M -> forall branches,
  (forall branch, In branch branches ->
    RawCodedFormulaAtomicallyAdequate M branch) ->
  RawCodedFormulaAtomicallyAdequate M
    (rawFiniteRightDisjunctionCode M branches).
Proof.
  intros M hPA branches.
  induction branches as [| head tail ih]; intro hall.
  - cbn [rawFiniteRightDisjunctionCode].
    exact (raw_formulaBotCode_atomically_adequate M hPA).
  - destruct tail as [| second rest].
    + cbn [rawFiniteRightDisjunctionCode].
      apply hall. now left.
    + cbn [rawFiniteRightDisjunctionCode].
      apply (raw_formulaOrCode_atomically_adequate M hPA).
      * apply hall. now left.
      * apply ih. intros branch hbranch.
        apply hall. now right.
Qed.

Lemma raw_finiteDisjunctionConsTransplantAdequate_of_members :
    forall (M : RawPAModel), RawPASatisfies M -> forall branches,
  (forall branch, In branch branches ->
    RawCodedFormulaAtomicallyAdequate M branch) ->
  RawFiniteDisjunctionConsTransplantAdequate M branches.
Proof.
  intros M hPA branches.
  induction branches as [| head tail ih]; intro hall.
  - exact I.
  - destruct tail as [| second rest].
    + exact I.
    + cbn [RawFiniteDisjunctionConsTransplantAdequate].
      split.
      * apply hall. now left.
      * split.
        -- apply
             (raw_finiteRightDisjunctionCode_atomically_adequate_of_members
               M hPA (second :: rest)).
           intros branch hbranch. apply hall. now right.
        -- apply ih. intros branch hbranch. apply hall. now right.
Qed.

Lemma raw_finiteDisjunctionDerivedCaseResources_of_members :
    forall (M : RawPAModel), RawPASatisfies M -> forall branches context,
  RawContextListRealizable M context ->
  (forall branch, In branch branches ->
    RawCodedFormulaAtomicallyAdequate M branch) ->
  RawFiniteDisjunctionDerivedCaseResources M branches context.
Proof.
  intros M hPA branches context hcontext hall.
  destruct branches as [| first tail].
  - exact I.
  - destruct tail as [| second rest].
    + exact I.
    + cbn [RawFiniteDisjunctionDerivedCaseResources].
      split; [exact hcontext |].
      apply raw_finiteDisjunctionConsTransplantAdequate_of_members;
        assumption.
Qed.

Lemma raw_finiteDisjunctionMatrixResources_of_members :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      leftBranches rightBranches context,
  RawContextListRealizable M context ->
  (forall branch, In branch leftBranches ->
    RawCodedFormulaAtomicallyAdequate M branch) ->
  (forall branch, In branch rightBranches ->
    RawCodedFormulaAtomicallyAdequate M branch) ->
  RawFiniteDisjunctionMatrixResources M
    leftBranches rightBranches context.
Proof.
  intros M hPA leftBranches rightBranches context hcontext hleft hright.
  destruct leftBranches as [| leftHead leftTail]; [exact I |].
  destruct rightBranches as [| rightHead rightTail].
  - destruct leftTail; exact I.
  - destruct leftTail as [| leftSecond leftRest].
    + destruct rightTail as [| rightSecond rightRest].
      * exact I.
      * cbn [RawFiniteDisjunctionMatrixResources
          RawFiniteDisjunctionMatrixLeftResources].
        split.
        -- split; [exact hcontext |]. apply hleft. now left.
        -- apply raw_finiteDisjunctionDerivedCaseResources_of_members;
             assumption.
    + cbn [RawFiniteDisjunctionMatrixResources
        RawFiniteDisjunctionMatrixLeftResources].
      split.
      * split; [exact hcontext |].
        apply raw_finiteDisjunctionConsTransplantAdequate_of_members;
          assumption.
      * apply raw_finiteDisjunctionDerivedCaseResources_of_members;
          assumption.
Qed.

Lemma raw_dynamicTruthLocalSigmaBranches_member_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerPiApplication,
  RawCodedFormulaAtomicallyAdequate M lowerPiApplication ->
  forall branch,
  In branch (rawDynamicTruthLocalSigmaBranches M lowerPiApplication) ->
  RawCodedFormulaAtomicallyAdequate M branch.
Proof.
  intros M hPA lowerPi hlower branch hbranch.
  unfold rawDynamicTruthLocalSigmaBranches in hbranch.
  apply in_map_iff in hbranch.
  destruct hbranch as [selected [<- _]].
  destruct selected;
    cbn [rawDynamicTruthLocalSigmaBranchCode].
  - rewrite rawDynamicTruthSigmaQFEx8BranchCode_eq_numeral by exact hPA.
    exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
      dynamicTruthSigmaQFEx8BranchFormula).
  - rewrite rawDynamicTruthSigmaImpFalseLeftEx8BranchCode_eq_quoted
      by exact hPA.
    apply raw_quotedFormula_atomically_adequate. exact hPA.
  - rewrite rawDynamicTruthSigmaImpTrueRightEx8BranchCode_eq_quoted
      by exact hPA.
    apply raw_quotedFormula_atomically_adequate. exact hPA.
  - rewrite rawDynamicTruthSigmaAndEx8BranchCode_eq_quoted by exact hPA.
    apply raw_quotedFormula_atomically_adequate. exact hPA.
  - rewrite rawDynamicTruthSigmaOrEx8BranchCode_eq_quoted by exact hPA.
    apply raw_quotedFormula_atomically_adequate. exact hPA.
  - rewrite rawDynamicTruthSigmaEx8BranchCode_eq_quoted by exact hPA.
    apply raw_quotedFormula_atomically_adequate. exact hPA.
  - unfold rawDynamicTruthSigmaUniversalEx8BranchCode,
      rawFormulaEx8Code.
    repeat apply raw_formulaExCode_atomically_adequate; try exact hPA.
    unfold rawCoqDynamicTruthSigmaUniversalLeafTemplateCode.
    apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
    + apply raw_quotedFormula_atomically_adequate. exact hPA.
    + apply raw_formulaImpCode_atomically_adequate; [exact hPA | |].
      * unfold rawFormulaEx3Code.
        repeat apply raw_formulaExCode_atomically_adequate; try exact hPA.
        apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
        -- apply raw_quotedFormula_atomically_adequate. exact hPA.
        -- exact hlower.
      * exact (raw_formulaBotCode_atomically_adequate M hPA).
Qed.

Lemma raw_dynamicTruthLocalPiBranches_member_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerSigmaApplication,
  RawCodedFormulaAtomicallyAdequate M lowerSigmaApplication ->
  forall branch,
  In branch (rawDynamicTruthLocalPiBranches M lowerSigmaApplication) ->
  RawCodedFormulaAtomicallyAdequate M branch.
Proof.
  intros M hPA lowerSigma hlower branch hbranch.
  unfold rawDynamicTruthLocalPiBranches in hbranch.
  apply in_map_iff in hbranch.
  destruct hbranch as [selected [<- _]].
  destruct selected;
    cbn [rawDynamicTruthLocalPiBranchCode].
  - rewrite rawDynamicTruthPiQFEx8BranchCode_eq_numeral by exact hPA.
    exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
      dynamicTruthPiQFEx8BranchFormula).
  - rewrite rawDynamicTruthPiImpEx8BranchCode_eq_quoted by exact hPA.
    apply raw_quotedFormula_atomically_adequate. exact hPA.
  - rewrite rawDynamicTruthPiAndEx8BranchCode_eq_quoted by exact hPA.
    apply raw_quotedFormula_atomically_adequate. exact hPA.
  - rewrite rawDynamicTruthPiOrEx8BranchCode_eq_quoted by exact hPA.
    apply raw_quotedFormula_atomically_adequate. exact hPA.
  - rewrite rawDynamicTruthPiAllEx8BranchCode_eq_quoted by exact hPA.
    apply raw_quotedFormula_atomically_adequate. exact hPA.
  - unfold rawDynamicTruthPiExistentialEx8BranchCode,
      rawDynamicTruthPiFormulaEx8Code.
    repeat apply raw_formulaExCode_atomically_adequate; try exact hPA.
    unfold rawCoqDynamicTruthPiExistentialLeafTemplateCode.
    apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
    + apply raw_quotedFormula_atomically_adequate. exact hPA.
    + apply raw_formulaImpCode_atomically_adequate; [exact hPA | |].
      * unfold rawDynamicTruthPiFormulaEx3Code.
        repeat apply raw_formulaExCode_atomically_adequate; try exact hPA.
        apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
        -- apply raw_quotedFormula_atomically_adequate. exact hPA.
        -- exact hlower.
      * exact (raw_formulaBotCode_atomically_adequate M hPA).
Qed.

Corollary raw_dynamicTruthLocalCollisionMatrixResources_of_adequacy :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      context lowerPiApplication lowerSigmaApplication,
  RawContextListRealizable M context ->
  RawCodedFormulaAtomicallyAdequate M lowerPiApplication ->
  RawCodedFormulaAtomicallyAdequate M lowerSigmaApplication ->
  RawFiniteDisjunctionMatrixResources M
    (rawDynamicTruthLocalSigmaBranches M lowerPiApplication)
    (rawDynamicTruthLocalPiBranches M lowerSigmaApplication)
    context.
Proof.
  intros M hPA context lowerPi lowerSigma hcontext hlowerPi hlowerSigma.
  apply (raw_finiteDisjunctionMatrixResources_of_members
    M hPA _ _ context hcontext).
  - exact (raw_dynamicTruthLocalSigmaBranches_member_adequate
      M hPA lowerPi hlowerPi).
  - exact (raw_dynamicTruthLocalPiBranches_member_adequate
      M hPA lowerSigma hlowerSigma).
Qed.

(** ------------------------------------------------------------------
    Positional recovery of the sixteen fixed constructor pairs.

    A helper record contains a proof field, so two records formed with two
    proofs of the same membership proposition need not be convertible in
    intensional type theory.  The formula projection of either record is,
    however, definitionally the same.  The following adapter quantifies over
    the *actual* certificate stored at one batch position and then forgets
    that certificate before identifying the carrier target. *)

Lemma raw_dynamicTruthNativeLocal_fixed_helper_root_to_local : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      translation context lowerPiApplication lowerSigmaApplication
      sigmaBranch piBranch,
  RawCodedTemplatePAAgreement M translation ->
  DynamicTruthFixedConstructorCell sigmaBranch piBranch ->
  forall (certificate : Formula.BProv Formula.Ax_s []
      (dynamicTruthFixedConstructorBranchDisjointnessFormula
        sigmaBranch piBranch)) root,
  RawCodedPALocalProofOf M context
    (rawFixedPAHelperTranslatedTargetCode M translation
      {| rawFixedPAHelperFormula :=
           dynamicTruthFixedConstructorBranchDisjointnessFormula
             sigmaBranch piBranch;
         rawFixedPAHelperBProv := certificate |}) root ->
  RawDynamicTruthLocalRootAt M context
    (rawFormulaImpCode M
      (rawDynamicTruthLocalSigmaConstructorBranchCode M
        lowerPiApplication sigmaBranch)
      (rawFormulaImpCode M
        (rawDynamicTruthLocalPiConstructorBranchCode M
          lowerSigmaApplication piBranch)
        (rawFormulaBotCode M))).
Proof.
  intros M hPA translation context lowerPi lowerSigma
    sigmaBranch piBranch hagreement hcell certificate root hroot.
  change (RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (embedPAFormula
        (dynamicTruthFixedConstructorBranchDisjointnessFormula
          sigmaBranch piBranch))) root) in hroot.
  rewrite (rawTemplateFormula_embedPA hagreement) in hroot.
  unfold dynamicTruthFixedConstructorBranchDisjointnessFormula in hroot.
  rewrite <- (rawDynamicTruthConstructorBranchDisjointnessCode_eq_quoted
    M hPA sigmaBranch pBot piBranch pBot) in hroot.
  change (RawCodedPALocalProofOf M context
    (rawDynamicTruthFixedConstructorBranchDisjointnessCode M
      sigmaBranch piBranch) root) in hroot.
  rewrite (rawDynamicTruthFixedConstructorCode_eq_local
    M hPA sigmaBranch piBranch hcell lowerPi lowerSigma) in hroot.
  now exists root.
Qed.

Theorem raw_dynamicTruthNativeLocal_fixedPairs_of_40_helpers : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      translation context roots lowerPiApplication lowerSigmaApplication,
  RawCodedTemplatePAAgreement M translation ->
  RawFixedPAHelperBatchLocalProofs M translation context
    rawDynamicTruthReadyAndAllMixedQFPAHelpers roots ->
  RawDynamicTruthLocalFixedPairFamily M context
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA translation context roots lowerPi lowerSigma
    hagreement hhelpers.
  destruct (raw_dynamicTruthNativeLocal_fixedPairBatch_of_40_helpers
    M translation context roots hhelpers) as (fixedRoots & hfixed).
  pose proof (raw_fixedPAHelperBatchLocalProofs_length
    M translation context _ _ hfixed) as hlength.
  rewrite rawDynamicTruthFixedConstructorCollisionPAHelpers_length
    in hlength.
  unfold rawDynamicTruthFixedConstructorCollisionPAHelpers in hfixed.
  destruct fixedRoots as [| root1 fixedRoots]; [discriminate hlength |].
  destruct fixedRoots as [| root2 fixedRoots]; [discriminate hlength |].
  destruct fixedRoots as [| root3 fixedRoots]; [discriminate hlength |].
  destruct fixedRoots as [| root4 fixedRoots]; [discriminate hlength |].
  destruct fixedRoots as [| root5 fixedRoots]; [discriminate hlength |].
  destruct fixedRoots as [| root6 fixedRoots]; [discriminate hlength |].
  destruct fixedRoots as [| root7 fixedRoots]; [discriminate hlength |].
  destruct fixedRoots as [| root8 fixedRoots]; [discriminate hlength |].
  destruct fixedRoots as [| root9 fixedRoots]; [discriminate hlength |].
  destruct fixedRoots as [| root10 fixedRoots]; [discriminate hlength |].
  destruct fixedRoots as [| root11 fixedRoots]; [discriminate hlength |].
  destruct fixedRoots as [| root12 fixedRoots]; [discriminate hlength |].
  destruct fixedRoots as [| root13 fixedRoots]; [discriminate hlength |].
  destruct fixedRoots as [| root14 fixedRoots]; [discriminate hlength |].
  destruct fixedRoots as [| root15 fixedRoots]; [discriminate hlength |].
  destruct fixedRoots as [| root16 fixedRoots]; [discriminate hlength |].
  destruct fixedRoots; [| discriminate hlength].
  cbn [RawFixedPAHelperBatchLocalProofs] in hfixed.
  destruct hfixed as
    (hroot1 & hroot2 & hroot3 & hroot4 & hroot5 & hroot6 &
      hroot7 & hroot8 & hroot9 & hroot10 & hroot11 & hroot12 &
      hroot13 & hroot14 & hroot15 & hroot16 & _).
  intros sigmaBranch piBranch hcell.
  destruct sigmaBranch, piBranch;
    try (exfalso;
      unfold DynamicTruthFixedConstructorCell,
        DynamicTruthConstructorBranchesDisjoint in hcell;
      cbn [dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal] in hcell;
      intuition discriminate).
  - eapply (raw_dynamicTruthNativeLocal_fixed_helper_root_to_local M hPA);
      [exact hagreement | exact hcell | exact hroot1].
  - eapply (raw_dynamicTruthNativeLocal_fixed_helper_root_to_local M hPA);
      [exact hagreement | exact hcell | exact hroot2].
  - eapply (raw_dynamicTruthNativeLocal_fixed_helper_root_to_local M hPA);
      [exact hagreement | exact hcell | exact hroot3].
  - eapply (raw_dynamicTruthNativeLocal_fixed_helper_root_to_local M hPA);
      [exact hagreement | exact hcell | exact hroot4].
  - eapply (raw_dynamicTruthNativeLocal_fixed_helper_root_to_local M hPA);
      [exact hagreement | exact hcell | exact hroot5].
  - eapply (raw_dynamicTruthNativeLocal_fixed_helper_root_to_local M hPA);
      [exact hagreement | exact hcell | exact hroot6].
  - eapply (raw_dynamicTruthNativeLocal_fixed_helper_root_to_local M hPA);
      [exact hagreement | exact hcell | exact hroot7].
  - eapply (raw_dynamicTruthNativeLocal_fixed_helper_root_to_local M hPA);
      [exact hagreement | exact hcell | exact hroot8].
  - eapply (raw_dynamicTruthNativeLocal_fixed_helper_root_to_local M hPA);
      [exact hagreement | exact hcell | exact hroot9].
  - eapply (raw_dynamicTruthNativeLocal_fixed_helper_root_to_local M hPA);
      [exact hagreement | exact hcell | exact hroot10].
  - eapply (raw_dynamicTruthNativeLocal_fixed_helper_root_to_local M hPA);
      [exact hagreement | exact hcell | exact hroot11].
  - eapply (raw_dynamicTruthNativeLocal_fixed_helper_root_to_local M hPA);
      [exact hagreement | exact hcell | exact hroot12].
  - eapply (raw_dynamicTruthNativeLocal_fixed_helper_root_to_local M hPA);
      [exact hagreement | exact hcell | exact hroot13].
  - eapply (raw_dynamicTruthNativeLocal_fixed_helper_root_to_local M hPA);
      [exact hagreement | exact hcell | exact hroot14].
  - eapply (raw_dynamicTruthNativeLocal_fixed_helper_root_to_local M hPA);
      [exact hagreement | exact hcell | exact hroot15].
  - eapply (raw_dynamicTruthNativeLocal_fixed_helper_root_to_local M hPA);
      [exact hagreement | exact hcell | exact hroot16].
Qed.

(** ------------------------------------------------------------------
    The genuinely current-field collision kernel.

    Context realizability/self-shift and all sixteen fixed pairs are no
    longer residuals: the witnessed helper context supplies them.  What
    remains is precisely the carrier-dependent information that the fixed
    batch cannot know before the current successor edge is selected. *)

Record RawDynamicTruthNativeLocalCurrentKernelInputsAt
    (M : RawPAModel) (context lowerPiApplication lowerSigmaApplication : M)
    : Type := {
  rawDynamicTruthNativeLocalCurrentKernel_predecessorRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthImpPredecessorStateExclusivityCode M);
  rawDynamicTruthNativeLocalCurrentKernel_binderProjections :
    forall cell : DynamicTruthBinderOffDiagonalCell,
      RawDynamicTruthBinderPrincipalProjectionInterfaceAt M context cell
        lowerPiApplication lowerSigmaApplication;
  rawDynamicTruthNativeLocalCurrentKernel_sigmaExTrace :
    RawDynamicTruthQuantifierLowerApplicationDirectTrace
      M lowerSigmaApplication;
  rawDynamicTruthNativeLocalCurrentKernel_sigmaAllTrace :
    RawDynamicTruthQuantifierLowerApplicationDirectTrace
      M lowerPiApplication;
  rawDynamicTruthNativeLocalCurrentKernel_sigmaExCrossRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthSigmaExPiExCrossLevelPremiseCode M
        lowerSigmaApplication);
  rawDynamicTruthNativeLocalCurrentKernel_sigmaAllCrossRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthSigmaAllPiAllCrossLevelPremiseCode M
        lowerPiApplication);
  rawDynamicTruthNativeLocalCurrentKernel_mixedReplayRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthMixedQFReplayExclusivityCode M)
}.

Arguments RawDynamicTruthNativeLocalCurrentKernelInputsAt
  M context lowerPiApplication lowerSigmaApplication : clear implicits.

Theorem
    raw_dynamicTruthNativeLocalCollisionResidualInputsAt_of_current_kernel :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      translation witnessList context helperRoots
      lowerPiApplication lowerSigmaApplication,
  RawCodedTemplatePAAgreement M translation ->
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawFixedPAHelperBatchLocalProofs M translation context
    rawDynamicTruthReadyAndAllMixedQFPAHelpers helperRoots ->
  RawCodedFormulaAtomicallyAdequate M lowerPiApplication ->
  RawCodedFormulaAtomicallyAdequate M lowerSigmaApplication ->
  RawDynamicTruthNativeLocalCurrentKernelInputsAt M context
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthNativeLocalCollisionResidualInputsAt M context
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA translation witnessList context helperRoots
    lowerPi lowerSigma hagreement hwitness hhelpers
    hlowerPi hlowerSigma kernel.
  destruct kernel as
    [hpredecessor hbinder hsigmaExTrace hsigmaAllTrace
      hsigmaExCross hsigmaAllCross hmixedReplay].
  refine
    {| rawDynamicTruthNativeLocalCollision_contextRealizable :=
         raw_codedPAAxiomWitnessContext_context_realizable
           M witnessList context hwitness;
       rawDynamicTruthNativeLocalCollision_lowerPiAdequate := hlowerPi;
       rawDynamicTruthNativeLocalCollision_lowerSigmaAdequate := hlowerSigma;
       rawDynamicTruthNativeLocalCollision_contextSelfShift :=
         raw_codedPAAxiomWitnessContext_selfShift
           M hPA witnessList context hwitness;
       rawDynamicTruthNativeLocalCollision_predecessorRoot := hpredecessor;
       rawDynamicTruthNativeLocalCollision_fixedPairs :=
         raw_dynamicTruthNativeLocal_fixedPairs_of_40_helpers
           M hPA translation context helperRoots lowerPi lowerSigma
           hagreement hhelpers;
       rawDynamicTruthNativeLocalCollision_binderProjections := hbinder;
       rawDynamicTruthNativeLocalCollision_sigmaExTrace := hsigmaExTrace;
       rawDynamicTruthNativeLocalCollision_sigmaAllTrace := hsigmaAllTrace;
       rawDynamicTruthNativeLocalCollision_sigmaExCrossRoot := hsigmaExCross;
       rawDynamicTruthNativeLocalCollision_sigmaAllCrossRoot :=
         hsigmaAllCross;
       rawDynamicTruthNativeLocalCollision_mixedReplayRoot := hmixedReplay |}.
Qed.

(** ------------------------------------------------------------------
    One trace-linked staged root package on the visible context. *)

Definition RawDynamicTruthNativeLocalStagedRootsAt
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication : M) : Prop :=
    RawDynamicTruthNativeLocalDomainCaseDecisionRootsAt M
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence /\
    RawDynamicTruthLocalRootAt M
      (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
        sigmaDomain piDomain sigmaEvidence piEvidence)
      (rawDynamicTruthSigmaSuccessorRowCode M
        sigmaRowDomain lowerPiApplication) /\
    RawDynamicTruthLocalRootAt M
      (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
        sigmaDomain piDomain sigmaEvidence piEvidence)
      (rawDynamicTruthPiSuccessorRowCode M
        piRowDomain lowerSigmaApplication) /\
    exists currentKernel :
        RawDynamicTruthNativeLocalCurrentKernelInputsAt M baseContext
          lowerPiApplication lowerSigmaApplication,
      RawContextShift M
        (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
          sigmaDomain piDomain)
        (rawDynamicTruthNativeLocalAdmissibleContextOn M baseContext
          sigmaDomain piDomain) /\
      RawContextShift M
        (rawDynamicTruthNativeLocalExclusiveSigmaContextOn M baseContext
          sigmaDomain piDomain sigmaEvidence)
        (rawDynamicTruthNativeLocalExclusiveSigmaContextOn M baseContext
          sigmaDomain piDomain sigmaEvidence) /\
      RawContextShift M
        (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
          sigmaDomain piDomain sigmaEvidence piEvidence)
        (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
          sigmaDomain piDomain sigmaEvidence piEvidence) /\
      exists sigmaProjection :
          RawDynamicTruthSigmaSuccessorRowBranchDisjunctionCompilationInputs M
            (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
              sigmaDomain piDomain sigmaEvidence piEvidence)
            sigmaRowDomain lowerPiApplication,
        exists piProjection :
          RawDynamicTruthPiSuccessorRowBranchDisjunctionCompilationInputs M
            (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
              sigmaDomain piDomain sigmaEvidence piEvidence)
            piRowDomain lowerSigmaApplication,
          True.

Arguments RawDynamicTruthNativeLocalStagedRootsAt
  M baseContext sigmaDomain piDomain sigmaEvidence piEvidence
  sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
  : clear implicits.

(** The theorem consumes only one trace and its exact row linkage.  Thus the
    two row roots, their projection traces, and every collision input all
    refer to the same four successor witnesses; unrelated row parameters
    cannot be substituted into the package. *)
Theorem
    raw_dynamicTruthNativeLocalLeafRootsOn_of_staged_roots_and_40_helpers :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      translation witnessList baseContext helperRoots
      (tail : nat -> M) predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication,
  RawCodedTemplatePAAgreement M translation ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawFixedPAHelperBatchLocalProofs M translation baseContext
    rawDynamicTruthReadyAndAllMixedQFPAHelpers helperRoots ->
  RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  RawDynamicTruthNativeLocalExactRowParametersAt M predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthNativeLocalStagedRootsAt M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthNativeLocalLeafRootsOn M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M hPA translation witnessList baseContext helperRoots
    tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma
    hagreement hwitness hhelpers htrace hlinked staged.
  pose proof (raw_dynamicTruthNativeLocalProofTraceAt_linked_adequacy
    M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma htrace hlinked)
    as adequacy.
  destruct adequacy as
    [hsigmaDomain hpiDomain hsigmaEvidence hpiEvidence hadmissible
      hsigmaRowDomain hpiRowDomain hlowerPi hlowerSigma].
  destruct staged as
    (hcases & hsigmaRow & hpiRow & hkernel &
      hadmissibleShift & hsigmaShift & hpiShift &
      hsigmaProjection & hpiProjection & _).
  pose proof
    (raw_dynamicTruthNativeLocalCollisionResidualInputsAt_of_current_kernel
      M hPA translation witnessList baseContext helperRoots
      lowerPi lowerSigma hagreement hwitness hhelpers
      hlowerPi hlowerSigma hkernel) as residual.
  set (exclusiveContext :=
    rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence).
  assert (matrixResources :
      RawFiniteDisjunctionMatrixResources M
        (rawDynamicTruthLocalSigmaBranches M lowerPi)
        (rawDynamicTruthLocalPiBranches M lowerSigma)
        exclusiveContext).
  { apply (raw_dynamicTruthLocalCollisionMatrixResources_of_adequacy
      M hPA exclusiveContext lowerPi lowerSigma).
    - exact (rawDynamicTruthSigmaBranchDisjunction_contextRealizable
        hsigmaProjection).
    - exact hlowerPi.
    - exact hlowerSigma. }
  pose proof
    (raw_dynamicTruthNativeLocalExclusiveMatrixResourcesAt_of_40_helpers
      M hPA translation witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPi lowerSigma
      hagreement hwitness hhelpers residual
      hadmissible hsigmaEvidence hpiEvidence
      hadmissibleShift hsigmaShift hpiShift
      hsigmaProjection hpiProjection matrixResources) as matrix.
  split.
  - apply (raw_dynamicTruthNativeLocalDecisionRootOn_of_structural_roots
      M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence).
    + apply (raw_dynamicTruthNativeLocalAdmissibleDomainRootAt_realizable
        M hPA baseContext sigmaDomain piDomain).
      exact (raw_codedPAAxiomWitnessContext_context_realizable
        M witnessList baseContext hwitness).
    + exact hcases.
  - apply (raw_dynamicTruthNativeLocalExclusiveRootOn_of_rows_and_matrix
      M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPi lowerSigma matrix).
    destruct hsigmaRow as [sigmaRowRoot hsigmaRow].
    destruct hpiRow as [piRowRoot hpiRow].
    exists sigmaRowRoot, piRowRoot. now split.
Qed.

Corollary
    raw_dynamicTruthNativeLocalFieldRootOn_of_staged_roots_and_40_helpers :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      translation witnessList baseContext helperRoots
      (tail : nat -> M) predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication,
  RawCodedTemplatePAAgreement M translation ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawFixedPAHelperBatchLocalProofs M translation baseContext
    rawDynamicTruthReadyAndAllMixedQFPAHelpers helperRoots ->
  RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  RawDynamicTruthNativeLocalExactRowParametersAt M predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthNativeLocalStagedRootsAt M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthNativeLocalFieldRootOn M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M hPA translation witnessList baseContext helperRoots
    tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma
    hagreement hwitness hhelpers htrace hlinked staged.
  apply (raw_dynamicTruthNativeLocalFieldRootOn_of_leaf_roots
    M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence).
  - exact (raw_codedPAAxiomWitnessContext_selfShift
      M hPA witnessList baseContext hwitness).
  - exact
      (raw_dynamicTruthNativeLocalLeafRootsOn_of_staged_roots_and_40_helpers
        M hPA translation witnessList baseContext helperRoots
        tail predecessorLevel inputGlobalSigma inputGlobalPi
        sigmaDomain piDomain sigmaEvidence piEvidence
        sigmaRowDomain piRowDomain lowerPi lowerSigma
        hagreement hwitness hhelpers htrace hlinked staged).
Qed.

(** A synchronized compiler cannot choose four unrelated carrier values.
    It must return a staged package together with the exact linkage exposed
    by the very trace it is compiling. *)
Definition RawDynamicTruthNativeLocalVisibleStagedRootCompilerOn
    (M : RawPAModel) (baseContext : M) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    exists sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication : M,
      RawDynamicTruthNativeLocalExactRowParametersAt M predecessorLevel
        inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
        sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication /\
      RawDynamicTruthNativeLocalStagedRootsAt M baseContext
        sigmaDomain piDomain sigmaEvidence piEvidence
        sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication.

Arguments RawDynamicTruthNativeLocalVisibleStagedRootCompilerOn
  M baseContext : clear implicits.

Definition RawDynamicTruthNativeLocalVisibleLeafRootCompilerOn
    (M : RawPAModel) (baseContext : M) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    RawDynamicTruthNativeLocalLeafRootsOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence.

Arguments RawDynamicTruthNativeLocalVisibleLeafRootCompilerOn
  M baseContext : clear implicits.

Theorem
    raw_dynamicTruthNativeLocalVisibleLeafRootCompilerOn_of_staged_roots :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      translation witnessList baseContext helperRoots,
  RawCodedTemplatePAAgreement M translation ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawFixedPAHelperBatchLocalProofs M translation baseContext
    rawDynamicTruthReadyAndAllMixedQFPAHelpers helperRoots ->
  RawDynamicTruthNativeLocalVisibleStagedRootCompilerOn M baseContext ->
  RawDynamicTruthNativeLocalVisibleLeafRootCompilerOn M baseContext.
Proof.
  intros M hPA translation witnessList baseContext helperRoots
    hagreement hwitness hhelpers hstagedCompiler
    tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence htrace.
  destruct (hstagedCompiler tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence htrace) as
    (sigmaRowDomain & piRowDomain & lowerPi & lowerSigma &
      hlinked & hstaged).
  exact
    (raw_dynamicTruthNativeLocalLeafRootsOn_of_staged_roots_and_40_helpers
      M hPA translation witnessList baseContext helperRoots
      tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPi lowerSigma
      hagreement hwitness hhelpers htrace hlinked hstaged).
Qed.

(** The exact-row witness itself is never an extra mathematical assumption:
    every native proof trace exposes one.  This helper packages the common
    situation in which a kernel callback can build staged roots for whichever
    exact witnesses the trace reveals. *)
Definition RawDynamicTruthNativeLocalExactStagedRootBuilderOn
    (M : RawPAModel) (baseContext : M) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication,
    RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    RawDynamicTruthNativeLocalExactRowParametersAt M predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication ->
    RawDynamicTruthNativeLocalStagedRootsAt M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication.

Arguments RawDynamicTruthNativeLocalExactStagedRootBuilderOn
  M baseContext : clear implicits.

Lemma
    raw_dynamicTruthNativeLocalVisibleStagedRootCompilerOn_of_exact_builder :
    forall (M : RawPAModel) baseContext,
  RawDynamicTruthNativeLocalExactStagedRootBuilderOn M baseContext ->
  RawDynamicTruthNativeLocalVisibleStagedRootCompilerOn M baseContext.
Proof.
  intros M baseContext hbuilder tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence htrace.
  destruct (raw_dynamicTruthNativeLocalProofTraceAt_exposes_exact_rows
    M tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence htrace) as
    (sigmaRowDomain & piRowDomain & lowerPi & lowerSigma & hlinked).
  exists sigmaRowDomain, piRowDomain, lowerPi, lowerSigma.
  split; [exact hlinked |].
  exact (hbuilder tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma htrace hlinked).
Qed.

End PABoundedRawCodedDynamicTruthNativeLocalStagedRootCompilation.
