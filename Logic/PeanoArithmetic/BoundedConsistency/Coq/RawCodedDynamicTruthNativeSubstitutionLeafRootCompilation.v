(**
  Trace-linked leaf compilation for the native formula-substitution field.

  [RawCodedDynamicTruthNativeSubstitutionProofCompilation] exposes four
  implication roots in the literal context whose head is the complete
  substitution side-condition conjunction.  This file factors each such
  implication through its genuinely proof-producing directional leaf: the
  source certificate is added as a visible assumption, the target
  certificate is proved in that extended context, and implication
  introduction discharges only that assumption.

  A base context is retained throughout.  This is essential for the raw
  calculus: arithmetic lemmas may use an honest witnessed PA-axiom tail, and
  there is no rule which silently erases that tail.  Specialization to the
  historical empty context is therefore exposed only as a conditional
  adapter.

  Everything structurally available from the graph trace is compiled here:

  - the two numeral-driven domain substitutions and four represented
    three-step applications yield atomic adequacy of all selected codes;
  - the five members of the nested antecedent conjunction are projected by
    concrete assumption and conjunction-elimination proof roots;
  - four directional target leaves are wrapped by concrete implication-
    introduction roots into the exact Sigma and Pi local-root bundles.

  The remaining interface is consequently trace-linked and receives all
  adequacy and side-condition proof resources which the trace itself can
  provide.  It asks only for the four target leaves.  No semantic validity,
  completeness, proof irrelevance, completed field proof, or context erasure
  is used below.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthOperationTransport
  RawCodedNumeralTermCode
  RawCodedFormulaSingleSubstitutionAtomicAdequacy
  RawCodedTermOpeningAfterShiftSyntaxStability
  RawCodedDynamicTruthTernaryApplicationTotality
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedRestrictedPAProof
  RawCodedProofAssumptionLeaf
  RawCodedProofImpIConstructor
  RawCodedProofAndIConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofAndIntroduction
  RawCodedPAProofImpICertificates
  RawCodedDynamicTruthPairedSuccessorAdequacy
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeSubstitutionCarrier
  RawCodedDynamicTruthNativeSubstitutionPositiveGraph
  RawCodedDynamicTruthNativeSubstitutionProofCompilation.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthNativeSubstitutionLeafRootCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthOperationTransport.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFormulaSingleSubstitutionAtomicAdequacy.
Import PABoundedRawCodedTermOpeningAfterShiftSyntaxStability.
Import PABoundedRawCodedDynamicTruthTernaryApplicationTotality.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofAndIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofAndIntroduction.
Import PABoundedRawCodedPAProofImpICertificates.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionCarrier.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionProofCompilation.

(** ------------------------------------------------------------------
    Exact contexts with a visible base tail. *)

Definition rawDynamicTruthNativeSubstitutionCommonContextOn
    (M : RawPAModel) (baseContext sigmaDomain piDomain : M) : M :=
  rawListNode M
    (rawDynamicTruthNativeSubstitutionAntecedentCode M
      sigmaDomain piDomain)
    baseContext.

Definition rawDynamicTruthNativeSubstitutionDirectionalContextOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain assumption : M) : M :=
  rawListNode M assumption
    (rawDynamicTruthNativeSubstitutionCommonContextOn M baseContext
      sigmaDomain piDomain).

Arguments rawDynamicTruthNativeSubstitutionCommonContextOn
  M baseContext sigmaDomain piDomain : clear implicits.
Arguments rawDynamicTruthNativeSubstitutionDirectionalContextOn
  M baseContext sigmaDomain piDomain assumption : clear implicits.

Lemma rawDynamicTruthNativeSubstitutionCommonContextOn_empty : forall
    (M : RawPAModel) sigmaDomain piDomain,
  rawDynamicTruthNativeSubstitutionCommonContextOn M (raw_zero M)
      sigmaDomain piDomain =
  rawDynamicTruthNativeSubstitutionCommonContext M sigmaDomain piDomain.
Proof.
  reflexivity.
Qed.

Lemma raw_dynamicTruthNativeSubstitutionCommonContextOn_realizable : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain,
  RawContextListRealizable M baseContext ->
  RawContextListRealizable M
    (rawDynamicTruthNativeSubstitutionCommonContextOn M baseContext
      sigmaDomain piDomain).
Proof.
  intros M hPA baseContext sigmaDomain piDomain hbase.
  exact (raw_contextList_cons_realizable M hPA baseContext
    (rawDynamicTruthNativeSubstitutionAntecedentCode M
      sigmaDomain piDomain) hbase).
Qed.

Lemma raw_dynamicTruthNativeSubstitutionDirectionalContextOn_realizable :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain assumption,
  RawContextListRealizable M baseContext ->
  RawContextListRealizable M
    (rawDynamicTruthNativeSubstitutionDirectionalContextOn M baseContext
      sigmaDomain piDomain assumption).
Proof.
  intros M hPA baseContext sigmaDomain piDomain assumption hbase.
  apply (raw_contextList_cons_realizable M hPA).
  exact (raw_dynamicTruthNativeSubstitutionCommonContextOn_realizable
    M hPA baseContext sigmaDomain piDomain hbase).
Qed.

(** ------------------------------------------------------------------
    Atomic adequacy already carried by the represented trace. *)

(** The final substitution in a three-step application uses a fixed
    standard replacement term.  Its checked syntax is therefore sufficient
    to obtain adequacy of the output; adequacy of the input is not smuggled
    in as an extra premise. *)
Lemma
    raw_dynamicTruthNativeSubstitutionApplication_target_atomically_adequate :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      firstReplacement secondReplacement thirdReplacement input output,
  RawDynamicTruthNativeSubstitutionApplication M
    firstReplacement secondReplacement thirdReplacement input output ->
  RawCodedFormulaAtomicallyAdequate M output.
Proof.
  intros M hPA firstReplacement secondReplacement thirdReplacement
    input output
    (firstResult & secondResult & _hfirst & _hsecond & hthird).
  exact (raw_codedFormulaSingleSubstitution_target_atomically_adequate
    M hPA (raw_codedTermOpeningAfterShiftSyntaxStable_of_PA M hPA)
    (rawNumeralValue M (termCode thirdReplacement))
    (raw_zero M) (raw_zero M)
    (raw_dynamicTruthApplication_fixedReplacement_syntax
      M hPA thirdReplacement)
    secondResult output hthird).
Qed.

(** Both input-domain codes are instances of fixed formula templates under
    the represented numeral selected by the trace. *)
Lemma raw_dynamicTruthNativeSubstitutionDomain_target_atomically_adequate :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      level numeralCode templateCode domain,
  RawNumeralTermCodeAt M level numeralCode ->
  RawCodedFormulaSingleSubstitution M numeralCode
    (rawNumeralValue M templateCode) domain ->
  RawCodedFormulaAtomicallyAdequate M domain.
Proof.
  intros M hPA level numeralCode templateCode domain
    hnumeral hsubstitution.
  exact (raw_codedFormulaSingleSubstitution_target_atomically_adequate
    M hPA (raw_codedTermOpeningAfterShiftSyntaxStable_of_PA M hPA)
    numeralCode (raw_zero M) (raw_zero M)
    (raw_numeralTermCode_syntax_realizable_zero
      M hPA level numeralCode hnumeral)
    (rawNumeralValue M templateCode) domain hsubstitution).
Qed.

Record RawDynamicTruthNativeSubstitutionProofTraceAdequacyAt
    (M : RawPAModel)
    (currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi : M) : Prop := {
  rawDynamicTruthNativeSubstitution_currentGlobalSigma_adequate :
    RawCodedFormulaAtomicallyAdequate M currentGlobalSigma;
  rawDynamicTruthNativeSubstitution_currentGlobalPi_adequate :
    RawCodedFormulaAtomicallyAdequate M currentGlobalPi;
  rawDynamicTruthNativeSubstitution_sigmaDomain_adequate :
    RawCodedFormulaAtomicallyAdequate M sigmaDomain;
  rawDynamicTruthNativeSubstitution_piDomain_adequate :
    RawCodedFormulaAtomicallyAdequate M piDomain;
  rawDynamicTruthNativeSubstitution_sourceSigma_adequate :
    RawCodedFormulaAtomicallyAdequate M sourceSigma;
  rawDynamicTruthNativeSubstitution_targetSigma_adequate :
    RawCodedFormulaAtomicallyAdequate M targetSigma;
  rawDynamicTruthNativeSubstitution_sourcePi_adequate :
    RawCodedFormulaAtomicallyAdequate M sourcePi;
  rawDynamicTruthNativeSubstitution_targetPi_adequate :
    RawCodedFormulaAtomicallyAdequate M targetPi
}.

Arguments RawDynamicTruthNativeSubstitutionProofTraceAdequacyAt
  M currentGlobalSigma currentGlobalPi sigmaDomain piDomain
  sourceSigma targetSigma sourcePi targetPi : clear implicits.

Theorem raw_dynamicTruthNativeSubstitutionProofTraceAt_adequacy : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  RawDynamicTruthNativeSubstitutionProofTraceAt M tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi ->
  RawDynamicTruthNativeSubstitutionProofTraceAdequacyAt M
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi.
Proof.
  intros M hPA tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    (horbit & currentLevel & currentLevelNumeral & hlevel & hnumeral &
      hsigmaDomain & hpiDomain & hsourceSigma & htargetSigma &
      hsourcePi & htargetPi).
  destruct (proj1
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M tail
      (raw_succ M predecessorLevel) currentGlobalSigma currentGlobalPi)
    horbit) as (_horbit & hglobalSigma & hglobalPi).
  constructor.
  - exact hglobalSigma.
  - exact hglobalPi.
  - exact (raw_dynamicTruthNativeSubstitutionDomain_target_atomically_adequate
      M hPA currentLevel currentLevelNumeral
      (formulaCode dynamicTruthLocalSigmaInputDomainTemplate)
      sigmaDomain hnumeral hsigmaDomain).
  - exact (raw_dynamicTruthNativeSubstitutionDomain_target_atomically_adequate
      M hPA currentLevel currentLevelNumeral
      (formulaCode dynamicTruthLocalPiInputDomainTemplate)
      piDomain hnumeral hpiDomain).
  - exact
      (raw_dynamicTruthNativeSubstitutionApplication_target_atomically_adequate
        M hPA
        dynamicTruthNativeSubstitutionSourceFirstReplacement
        dynamicTruthNativeSubstitutionSourceSecondReplacement
        dynamicTruthNativeSubstitutionSourceThirdReplacement
        currentGlobalSigma sourceSigma hsourceSigma).
  - exact
      (raw_dynamicTruthNativeSubstitutionApplication_target_atomically_adequate
        M hPA
        dynamicTruthNativeSubstitutionTargetFirstReplacement
        dynamicTruthNativeSubstitutionTargetSecondReplacement
        dynamicTruthNativeSubstitutionTargetThirdReplacement
        currentGlobalSigma targetSigma htargetSigma).
  - exact
      (raw_dynamicTruthNativeSubstitutionApplication_target_atomically_adequate
        M hPA
        dynamicTruthNativeSubstitutionSourceFirstReplacement
        dynamicTruthNativeSubstitutionSourceSecondReplacement
        dynamicTruthNativeSubstitutionSourceThirdReplacement
        currentGlobalPi sourcePi hsourcePi).
  - exact
      (raw_dynamicTruthNativeSubstitutionApplication_target_atomically_adequate
        M hPA
        dynamicTruthNativeSubstitutionTargetFirstReplacement
        dynamicTruthNativeSubstitutionTargetSecondReplacement
        dynamicTruthNativeSubstitutionTargetThirdReplacement
        currentGlobalPi targetPi htargetPi).
Qed.

(** ------------------------------------------------------------------
    Concrete projection of the five substitution side conditions. *)

Definition rawDynamicTruthNativeSubstitutionFormulaConditionCode
    (M : RawPAModel) : M :=
  rawNumeralValue M
    (formulaCode
      (codedFormulaSingleSubstitutionTermAt
        (tVar 0) (tVar 1) (tVar 2))).

Definition rawDynamicTruthNativeSubstitutionAssignmentConditionCode
    (M : RawPAModel) : M :=
  rawNumeralValue M
    (formulaCode
      (codedFormulaSubstitutionAssignmentRelationTermAt
        (tVar 0) (tVar 1) (tVar 3) (tVar 4) (tVar 5) (tVar 6))).

Definition rawDynamicTruthNativeSubstitutionTargetAdmissibleConditionCode
    (M : RawPAModel) : M :=
  rawNumeralValue M
    (formulaCode
      (codedFormulaTargetAdmissibilityDataTermAt
        (tVar 2) (tVar 5) (tVar 6))).

Definition rawDynamicTruthNativeSubstitutionRankAgreementConditionCode
    (M : RawPAModel) : M :=
  rawNumeralValue M
    (formulaCode
      (codedFormulaRankAgreementTermAt (tVar 1) (tVar 2))).

Definition RawDynamicTruthNativeSubstitutionSideConditionRootsOn
    (M : RawPAModel) (baseContext sigmaDomain piDomain : M) : Prop :=
  exists formulaSubstitutionRoot assignmentSubstitutionRoot
      sourceAdmissibleRoot targetAdmissibleRoot rankAgreementRoot : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeSubstitutionCommonContextOn M baseContext
        sigmaDomain piDomain)
      (rawDynamicTruthNativeSubstitutionFormulaConditionCode M)
      formulaSubstitutionRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeSubstitutionCommonContextOn M baseContext
        sigmaDomain piDomain)
      (rawDynamicTruthNativeSubstitutionAssignmentConditionCode M)
      assignmentSubstitutionRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeSubstitutionCommonContextOn M baseContext
        sigmaDomain piDomain)
      (rawDynamicTruthNativeSubstitutionSourceAdmissibleCode M
        sigmaDomain piDomain)
      sourceAdmissibleRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeSubstitutionCommonContextOn M baseContext
        sigmaDomain piDomain)
      (rawDynamicTruthNativeSubstitutionTargetAdmissibleConditionCode M)
      targetAdmissibleRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeSubstitutionCommonContextOn M baseContext
        sigmaDomain piDomain)
      (rawDynamicTruthNativeSubstitutionRankAgreementConditionCode M)
      rankAgreementRoot.

Arguments RawDynamicTruthNativeSubstitutionSideConditionRootsOn
  M baseContext sigmaDomain piDomain : clear implicits.

Theorem raw_dynamicTruthNativeSubstitutionSideConditionRootsOn : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain,
  RawContextListRealizable M baseContext ->
  RawDynamicTruthNativeSubstitutionSideConditionRootsOn M baseContext
    sigmaDomain piDomain.
Proof.
  intros M hPA baseContext sigmaDomain piDomain hbase.
  set (context := rawDynamicTruthNativeSubstitutionCommonContextOn M
    baseContext sigmaDomain piDomain).
  set (substitutionCode :=
    rawDynamicTruthNativeSubstitutionFormulaConditionCode M).
  set (assignmentCode :=
    rawDynamicTruthNativeSubstitutionAssignmentConditionCode M).
  set (sourceCode := rawDynamicTruthNativeSubstitutionSourceAdmissibleCode M
    sigmaDomain piDomain).
  set (targetCode :=
    rawDynamicTruthNativeSubstitutionTargetAdmissibleConditionCode M).
  set (rankCode :=
    rawDynamicTruthNativeSubstitutionRankAgreementConditionCode M).
  pose proof (raw_codedPALocalProofOf_assumption M hPA baseContext
    (rawDynamicTruthNativeSubstitutionAntecedentCode M
      sigmaDomain piDomain) hbase) as hall.
  change (RawCodedPALocalProofOf M context
    (rawFormulaAndCode M substitutionCode
      (rawFormulaAndCode M assignmentCode
        (rawFormulaAndCode M sourceCode
          (rawFormulaAndCode M targetCode rankCode))))
    (rawProofAssumptionRoot M context
      (rawDynamicTruthNativeSubstitutionAntecedentCode M
        sigmaDomain piDomain))) in hall.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA context substitutionCode
    (rawFormulaAndCode M assignmentCode
      (rawFormulaAndCode M sourceCode
        (rawFormulaAndCode M targetCode rankCode))) _ hall) as hsubstitution.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context substitutionCode
    (rawFormulaAndCode M assignmentCode
      (rawFormulaAndCode M sourceCode
        (rawFormulaAndCode M targetCode rankCode))) _ hall) as hrest1.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA context assignmentCode
    (rawFormulaAndCode M sourceCode
      (rawFormulaAndCode M targetCode rankCode)) _ hrest1) as hassignment.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context assignmentCode
    (rawFormulaAndCode M sourceCode
      (rawFormulaAndCode M targetCode rankCode)) _ hrest1) as hrest2.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA context sourceCode
    (rawFormulaAndCode M targetCode rankCode) _ hrest2) as hsource.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context sourceCode
    (rawFormulaAndCode M targetCode rankCode) _ hrest2) as hrest3.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA context targetCode
    rankCode _ hrest3) as htarget.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context targetCode
    rankCode _ hrest3) as hrank.
  lazymatch type of hsubstitution with
  | RawCodedPALocalProofOf _ _ _ ?substitutionRoot =>
    lazymatch type of hassignment with
    | RawCodedPALocalProofOf _ _ _ ?assignmentRoot =>
      lazymatch type of hsource with
      | RawCodedPALocalProofOf _ _ _ ?sourceRoot =>
        lazymatch type of htarget with
        | RawCodedPALocalProofOf _ _ _ ?targetRoot =>
          lazymatch type of hrank with
          | RawCodedPALocalProofOf _ _ _ ?rankRoot =>
            exists substitutionRoot, assignmentRoot, sourceRoot,
              targetRoot, rankRoot;
            split; [exact hsubstitution |];
            split; [exact hassignment |];
            split; [exact hsource |];
            split; [exact htarget | exact hrank]
          end
        end
      end
    end
  end.
Qed.

(** ------------------------------------------------------------------
    Four exact directional leaves and their implication shells. *)

Definition RawDynamicTruthNativeSubstitutionSigmaDirectionalLeavesOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain sourceSigma targetSigma : M) : Prop :=
  exists sourceToTargetLeaf targetToSourceLeaf : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeSubstitutionDirectionalContextOn M baseContext
        sigmaDomain piDomain sourceSigma)
      targetSigma sourceToTargetLeaf /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeSubstitutionDirectionalContextOn M baseContext
        sigmaDomain piDomain targetSigma)
      sourceSigma targetToSourceLeaf.

Definition RawDynamicTruthNativeSubstitutionPiDirectionalLeavesOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain sourcePi targetPi : M) : Prop :=
  exists sourceToTargetLeaf targetToSourceLeaf : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeSubstitutionDirectionalContextOn M baseContext
        sigmaDomain piDomain sourcePi)
      targetPi sourceToTargetLeaf /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeSubstitutionDirectionalContextOn M baseContext
        sigmaDomain piDomain targetPi)
      sourcePi targetToSourceLeaf.

Definition RawDynamicTruthNativeSubstitutionSigmaLocalRootsOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain sourceSigma targetSigma : M) : Prop :=
  exists sourceToTargetRoot targetToSourceRoot : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeSubstitutionCommonContextOn M baseContext
        sigmaDomain piDomain)
      (rawFormulaImpCode M sourceSigma targetSigma)
      sourceToTargetRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeSubstitutionCommonContextOn M baseContext
        sigmaDomain piDomain)
      (rawFormulaImpCode M targetSigma sourceSigma)
      targetToSourceRoot.

Definition RawDynamicTruthNativeSubstitutionPiLocalRootsOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain sourcePi targetPi : M) : Prop :=
  exists sourceToTargetRoot targetToSourceRoot : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeSubstitutionCommonContextOn M baseContext
        sigmaDomain piDomain)
      (rawFormulaImpCode M sourcePi targetPi)
      sourceToTargetRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeSubstitutionCommonContextOn M baseContext
        sigmaDomain piDomain)
      (rawFormulaImpCode M targetPi sourcePi)
      targetToSourceRoot.

Arguments RawDynamicTruthNativeSubstitutionSigmaDirectionalLeavesOn
  M baseContext sigmaDomain piDomain sourceSigma targetSigma
  : clear implicits.
Arguments RawDynamicTruthNativeSubstitutionPiDirectionalLeavesOn
  M baseContext sigmaDomain piDomain sourcePi targetPi : clear implicits.
Arguments RawDynamicTruthNativeSubstitutionSigmaLocalRootsOn
  M baseContext sigmaDomain piDomain sourceSigma targetSigma
  : clear implicits.
Arguments RawDynamicTruthNativeSubstitutionPiLocalRootsOn
  M baseContext sigmaDomain piDomain sourcePi targetPi : clear implicits.

Theorem
    raw_dynamicTruthNativeSubstitutionSigmaLocalRootsOn_of_directional_leaves :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain sourceSigma targetSigma,
  RawDynamicTruthNativeSubstitutionSigmaDirectionalLeavesOn M baseContext
    sigmaDomain piDomain sourceSigma targetSigma ->
  RawDynamicTruthNativeSubstitutionSigmaLocalRootsOn M baseContext
    sigmaDomain piDomain sourceSigma targetSigma.
Proof.
  intros M hPA baseContext sigmaDomain piDomain sourceSigma targetSigma
    (forwardLeaf & backwardLeaf & hforward & hbackward).
  exists
    (rawProofImpIRoot M
      (rawDynamicTruthNativeSubstitutionCommonContextOn M baseContext
        sigmaDomain piDomain)
      sourceSigma targetSigma forwardLeaf),
    (rawProofImpIRoot M
      (rawDynamicTruthNativeSubstitutionCommonContextOn M baseContext
        sigmaDomain piDomain)
      targetSigma sourceSigma backwardLeaf).
  split.
  - exact (raw_codedPALocalProofOf_impI M hPA
      (rawDynamicTruthNativeSubstitutionCommonContextOn M baseContext
        sigmaDomain piDomain)
      sourceSigma targetSigma forwardLeaf hforward).
  - exact (raw_codedPALocalProofOf_impI M hPA
      (rawDynamicTruthNativeSubstitutionCommonContextOn M baseContext
        sigmaDomain piDomain)
      targetSigma sourceSigma backwardLeaf hbackward).
Qed.

Theorem
    raw_dynamicTruthNativeSubstitutionPiLocalRootsOn_of_directional_leaves :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain sourcePi targetPi,
  RawDynamicTruthNativeSubstitutionPiDirectionalLeavesOn M baseContext
    sigmaDomain piDomain sourcePi targetPi ->
  RawDynamicTruthNativeSubstitutionPiLocalRootsOn M baseContext
    sigmaDomain piDomain sourcePi targetPi.
Proof.
  intros M hPA baseContext sigmaDomain piDomain sourcePi targetPi
    (forwardLeaf & backwardLeaf & hforward & hbackward).
  exists
    (rawProofImpIRoot M
      (rawDynamicTruthNativeSubstitutionCommonContextOn M baseContext
        sigmaDomain piDomain)
      sourcePi targetPi forwardLeaf),
    (rawProofImpIRoot M
      (rawDynamicTruthNativeSubstitutionCommonContextOn M baseContext
        sigmaDomain piDomain)
      targetPi sourcePi backwardLeaf).
  split.
  - exact (raw_codedPALocalProofOf_impI M hPA
      (rawDynamicTruthNativeSubstitutionCommonContextOn M baseContext
        sigmaDomain piDomain)
      sourcePi targetPi forwardLeaf hforward).
  - exact (raw_codedPALocalProofOf_impI M hPA
      (rawDynamicTruthNativeSubstitutionCommonContextOn M baseContext
        sigmaDomain piDomain)
      targetPi sourcePi backwardLeaf hbackward).
Qed.

(** The three conjunction-introduction nodes and the outer implication are
    generalized to the same visible tail.  This closes every propositional
    shell around the four directional roots; only universal closure remains
    deliberately tied to ordinary-proof packaging in the original module. *)
Definition rawDynamicTruthNativeSubstitutionTransportRootOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi
      sigmaForward sigmaBackward piForward piBackward : M) : M :=
  let context := rawDynamicTruthNativeSubstitutionCommonContextOn M
    baseContext sigmaDomain piDomain in
  rawProofAndIRoot M context
    (rawDynamicTruthNativeSubstitutionFormulaIffCode M
      sourceSigma targetSigma)
    (rawDynamicTruthNativeSubstitutionFormulaIffCode M sourcePi targetPi)
    (rawDynamicTruthNativeSubstitutionIffRoot M context
      sourceSigma targetSigma sigmaForward sigmaBackward)
    (rawDynamicTruthNativeSubstitutionIffRoot M context
      sourcePi targetPi piForward piBackward).

Definition rawDynamicTruthNativeSubstitutionBodyRootOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi
      sigmaForward sigmaBackward piForward piBackward : M) : M :=
  rawProofImpIRoot M baseContext
    (rawDynamicTruthNativeSubstitutionAntecedentCode M
      sigmaDomain piDomain)
    (rawDynamicTruthNativeSubstitutionTransportCode M
      sourceSigma targetSigma sourcePi targetPi)
    (rawDynamicTruthNativeSubstitutionTransportRootOn M
      baseContext sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi
      sigmaForward sigmaBackward piForward piBackward).

Arguments rawDynamicTruthNativeSubstitutionTransportRootOn
  M baseContext sigmaDomain piDomain
  sourceSigma targetSigma sourcePi targetPi
  sigmaForward sigmaBackward piForward piBackward : clear implicits.
Arguments rawDynamicTruthNativeSubstitutionBodyRootOn
  M baseContext sigmaDomain piDomain
  sourceSigma targetSigma sourcePi targetPi
  sigmaForward sigmaBackward piForward piBackward : clear implicits.

Lemma rawDynamicTruthNativeSubstitutionTransportRootOn_empty : forall
    (M : RawPAModel)
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      sigmaForward sigmaBackward piForward piBackward,
  rawDynamicTruthNativeSubstitutionTransportRootOn M (raw_zero M)
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      sigmaForward sigmaBackward piForward piBackward =
  rawDynamicTruthNativeSubstitutionTransportRoot M
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      sigmaForward sigmaBackward piForward piBackward.
Proof.
  reflexivity.
Qed.

Lemma rawDynamicTruthNativeSubstitutionBodyRootOn_empty : forall
    (M : RawPAModel)
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      sigmaForward sigmaBackward piForward piBackward,
  rawDynamicTruthNativeSubstitutionBodyRootOn M (raw_zero M)
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      sigmaForward sigmaBackward piForward piBackward =
  rawDynamicTruthNativeSubstitutionBodyRoot M
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      sigmaForward sigmaBackward piForward piBackward.
Proof.
  reflexivity.
Qed.

Definition RawDynamicTruthNativeSubstitutionBodyLocalRootOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi : M) : Prop :=
  exists child : M,
    RawCodedPALocalProofOf M baseContext
      (rawDynamicTruthNativeSubstitutionBodyCode M
        sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi)
      child.

Arguments RawDynamicTruthNativeSubstitutionBodyLocalRootOn
  M baseContext sigmaDomain piDomain
  sourceSigma targetSigma sourcePi targetPi : clear implicits.

Theorem
    raw_dynamicTruthNativeSubstitutionBodyLocalRootOn_of_polarity_roots :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi,
  RawDynamicTruthNativeSubstitutionSigmaLocalRootsOn M baseContext
    sigmaDomain piDomain sourceSigma targetSigma ->
  RawDynamicTruthNativeSubstitutionPiLocalRootsOn M baseContext
    sigmaDomain piDomain sourcePi targetPi ->
  RawDynamicTruthNativeSubstitutionBodyLocalRootOn M baseContext
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi.
Proof.
  intros M hPA baseContext sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi
    (sigmaForward & sigmaBackward & hsigmaForward & hsigmaBackward)
    (piForward & piBackward & hpiForward & hpiBackward).
  set (context := rawDynamicTruthNativeSubstitutionCommonContextOn M
    baseContext sigmaDomain piDomain).
  pose proof (raw_codedPALocalProofOf_andI M hPA context
    (rawFormulaImpCode M sourceSigma targetSigma)
    (rawFormulaImpCode M targetSigma sourceSigma)
    sigmaForward sigmaBackward hsigmaForward hsigmaBackward) as hsigmaIff.
  pose proof (raw_codedPALocalProofOf_andI M hPA context
    (rawFormulaImpCode M sourcePi targetPi)
    (rawFormulaImpCode M targetPi sourcePi)
    piForward piBackward hpiForward hpiBackward) as hpiIff.
  pose proof (raw_codedPALocalProofOf_andI M hPA context
    (rawDynamicTruthNativeSubstitutionFormulaIffCode M
      sourceSigma targetSigma)
    (rawDynamicTruthNativeSubstitutionFormulaIffCode M sourcePi targetPi)
    (rawDynamicTruthNativeSubstitutionIffRoot M context
      sourceSigma targetSigma sigmaForward sigmaBackward)
    (rawDynamicTruthNativeSubstitutionIffRoot M context
      sourcePi targetPi piForward piBackward)
    hsigmaIff hpiIff) as htransport.
  pose proof (raw_codedPALocalProofOf_impI M hPA baseContext
    (rawDynamicTruthNativeSubstitutionAntecedentCode M
      sigmaDomain piDomain)
    (rawDynamicTruthNativeSubstitutionTransportCode M
      sourceSigma targetSigma sourcePi targetPi)
    (rawDynamicTruthNativeSubstitutionTransportRootOn M
      baseContext sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi
      sigmaForward sigmaBackward piForward piBackward)
    htransport) as hbody.
  exists (rawDynamicTruthNativeSubstitutionBodyRootOn M baseContext
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    sigmaForward sigmaBackward piForward piBackward).
  exact hbody.
Qed.

(** ------------------------------------------------------------------
    Trace-linked residual interfaces and adapters. *)

(** Direct form of the remaining leaf interface.  The trace argument keeps
    all four target codes tied to the same represented application data. *)
Definition RawDynamicTruthNativeSubstitutionDirectionalLeafRootCompilerOn
    (M : RawPAModel) (baseContext : M) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
    RawDynamicTruthNativeSubstitutionProofTraceAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi ->
    RawDynamicTruthNativeSubstitutionSigmaDirectionalLeavesOn M baseContext
      sigmaDomain piDomain sourceSigma targetSigma /\
    RawDynamicTruthNativeSubstitutionPiDirectionalLeavesOn M baseContext
      sigmaDomain piDomain sourcePi targetPi.

Arguments RawDynamicTruthNativeSubstitutionDirectionalLeafRootCompilerOn
  M baseContext : clear implicits.

(** Resource-explicit form.  This is the narrowest honest arithmetic seam:
    the compiler is handed both adequacy and all five local proofs which are
    constructible from the trace/context shell, and must produce only the
    four directional target leaves. *)
Definition
    RawDynamicTruthNativeSubstitutionTraceLinkedDirectionalLeafCompilerOn
    (M : RawPAModel) (baseContext : M) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
    RawDynamicTruthNativeSubstitutionProofTraceAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi ->
    RawDynamicTruthNativeSubstitutionProofTraceAdequacyAt M
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi ->
    RawDynamicTruthNativeSubstitutionSideConditionRootsOn M baseContext
      sigmaDomain piDomain ->
    RawDynamicTruthNativeSubstitutionSigmaDirectionalLeavesOn M baseContext
      sigmaDomain piDomain sourceSigma targetSigma /\
    RawDynamicTruthNativeSubstitutionPiDirectionalLeavesOn M baseContext
      sigmaDomain piDomain sourcePi targetPi.

Arguments
  RawDynamicTruthNativeSubstitutionTraceLinkedDirectionalLeafCompilerOn
  M baseContext : clear implicits.

Theorem
    raw_dynamicTruthNativeSubstitutionDirectionalLeafRootCompilerOn_of_trace_linked :
  forall (M : RawPAModel), RawPASatisfies M -> forall baseContext,
  RawContextListRealizable M baseContext ->
  RawDynamicTruthNativeSubstitutionTraceLinkedDirectionalLeafCompilerOn
    M baseContext ->
  RawDynamicTruthNativeSubstitutionDirectionalLeafRootCompilerOn
    M baseContext.
Proof.
  intros M hPA baseContext hbase hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi htrace.
  apply (hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi htrace).
  - exact (raw_dynamicTruthNativeSubstitutionProofTraceAt_adequacy
      M hPA tail predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      htrace).
  - exact (raw_dynamicTruthNativeSubstitutionSideConditionRootsOn
      M hPA baseContext sigmaDomain piDomain hbase).
Qed.

Theorem
    raw_dynamicTruthNativeSubstitutionLocalRootsOn_of_directional_leaf_compiler :
  forall (M : RawPAModel), RawPASatisfies M -> forall baseContext,
  RawDynamicTruthNativeSubstitutionDirectionalLeafRootCompilerOn
    M baseContext ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  RawDynamicTruthNativeSubstitutionProofTraceAt M tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi ->
  RawDynamicTruthNativeSubstitutionSigmaLocalRootsOn M baseContext
      sigmaDomain piDomain sourceSigma targetSigma /\
  RawDynamicTruthNativeSubstitutionPiLocalRootsOn M baseContext
      sigmaDomain piDomain sourcePi targetPi.
Proof.
  intros M hPA baseContext hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi htrace.
  destruct (hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi htrace) as
    [hsigmaLeaves hpiLeaves].
  split.
  - exact
      (raw_dynamicTruthNativeSubstitutionSigmaLocalRootsOn_of_directional_leaves
        M hPA baseContext sigmaDomain piDomain sourceSigma targetSigma
        hsigmaLeaves).
  - exact
      (raw_dynamicTruthNativeSubstitutionPiLocalRootsOn_of_directional_leaves
        M hPA baseContext sigmaDomain piDomain sourcePi targetPi
        hpiLeaves).
Qed.

Corollary
    raw_dynamicTruthNativeSubstitutionBodyLocalRootOn_of_directional_leaf_compiler :
  forall (M : RawPAModel), RawPASatisfies M -> forall baseContext,
  RawDynamicTruthNativeSubstitutionDirectionalLeafRootCompilerOn
    M baseContext ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  RawDynamicTruthNativeSubstitutionProofTraceAt M tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi ->
  RawDynamicTruthNativeSubstitutionBodyLocalRootOn M baseContext
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi.
Proof.
  intros M hPA baseContext hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi htrace.
  destruct
    (raw_dynamicTruthNativeSubstitutionLocalRootsOn_of_directional_leaf_compiler
      M hPA baseContext hcompiler tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi htrace) as
    [hsigma hpi].
  exact
    (raw_dynamicTruthNativeSubstitutionBodyLocalRootOn_of_polarity_roots
      M hPA baseContext sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi hsigma hpi).
Qed.

(** Literal-empty adapter to the original local-root compiler.  Its premise
    deliberately asks for leaves genuinely proved over the empty base tail. *)
Theorem
    raw_dynamicTruthNativeSubstitutionLocalRootCompiler_of_empty_directional_leaves :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeSubstitutionDirectionalLeafRootCompilerOn
    M (raw_zero M) ->
  RawDynamicTruthNativeSubstitutionLocalRootCompiler M.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi htrace.
  destruct
    (raw_dynamicTruthNativeSubstitutionLocalRootsOn_of_directional_leaf_compiler
      M hPA (raw_zero M) hcompiler tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi htrace) as
    [hsigma hpi].
  split; assumption.
Qed.

(** The resource-explicit empty adapter additionally discharges every
    trace/context resource which is derivable without arithmetic leaves. *)
Corollary
    raw_dynamicTruthNativeSubstitutionLocalRootCompiler_of_empty_trace_linked_leaves :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeSubstitutionTraceLinkedDirectionalLeafCompilerOn
    M (raw_zero M) ->
  RawDynamicTruthNativeSubstitutionLocalRootCompiler M.
Proof.
  intros M hPA hcompiler.
  apply
    (raw_dynamicTruthNativeSubstitutionLocalRootCompiler_of_empty_directional_leaves
      M hPA).
  exact
    (raw_dynamicTruthNativeSubstitutionDirectionalLeafRootCompilerOn_of_trace_linked
      M hPA (raw_zero M)
      (raw_contextList_empty_realizable M hPA) hcompiler).
Qed.

(** Witnessed-tail form used by ordinary PA-proof packaging.  The witness
    relation remains visible and supplies realizability of the exact tail;
    it is never converted to an empty context. *)
Definition
    RawDynamicTruthNativeSubstitutionWitnessedDirectionalLeafRootInterface
    (M : RawPAModel) : Prop :=
  forall witnessList baseContext,
    RawCodedPAAxiomWitnessContext M witnessList baseContext ->
    RawDynamicTruthNativeSubstitutionTraceLinkedDirectionalLeafCompilerOn
      M baseContext.

Arguments
  RawDynamicTruthNativeSubstitutionWitnessedDirectionalLeafRootInterface
  M : clear implicits.

Corollary
    raw_dynamicTruthNativeSubstitutionWitnessedLocalRoots_of_directional_leaves :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeSubstitutionWitnessedDirectionalLeafRootInterface M ->
  forall witnessList baseContext,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  RawDynamicTruthNativeSubstitutionProofTraceAt M tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi ->
  RawDynamicTruthNativeSubstitutionSigmaLocalRootsOn M baseContext
      sigmaDomain piDomain sourceSigma targetSigma /\
  RawDynamicTruthNativeSubstitutionPiLocalRootsOn M baseContext
      sigmaDomain piDomain sourcePi targetPi.
Proof.
  intros M hPA hinterface witnessList baseContext hwitness.
  apply
    (raw_dynamicTruthNativeSubstitutionLocalRootsOn_of_directional_leaf_compiler
      M hPA baseContext).
  exact
    (raw_dynamicTruthNativeSubstitutionDirectionalLeafRootCompilerOn_of_trace_linked
      M hPA baseContext
      (raw_codedPAAxiomWitnessContext_context_realizable
        M witnessList baseContext hwitness)
      (hinterface witnessList baseContext hwitness)).
Qed.

Corollary
    raw_dynamicTruthNativeSubstitutionWitnessedBodyLocalRoot_of_directional_leaves :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeSubstitutionWitnessedDirectionalLeafRootInterface M ->
  forall witnessList baseContext,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  RawDynamicTruthNativeSubstitutionProofTraceAt M tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi ->
  RawDynamicTruthNativeSubstitutionBodyLocalRootOn M baseContext
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi.
Proof.
  intros M hPA hinterface witnessList baseContext hwitness
    tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi htrace.
  destruct
    (raw_dynamicTruthNativeSubstitutionWitnessedLocalRoots_of_directional_leaves
      M hPA hinterface witnessList baseContext hwitness
      tail predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi htrace)
    as [hsigma hpi].
  exact
    (raw_dynamicTruthNativeSubstitutionBodyLocalRootOn_of_polarity_roots
      M hPA baseContext sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi hsigma hpi).
Qed.

End PABoundedRawCodedDynamicTruthNativeSubstitutionLeafRootCompilation.
