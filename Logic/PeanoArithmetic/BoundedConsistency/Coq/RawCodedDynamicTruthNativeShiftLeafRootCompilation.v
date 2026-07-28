(**
  Trace-linked leaf compilation for the native formula-shift field.

  [RawCodedDynamicTruthNativeShiftProofCompilation] exposes the correct
  propositional shell, but its final compiler still asks for four implication
  roots over the literal shift-data context.  This file factors those roots
  one step further.  A directional leaf keeps the source formula as the
  literal head assumption; the public implication is then obtained by the
  represented implication-introduction constructor.

  The factorization matters because the raw local calculus has no special
  rule that silently imports PA axioms.  Arithmetic transport must therefore
  be compiled over a visible witnessed PA tail (or, for the historical
  empty-tail endpoint, genuinely without arithmetic assumptions).  The
  definitions below never erase that tail.

  Everything around the four directional leaves is discharged here:

  - the orbit and four represented ternary applications imply atomic
    adequacy of all carrier-selected formula codes;
  - the five members of the nested shift-data conjunction are projected by
    concrete assumption and conjunction-elimination roots;
  - four directional target roots are discharged by concrete implication
    introduction into the exact Sigma and Pi root bundles.

  Thus [RawDynamicTruthNativeShiftDirectionalLeafRootCompilerOn] is the
  smallest remaining proof-producing interface.  It is indexed by the full
  trace and by the exact visible tail, and receives neither a completed field
  proof nor a semantic validity premise.
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
  RawCodedProofAndEConstructors
  RawCodedProofImpIConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofPropositionalRules
  RawCodedDynamicTruthPairedSuccessorAdequacy
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeShiftPositiveGraph
  RawCodedDynamicTruthNativeShiftProofCompilation.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthNativeShiftLeafRootCompilation.

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
Import PABoundedRawCodedProofAndEConstructors.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeShiftPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeShiftProofCompilation.

(** ------------------------------------------------------------------
    Exact contexts with a visible base tail. *)

Definition rawDynamicTruthNativeShiftCommonContextOn
    (M : RawPAModel) (baseContext sigmaDomain piDomain : M) : M :=
  rawListNode M
    (rawDynamicTruthNativeShiftAntecedentCode M sigmaDomain piDomain)
    baseContext.

Definition rawDynamicTruthNativeShiftDirectionalContextOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain assumption : M) : M :=
  rawListNode M assumption
    (rawDynamicTruthNativeShiftCommonContextOn M baseContext
      sigmaDomain piDomain).

Arguments rawDynamicTruthNativeShiftCommonContextOn
  M baseContext sigmaDomain piDomain : clear implicits.
Arguments rawDynamicTruthNativeShiftDirectionalContextOn
  M baseContext sigmaDomain piDomain assumption : clear implicits.

Lemma rawDynamicTruthNativeShiftCommonContextOn_empty : forall
    (M : RawPAModel) sigmaDomain piDomain,
  rawDynamicTruthNativeShiftCommonContextOn M (raw_zero M)
      sigmaDomain piDomain =
  rawDynamicTruthNativeShiftCommonContext M sigmaDomain piDomain.
Proof.
  reflexivity.
Qed.

Lemma raw_dynamicTruthNativeShiftCommonContextOn_realizable : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain,
  RawContextListRealizable M baseContext ->
  RawContextListRealizable M
    (rawDynamicTruthNativeShiftCommonContextOn M baseContext
      sigmaDomain piDomain).
Proof.
  intros M hPA baseContext sigmaDomain piDomain hbase.
  exact (raw_contextList_cons_realizable M hPA baseContext
    (rawDynamicTruthNativeShiftAntecedentCode M sigmaDomain piDomain)
    hbase).
Qed.

Lemma raw_dynamicTruthNativeShiftDirectionalContextOn_realizable : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain assumption,
  RawContextListRealizable M baseContext ->
  RawContextListRealizable M
    (rawDynamicTruthNativeShiftDirectionalContextOn M baseContext
      sigmaDomain piDomain assumption).
Proof.
  intros M hPA baseContext sigmaDomain piDomain assumption hbase.
  apply (raw_contextList_cons_realizable M hPA).
  exact (raw_dynamicTruthNativeShiftCommonContextOn_realizable M hPA
    baseContext sigmaDomain piDomain hbase).
Qed.

(** ------------------------------------------------------------------
    Adequacy information already contained in the trace. *)

(** A three-step application has an adequate output because its last
    represented substitution has a fixed standard replacement.  In
    particular, no adequacy assumption about the input is needed here. *)
Lemma raw_dynamicTruthNativeShiftApplication_target_atomically_adequate :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      firstReplacement secondReplacement thirdReplacement input output,
  RawDynamicTruthNativeShiftApplication M
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

(** The two input-domain substitutions use the represented numeral selected
    by the trace. *)
Lemma raw_dynamicTruthNativeShiftDomain_target_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall
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

Definition RawDynamicTruthNativeShiftProofTraceAdequacyAt
    (M : RawPAModel)
    (currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi : M) : Prop :=
  RawCodedFormulaAtomicallyAdequate M currentGlobalSigma /\
  RawCodedFormulaAtomicallyAdequate M currentGlobalPi /\
  RawCodedFormulaAtomicallyAdequate M sigmaDomain /\
  RawCodedFormulaAtomicallyAdequate M piDomain /\
  RawCodedFormulaAtomicallyAdequate M sourceSigma /\
  RawCodedFormulaAtomicallyAdequate M targetSigma /\
  RawCodedFormulaAtomicallyAdequate M sourcePi /\
  RawCodedFormulaAtomicallyAdequate M targetPi.

Arguments RawDynamicTruthNativeShiftProofTraceAdequacyAt
  M currentGlobalSigma currentGlobalPi sigmaDomain piDomain
  sourceSigma targetSigma sourcePi targetPi : clear implicits.

Theorem raw_dynamicTruthNativeShiftProofTraceAt_adequacy : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  RawDynamicTruthNativeShiftProofTraceAt M tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi ->
  RawDynamicTruthNativeShiftProofTraceAdequacyAt M
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
  repeat split.
  - exact hglobalSigma.
  - exact hglobalPi.
  - exact (raw_dynamicTruthNativeShiftDomain_target_atomically_adequate
      M hPA currentLevel currentLevelNumeral
      (formulaCode dynamicTruthLocalSigmaInputDomainTemplate)
      sigmaDomain hnumeral hsigmaDomain).
  - exact (raw_dynamicTruthNativeShiftDomain_target_atomically_adequate
      M hPA currentLevel currentLevelNumeral
      (formulaCode dynamicTruthLocalPiInputDomainTemplate)
      piDomain hnumeral hpiDomain).
  - exact
      (raw_dynamicTruthNativeShiftApplication_target_atomically_adequate
        M hPA
        dynamicTruthNativeShiftSourceFirstReplacement
        dynamicTruthNativeShiftSourceSecondReplacement
        dynamicTruthNativeShiftSourceThirdReplacement
        currentGlobalSigma sourceSigma hsourceSigma).
  - exact
      (raw_dynamicTruthNativeShiftApplication_target_atomically_adequate
        M hPA
        dynamicTruthNativeShiftTargetFirstReplacement
        dynamicTruthNativeShiftTargetSecondReplacement
        dynamicTruthNativeShiftTargetThirdReplacement
        currentGlobalSigma targetSigma htargetSigma).
  - exact
      (raw_dynamicTruthNativeShiftApplication_target_atomically_adequate
        M hPA
        dynamicTruthNativeShiftSourceFirstReplacement
        dynamicTruthNativeShiftSourceSecondReplacement
        dynamicTruthNativeShiftSourceThirdReplacement
        currentGlobalPi sourcePi hsourcePi).
  - exact
      (raw_dynamicTruthNativeShiftApplication_target_atomically_adequate
        M hPA
        dynamicTruthNativeShiftTargetFirstReplacement
        dynamicTruthNativeShiftTargetSecondReplacement
        dynamicTruthNativeShiftTargetThirdReplacement
        currentGlobalPi targetPi htargetPi).
Qed.

(** ------------------------------------------------------------------
    Concrete projection of the five side conditions. *)

Definition rawDynamicTruthNativeShiftFormulaShiftConditionCode
    (M : RawPAModel) : M :=
  rawNumeralValue M
    (formulaCode
      (codedFormulaShiftTermAt (tVar 0) (tVar 1) (tVar 2) (tVar 3))).

Definition rawDynamicTruthNativeShiftAssignmentShiftConditionCode
    (M : RawPAModel) : M :=
  rawNumeralValue M
    (formulaCode
      (codedFormulaShiftAssignmentRelationTermAt
        (tVar 0) (tVar 1) (tVar 2)
        (tVar 4) (tVar 5) (tVar 6) (tVar 7))).

Definition rawDynamicTruthNativeShiftTargetAdmissibleConditionCode
    (M : RawPAModel) : M :=
  rawNumeralValue M
    (formulaCode
      (codedFormulaTargetAdmissibilityDataTermAt
        (tVar 3) (tVar 6) (tVar 7))).

Definition rawDynamicTruthNativeShiftRankAgreementConditionCode
    (M : RawPAModel) : M :=
  rawNumeralValue M
    (formulaCode
      (codedFormulaRankAgreementTermAt (tVar 2) (tVar 3))).

(** The following names expose the concrete projection tree without forcing
    downstream proofs to repeat its long nested constructor terms. *)
Definition rawDynamicTruthNativeShiftSideConditionAssumptionRoot
    (M : RawPAModel) (baseContext sigmaDomain piDomain : M) : M :=
  rawProofAssumptionRoot M
    (rawDynamicTruthNativeShiftCommonContextOn M baseContext
      sigmaDomain piDomain)
    (rawDynamicTruthNativeShiftAntecedentCode M sigmaDomain piDomain).

Definition rawDynamicTruthNativeShiftSideConditionTail1Root
    (M : RawPAModel) (baseContext sigmaDomain piDomain : M) : M :=
  rawProofAndERoot M RawAndRight
    (rawDynamicTruthNativeShiftCommonContextOn M baseContext
      sigmaDomain piDomain)
    (rawDynamicTruthNativeShiftFormulaShiftConditionCode M)
    (rawFormulaAndCode M
      (rawDynamicTruthNativeShiftAssignmentShiftConditionCode M)
      (rawFormulaAndCode M
        (rawDynamicTruthNativeShiftSourceAdmissibleCode M
          sigmaDomain piDomain)
        (rawFormulaAndCode M
          (rawDynamicTruthNativeShiftTargetAdmissibleConditionCode M)
          (rawDynamicTruthNativeShiftRankAgreementConditionCode M))))
    (rawDynamicTruthNativeShiftSideConditionAssumptionRoot M baseContext
      sigmaDomain piDomain).

Definition rawDynamicTruthNativeShiftSideConditionTail2Root
    (M : RawPAModel) (baseContext sigmaDomain piDomain : M) : M :=
  rawProofAndERoot M RawAndRight
    (rawDynamicTruthNativeShiftCommonContextOn M baseContext
      sigmaDomain piDomain)
    (rawDynamicTruthNativeShiftAssignmentShiftConditionCode M)
    (rawFormulaAndCode M
      (rawDynamicTruthNativeShiftSourceAdmissibleCode M sigmaDomain piDomain)
      (rawFormulaAndCode M
        (rawDynamicTruthNativeShiftTargetAdmissibleConditionCode M)
        (rawDynamicTruthNativeShiftRankAgreementConditionCode M)))
    (rawDynamicTruthNativeShiftSideConditionTail1Root M baseContext
      sigmaDomain piDomain).

Definition rawDynamicTruthNativeShiftSideConditionTail3Root
    (M : RawPAModel) (baseContext sigmaDomain piDomain : M) : M :=
  rawProofAndERoot M RawAndRight
    (rawDynamicTruthNativeShiftCommonContextOn M baseContext
      sigmaDomain piDomain)
    (rawDynamicTruthNativeShiftSourceAdmissibleCode M sigmaDomain piDomain)
    (rawFormulaAndCode M
      (rawDynamicTruthNativeShiftTargetAdmissibleConditionCode M)
      (rawDynamicTruthNativeShiftRankAgreementConditionCode M))
    (rawDynamicTruthNativeShiftSideConditionTail2Root M baseContext
      sigmaDomain piDomain).

Definition rawDynamicTruthNativeShiftFormulaShiftConditionRoot
    (M : RawPAModel) (baseContext sigmaDomain piDomain : M) : M :=
  rawProofAndERoot M RawAndLeft
    (rawDynamicTruthNativeShiftCommonContextOn M baseContext
      sigmaDomain piDomain)
    (rawDynamicTruthNativeShiftFormulaShiftConditionCode M)
    (rawFormulaAndCode M
      (rawDynamicTruthNativeShiftAssignmentShiftConditionCode M)
      (rawFormulaAndCode M
        (rawDynamicTruthNativeShiftSourceAdmissibleCode M
          sigmaDomain piDomain)
        (rawFormulaAndCode M
          (rawDynamicTruthNativeShiftTargetAdmissibleConditionCode M)
          (rawDynamicTruthNativeShiftRankAgreementConditionCode M))))
    (rawDynamicTruthNativeShiftSideConditionAssumptionRoot M baseContext
      sigmaDomain piDomain).

Definition rawDynamicTruthNativeShiftAssignmentShiftConditionRoot
    (M : RawPAModel) (baseContext sigmaDomain piDomain : M) : M :=
  rawProofAndERoot M RawAndLeft
    (rawDynamicTruthNativeShiftCommonContextOn M baseContext
      sigmaDomain piDomain)
    (rawDynamicTruthNativeShiftAssignmentShiftConditionCode M)
    (rawFormulaAndCode M
      (rawDynamicTruthNativeShiftSourceAdmissibleCode M sigmaDomain piDomain)
      (rawFormulaAndCode M
        (rawDynamicTruthNativeShiftTargetAdmissibleConditionCode M)
        (rawDynamicTruthNativeShiftRankAgreementConditionCode M)))
    (rawDynamicTruthNativeShiftSideConditionTail1Root M baseContext
      sigmaDomain piDomain).

Definition rawDynamicTruthNativeShiftSourceAdmissibleConditionRoot
    (M : RawPAModel) (baseContext sigmaDomain piDomain : M) : M :=
  rawProofAndERoot M RawAndLeft
    (rawDynamicTruthNativeShiftCommonContextOn M baseContext
      sigmaDomain piDomain)
    (rawDynamicTruthNativeShiftSourceAdmissibleCode M sigmaDomain piDomain)
    (rawFormulaAndCode M
      (rawDynamicTruthNativeShiftTargetAdmissibleConditionCode M)
      (rawDynamicTruthNativeShiftRankAgreementConditionCode M))
    (rawDynamicTruthNativeShiftSideConditionTail2Root M baseContext
      sigmaDomain piDomain).

Definition rawDynamicTruthNativeShiftTargetAdmissibleConditionRoot
    (M : RawPAModel) (baseContext sigmaDomain piDomain : M) : M :=
  rawProofAndERoot M RawAndLeft
    (rawDynamicTruthNativeShiftCommonContextOn M baseContext
      sigmaDomain piDomain)
    (rawDynamicTruthNativeShiftTargetAdmissibleConditionCode M)
    (rawDynamicTruthNativeShiftRankAgreementConditionCode M)
    (rawDynamicTruthNativeShiftSideConditionTail3Root M baseContext
      sigmaDomain piDomain).

Definition rawDynamicTruthNativeShiftRankAgreementConditionRoot
    (M : RawPAModel) (baseContext sigmaDomain piDomain : M) : M :=
  rawProofAndERoot M RawAndRight
    (rawDynamicTruthNativeShiftCommonContextOn M baseContext
      sigmaDomain piDomain)
    (rawDynamicTruthNativeShiftTargetAdmissibleConditionCode M)
    (rawDynamicTruthNativeShiftRankAgreementConditionCode M)
    (rawDynamicTruthNativeShiftSideConditionTail3Root M baseContext
      sigmaDomain piDomain).

Definition RawDynamicTruthNativeShiftSideConditionRootsOn
    (M : RawPAModel) (baseContext sigmaDomain piDomain : M) : Prop :=
  exists formulaShiftRoot assignmentShiftRoot sourceAdmissibleRoot
      targetAdmissibleRoot rankAgreementRoot : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeShiftCommonContextOn M baseContext
        sigmaDomain piDomain)
      (rawDynamicTruthNativeShiftFormulaShiftConditionCode M)
      formulaShiftRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeShiftCommonContextOn M baseContext
        sigmaDomain piDomain)
      (rawDynamicTruthNativeShiftAssignmentShiftConditionCode M)
      assignmentShiftRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeShiftCommonContextOn M baseContext
        sigmaDomain piDomain)
      (rawDynamicTruthNativeShiftSourceAdmissibleCode M
        sigmaDomain piDomain)
      sourceAdmissibleRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeShiftCommonContextOn M baseContext
        sigmaDomain piDomain)
      (rawDynamicTruthNativeShiftTargetAdmissibleConditionCode M)
      targetAdmissibleRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeShiftCommonContextOn M baseContext
        sigmaDomain piDomain)
      (rawDynamicTruthNativeShiftRankAgreementConditionCode M)
      rankAgreementRoot.

Arguments RawDynamicTruthNativeShiftSideConditionRootsOn
  M baseContext sigmaDomain piDomain : clear implicits.

Theorem raw_dynamicTruthNativeShiftSideConditionRootsOn : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain,
  RawContextListRealizable M baseContext ->
  RawDynamicTruthNativeShiftSideConditionRootsOn M baseContext
    sigmaDomain piDomain.
Proof.
  intros M hPA baseContext sigmaDomain piDomain hbase.
  set (context := rawDynamicTruthNativeShiftCommonContextOn M baseContext
    sigmaDomain piDomain).
  set (shiftCode := rawDynamicTruthNativeShiftFormulaShiftConditionCode M).
  set (assignmentCode :=
    rawDynamicTruthNativeShiftAssignmentShiftConditionCode M).
  set (sourceCode := rawDynamicTruthNativeShiftSourceAdmissibleCode M
    sigmaDomain piDomain).
  set (targetCode :=
    rawDynamicTruthNativeShiftTargetAdmissibleConditionCode M).
  set (rankCode := rawDynamicTruthNativeShiftRankAgreementConditionCode M).
  pose proof (raw_codedPALocalProofOf_assumption M hPA baseContext
    (rawDynamicTruthNativeShiftAntecedentCode M sigmaDomain piDomain)
    hbase) as hall.
  change (RawCodedPALocalProofOf M context
    (rawFormulaAndCode M shiftCode
      (rawFormulaAndCode M assignmentCode
        (rawFormulaAndCode M sourceCode
          (rawFormulaAndCode M targetCode rankCode))))
    (rawProofAssumptionRoot M context
      (rawDynamicTruthNativeShiftAntecedentCode M sigmaDomain piDomain)))
    in hall.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA context shiftCode
    (rawFormulaAndCode M assignmentCode
      (rawFormulaAndCode M sourceCode
        (rawFormulaAndCode M targetCode rankCode))) _ hall) as hshift.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context shiftCode
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
  exists
    (rawDynamicTruthNativeShiftFormulaShiftConditionRoot M baseContext
      sigmaDomain piDomain),
    (rawDynamicTruthNativeShiftAssignmentShiftConditionRoot M baseContext
      sigmaDomain piDomain),
    (rawDynamicTruthNativeShiftSourceAdmissibleConditionRoot M baseContext
      sigmaDomain piDomain),
    (rawDynamicTruthNativeShiftTargetAdmissibleConditionRoot M baseContext
      sigmaDomain piDomain),
    (rawDynamicTruthNativeShiftRankAgreementConditionRoot M baseContext
      sigmaDomain piDomain).
  unfold rawDynamicTruthNativeShiftFormulaShiftConditionRoot,
    rawDynamicTruthNativeShiftAssignmentShiftConditionRoot,
    rawDynamicTruthNativeShiftSourceAdmissibleConditionRoot,
    rawDynamicTruthNativeShiftTargetAdmissibleConditionRoot,
    rawDynamicTruthNativeShiftRankAgreementConditionRoot,
    rawDynamicTruthNativeShiftSideConditionTail1Root,
    rawDynamicTruthNativeShiftSideConditionTail2Root,
    rawDynamicTruthNativeShiftSideConditionTail3Root,
    rawDynamicTruthNativeShiftSideConditionAssumptionRoot.
  fold context shiftCode assignmentCode sourceCode targetCode rankCode.
  split; [exact hshift |].
  split; [exact hassignment |].
  split; [exact hsource |].
  split; [exact htarget | exact hrank].
Qed.

(** ------------------------------------------------------------------
    The four exact directional leaves and their implication shells. *)

Definition RawDynamicTruthNativeShiftSigmaDirectionalLeavesOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain sourceSigma targetSigma : M) : Prop :=
  exists sourceToTargetLeaf targetToSourceLeaf : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeShiftDirectionalContextOn M baseContext
        sigmaDomain piDomain sourceSigma)
      targetSigma sourceToTargetLeaf /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeShiftDirectionalContextOn M baseContext
        sigmaDomain piDomain targetSigma)
      sourceSigma targetToSourceLeaf.

Definition RawDynamicTruthNativeShiftPiDirectionalLeavesOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain sourcePi targetPi : M) : Prop :=
  exists sourceToTargetLeaf targetToSourceLeaf : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeShiftDirectionalContextOn M baseContext
        sigmaDomain piDomain sourcePi)
      targetPi sourceToTargetLeaf /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeShiftDirectionalContextOn M baseContext
        sigmaDomain piDomain targetPi)
      sourcePi targetToSourceLeaf.

Definition RawDynamicTruthNativeShiftSigmaLocalRootsOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain sourceSigma targetSigma : M) : Prop :=
  exists sourceToTargetRoot targetToSourceRoot : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeShiftCommonContextOn M baseContext
        sigmaDomain piDomain)
      (rawFormulaImpCode M sourceSigma targetSigma)
      sourceToTargetRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeShiftCommonContextOn M baseContext
        sigmaDomain piDomain)
      (rawFormulaImpCode M targetSigma sourceSigma)
      targetToSourceRoot.

Definition RawDynamicTruthNativeShiftPiLocalRootsOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain sourcePi targetPi : M) : Prop :=
  exists sourceToTargetRoot targetToSourceRoot : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeShiftCommonContextOn M baseContext
        sigmaDomain piDomain)
      (rawFormulaImpCode M sourcePi targetPi)
      sourceToTargetRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeShiftCommonContextOn M baseContext
        sigmaDomain piDomain)
      (rawFormulaImpCode M targetPi sourcePi)
      targetToSourceRoot.

Arguments RawDynamicTruthNativeShiftSigmaDirectionalLeavesOn
  M baseContext sigmaDomain piDomain sourceSigma targetSigma
  : clear implicits.
Arguments RawDynamicTruthNativeShiftPiDirectionalLeavesOn
  M baseContext sigmaDomain piDomain sourcePi targetPi : clear implicits.
Arguments RawDynamicTruthNativeShiftSigmaLocalRootsOn
  M baseContext sigmaDomain piDomain sourceSigma targetSigma
  : clear implicits.
Arguments RawDynamicTruthNativeShiftPiLocalRootsOn
  M baseContext sigmaDomain piDomain sourcePi targetPi : clear implicits.

Theorem raw_dynamicTruthNativeShiftSigmaLocalRootsOn_of_directional_leaves :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain sourceSigma targetSigma,
  RawDynamicTruthNativeShiftSigmaDirectionalLeavesOn M baseContext
    sigmaDomain piDomain sourceSigma targetSigma ->
  RawDynamicTruthNativeShiftSigmaLocalRootsOn M baseContext
    sigmaDomain piDomain sourceSigma targetSigma.
Proof.
  intros M hPA baseContext sigmaDomain piDomain sourceSigma targetSigma
    (forwardLeaf & backwardLeaf & hforward & hbackward).
  exists
    (rawProofImpIRoot M
      (rawDynamicTruthNativeShiftCommonContextOn M baseContext
        sigmaDomain piDomain)
      sourceSigma targetSigma forwardLeaf),
    (rawProofImpIRoot M
      (rawDynamicTruthNativeShiftCommonContextOn M baseContext
        sigmaDomain piDomain)
      targetSigma sourceSigma backwardLeaf).
  split.
  - exact (raw_codedPALocalProofOf_impI M hPA
      (rawDynamicTruthNativeShiftCommonContextOn M baseContext
        sigmaDomain piDomain)
      sourceSigma targetSigma forwardLeaf hforward).
  - exact (raw_codedPALocalProofOf_impI M hPA
      (rawDynamicTruthNativeShiftCommonContextOn M baseContext
        sigmaDomain piDomain)
      targetSigma sourceSigma backwardLeaf hbackward).
Qed.

Theorem raw_dynamicTruthNativeShiftPiLocalRootsOn_of_directional_leaves :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain sourcePi targetPi,
  RawDynamicTruthNativeShiftPiDirectionalLeavesOn M baseContext
    sigmaDomain piDomain sourcePi targetPi ->
  RawDynamicTruthNativeShiftPiLocalRootsOn M baseContext
    sigmaDomain piDomain sourcePi targetPi.
Proof.
  intros M hPA baseContext sigmaDomain piDomain sourcePi targetPi
    (forwardLeaf & backwardLeaf & hforward & hbackward).
  exists
    (rawProofImpIRoot M
      (rawDynamicTruthNativeShiftCommonContextOn M baseContext
        sigmaDomain piDomain)
      sourcePi targetPi forwardLeaf),
    (rawProofImpIRoot M
      (rawDynamicTruthNativeShiftCommonContextOn M baseContext
        sigmaDomain piDomain)
      targetPi sourcePi backwardLeaf).
  split.
  - exact (raw_codedPALocalProofOf_impI M hPA
      (rawDynamicTruthNativeShiftCommonContextOn M baseContext
        sigmaDomain piDomain)
      sourcePi targetPi forwardLeaf hforward).
  - exact (raw_codedPALocalProofOf_impI M hPA
      (rawDynamicTruthNativeShiftCommonContextOn M baseContext
        sigmaDomain piDomain)
      targetPi sourcePi backwardLeaf hbackward).
Qed.

(** Exact specializations to the literal contexts exported by the original
    shift proof compiler. *)
Corollary
    raw_dynamicTruthNativeShiftSigmaLocalRootsAt_of_directional_leaves :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain sourceSigma targetSigma,
  RawDynamicTruthNativeShiftSigmaDirectionalLeavesOn M (raw_zero M)
    sigmaDomain piDomain sourceSigma targetSigma ->
  RawDynamicTruthNativeShiftSigmaLocalRootsAt M
    sigmaDomain piDomain sourceSigma targetSigma.
Proof.
  intros M hPA sigmaDomain piDomain sourceSigma targetSigma hleaves.
  exact
    (raw_dynamicTruthNativeShiftSigmaLocalRootsOn_of_directional_leaves
      M hPA (raw_zero M) sigmaDomain piDomain sourceSigma targetSigma
      hleaves).
Qed.

Corollary raw_dynamicTruthNativeShiftPiLocalRootsAt_of_directional_leaves :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain sourcePi targetPi,
  RawDynamicTruthNativeShiftPiDirectionalLeavesOn M (raw_zero M)
    sigmaDomain piDomain sourcePi targetPi ->
  RawDynamicTruthNativeShiftPiLocalRootsAt M
    sigmaDomain piDomain sourcePi targetPi.
Proof.
  intros M hPA sigmaDomain piDomain sourcePi targetPi hleaves.
  exact (raw_dynamicTruthNativeShiftPiLocalRootsOn_of_directional_leaves
    M hPA (raw_zero M) sigmaDomain piDomain sourcePi targetPi hleaves).
Qed.

(** The residual is linked to the full represented trace.  Parametrizing by
    [baseContext] prevents a proof over one witnessed PA tail from being
    reused at a different tail by definitional sleight of hand. *)
Definition RawDynamicTruthNativeShiftDirectionalLeafRootCompilerOn
    (M : RawPAModel) (baseContext : M) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
    RawDynamicTruthNativeShiftProofTraceAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi ->
    RawDynamicTruthNativeShiftSigmaDirectionalLeavesOn M baseContext
      sigmaDomain piDomain sourceSigma targetSigma /\
    RawDynamicTruthNativeShiftPiDirectionalLeavesOn M baseContext
      sigmaDomain piDomain sourcePi targetPi.

Arguments RawDynamicTruthNativeShiftDirectionalLeafRootCompilerOn
  M baseContext : clear implicits.

Theorem raw_dynamicTruthNativeShiftLocalRootsOn_of_directional_leaf_compiler :
  forall (M : RawPAModel), RawPASatisfies M -> forall baseContext,
  RawDynamicTruthNativeShiftDirectionalLeafRootCompilerOn M baseContext ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  RawDynamicTruthNativeShiftProofTraceAt M tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi ->
  RawDynamicTruthNativeShiftSigmaLocalRootsOn M baseContext
      sigmaDomain piDomain sourceSigma targetSigma /\
  RawDynamicTruthNativeShiftPiLocalRootsOn M baseContext
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
      (raw_dynamicTruthNativeShiftSigmaLocalRootsOn_of_directional_leaves
        M hPA baseContext sigmaDomain piDomain sourceSigma targetSigma
        hsigmaLeaves).
  - exact
      (raw_dynamicTruthNativeShiftPiLocalRootsOn_of_directional_leaves
        M hPA baseContext sigmaDomain piDomain sourcePi targetPi
        hpiLeaves).
Qed.

(** Literal-empty adapter to the historical local-root compiler.  This is a
    conditional adapter, not a claim that a witnessed PA tail can be erased. *)
Theorem raw_dynamicTruthNativeShiftLocalRootCompiler_of_empty_directional_leaves :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeShiftDirectionalLeafRootCompilerOn M (raw_zero M) ->
  RawDynamicTruthNativeShiftLocalRootCompiler M.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi htrace.
  destruct
    (raw_dynamicTruthNativeShiftLocalRootsOn_of_directional_leaf_compiler
      M hPA (raw_zero M) hcompiler tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi htrace) as
    [hsigma hpi].
  split.
  - exact hsigma.
  - exact hpi.
Qed.

(** A witnessed-tail form for downstream ordinary-PA packaging.  The witness
    premise is deliberately retained even though implication introduction
    itself needs only the four local leaves. *)
Definition RawDynamicTruthNativeShiftWitnessedDirectionalLeafRootInterface
    (M : RawPAModel) : Prop :=
  forall witnessList baseContext,
    RawCodedPAAxiomWitnessContext M witnessList baseContext ->
    RawDynamicTruthNativeShiftDirectionalLeafRootCompilerOn M baseContext.

Arguments RawDynamicTruthNativeShiftWitnessedDirectionalLeafRootInterface
  M : clear implicits.

Corollary raw_dynamicTruthNativeShiftWitnessedLocalRoots_of_directional_leaves :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeShiftWitnessedDirectionalLeafRootInterface M ->
  forall witnessList baseContext,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  RawDynamicTruthNativeShiftProofTraceAt M tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi ->
  RawDynamicTruthNativeShiftSigmaLocalRootsOn M baseContext
      sigmaDomain piDomain sourceSigma targetSigma /\
  RawDynamicTruthNativeShiftPiLocalRootsOn M baseContext
      sigmaDomain piDomain sourcePi targetPi.
Proof.
  intros M hPA hinterface witnessList baseContext hwitness.
  exact (raw_dynamicTruthNativeShiftLocalRootsOn_of_directional_leaf_compiler
    M hPA baseContext (hinterface witnessList baseContext hwitness)).
Qed.

End PABoundedRawCodedDynamicTruthNativeShiftLeafRootCompilation.
