(**
  Trace-linked leaf compilation for native PA-axiom soundness.

  The proof shell in
  [RawCodedDynamicTruthNativeAxiomSoundnessProofCompilation] leaves one
  local root

      witnessed-axiom /\ lower-admissible |- next-Sigma.

  This file removes the remaining fixed logical structure from that root.
  It performs three honest proof-code operations.

  - The four useful components of the antecedent are projected with an
    assumption leaf and conjunction elimination.
  - The lower-domain disjunction is split with represented disjunction
    elimination.
  - In each domain case, the existentially hidden PA-axiom witness is opened
    with represented existential elimination.  Its shifted context and
    shifted conclusion are retained explicitly.

  Consequently the residual consists of two witness-body leaves, one for
  each lower-domain case.  They are indexed by the actual paired-successor
  rows, wrapper, domain substitutions, and next-Sigma application exposed by
  the supplied trace.  An arbitrary base context and its target shift remain
  visible throughout; the witnessed-context endpoint uses the proved
  self-shift of PA-axiom contexts and never erases a nonempty tail.

  The successor and substitution relations below are code-construction
  traces, not PA proofs of their own correctness.  The witness-body leaves
  therefore remain an explicit proof-producing interface; no semantic
  validity-to-proof conversion is used.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedAssignment
  RawCodedFormulaOperations
  RawCodedFixedLevelTruthTotality
  RawCodedNumeralTermCode
  RawCodedFormulaSingleSubstitutionAtomicAdequacy
  RawCodedTermOpeningAfterShiftSyntaxStability
  RawCodedDynamicTruthTernaryApplicationTotality
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedContextShift
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitness
  RawCodedPAProofImpICertificates
  RawCodedPAAxiomContextSelfShift
  RawCodedProofAssumptionLeaf
  RawCodedProofAndEConstructors
  RawCodedProofOrEConstructor
  RawCodedProofExEConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPairedSuccessorRowGraph
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthPairedSuccessorAdequacy
  RawCodedDynamicTruthAxiomSoundnessBaseGraph
  RawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph
  RawCodedDynamicTruthNativeAxiomSoundnessProofCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeAxiomSoundnessLeafRootCompilation.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFormulaSingleSubstitutionAtomicAdequacy.
Import PABoundedRawCodedTermOpeningAfterShiftSyntaxStability.
Import PABoundedRawCodedDynamicTruthTernaryApplicationTotality.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAProofImpICertificates.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofAndEConstructors.
Import PABoundedRawCodedProofOrEConstructor.
Import PABoundedRawCodedProofExEConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
Import PABoundedRawCodedDynamicTruthAxiomSoundnessBaseGraph.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessProofCompilation.

(** ------------------------------------------------------------------
    Exact successor rows selected by the axiom-soundness trace. *)

(** All witnesses in this relation come from one paired successor.  Keeping
    the row domains and lower applications next to the wrapper prevents a
    later leaf compiler from silently choosing unrelated row parameters. *)
Definition RawDynamicTruthNativeAxiomSoundnessLinkedRowsAt
    (M : RawPAModel) (tail : nat -> M)
    (predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication : M) : Prop :=
  exists currentLevel nextGlobalSigma nextGlobalPi currentLevelNumeral
      localSigmaRow localPiRow sigmaNumeral piNumeral : M,
    RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi /\
    currentLevel = raw_succ M predecessorLevel /\
    RawNumeralTermCodeAt M
      (raw_succ M currentLevel) sigmaNumeral /\
    RawCodedFormulaSingleSubstitution M sigmaNumeral
      (rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode)
      sigmaRowDomain /\
    RawDynamicTruthCoqLowerApplication M
      currentGlobalPi lowerPiApplication /\
    localSigmaRow = rawDynamicTruthSigmaSuccessorRowCode M
      sigmaRowDomain lowerPiApplication /\
    RawNumeralTermCodeAt M
      (raw_succ M currentLevel) piNumeral /\
    RawCodedFormulaSingleSubstitution M piNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthPiRowDomainTemplate))
      piRowDomain /\
    RawDynamicTruthPiCoqLowerApplication M
      currentGlobalSigma lowerSigmaApplication /\
    localPiRow = rawDynamicTruthPiSuccessorRowCode M
      piRowDomain lowerSigmaApplication /\
    RawDynamicTruthPairedGlobalWrapperAt M
      localSigmaRow localPiRow nextGlobalSigma nextGlobalPi /\
    RawNumeralTermCodeAt M currentLevel currentLevelNumeral /\
    RawCodedFormulaSingleSubstitution M currentLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthNativeAxiomSigmaDomainTemplate))
      sigmaDomain /\
    RawCodedFormulaSingleSubstitution M currentLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthNativeAxiomPiDomainTemplate))
      piDomain /\
    RawDynamicTruthNativeAxiomApplication M
      nextGlobalSigma nextSigmaEvidence.

Arguments RawDynamicTruthNativeAxiomSoundnessLinkedRowsAt
  M tail predecessorLevel currentGlobalSigma currentGlobalPi
  sigmaDomain piDomain nextSigmaEvidence
  sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
  : clear implicits.

Theorem
    raw_dynamicTruthNativeAxiomSoundnessProofTraceAt_exposes_linked_rows :
    forall (M : RawPAModel) (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence,
  RawDynamicTruthNativeAxiomSoundnessProofTraceAt M tail
    predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence ->
  exists sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication : M,
    RawDynamicTruthNativeAxiomSoundnessLinkedRowsAt M tail
      predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication.
Proof.
  intros M tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence
    (horbit & currentLevel & nextGlobalSigma & nextGlobalPi &
      currentLevelNumeral & hlevel & hsuccessor & hlevelNumeral &
      hsigmaDomain & hpiDomain & hnextSigma).
  destruct hsuccessor as
    (localSigmaRow & localPiRow & [hsigmaRow hpiRow] & hwrapper).
  destruct hsigmaRow as
    (sigmaNumeral & sigmaRowDomain & lowerPiApplication &
      hsigmaNumeral & hsigmaRowDomain & hlowerPi & hsigmaRowCode).
  destruct hpiRow as
    (piNumeral & piRowDomain & lowerSigmaApplication &
      hpiNumeral & hpiRowDomain & hlowerSigma & hpiRowCode).
  exists sigmaRowDomain, piRowDomain,
    lowerPiApplication, lowerSigmaApplication.
  exists currentLevel, nextGlobalSigma, nextGlobalPi,
    currentLevelNumeral, localSigmaRow, localPiRow,
    sigmaNumeral, piNumeral.
  split; [exact horbit |].
  split; [exact hlevel |].
  split; [exact hsigmaNumeral |].
  split; [exact hsigmaRowDomain |].
  split; [exact hlowerPi |].
  split; [exact hsigmaRowCode |].
  split; [exact hpiNumeral |].
  split; [exact hpiRowDomain |].
  split; [exact hlowerSigma |].
  split; [exact hpiRowCode |].
  split; [exact hwrapper |].
  split; [exact hlevelNumeral |].
  split; [exact hsigmaDomain |].
  split; [exact hpiDomain | exact hnextSigma].
Qed.

Theorem raw_dynamicTruthNativeAxiomSoundnessProofTraceAt_of_linked_rows :
    forall (M : RawPAModel) (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthNativeAxiomSoundnessLinkedRowsAt M tail
    predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence
    sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthNativeAxiomSoundnessProofTraceAt M tail
    predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence.
Proof.
  intros M tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
    (currentLevel & nextGlobalSigma & nextGlobalPi & currentLevelNumeral &
      localSigmaRow & localPiRow & sigmaNumeral & piNumeral &
      horbit & hlevel & hsigmaNumeral & hsigmaRowDomain & hlowerPi &
      hsigmaRowCode & hpiNumeral & hpiRowDomain & hlowerSigma &
      hpiRowCode & hwrapper & hlevelNumeral & hsigmaDomain & hpiDomain &
      hnextSigma).
  split; [exact horbit |].
  exists currentLevel, nextGlobalSigma, nextGlobalPi, currentLevelNumeral.
  split; [exact hlevel |].
  split.
  - exists localSigmaRow, localPiRow. split.
    + split.
      * exists sigmaNumeral, sigmaRowDomain, lowerPiApplication.
        repeat split; assumption.
      * exists piNumeral, piRowDomain, lowerSigmaApplication.
        repeat split; assumption.
    + exact hwrapper.
  - repeat split; assumption.
Qed.

Corollary
    raw_dynamicTruthNativeAxiomSoundnessProofTraceAt_linked_rows_iff :
    forall (M : RawPAModel) (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence,
  RawDynamicTruthNativeAxiomSoundnessProofTraceAt M tail
    predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence <->
  exists sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication : M,
    RawDynamicTruthNativeAxiomSoundnessLinkedRowsAt M tail
      predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication.
Proof.
  intros. split.
  - apply
      raw_dynamicTruthNativeAxiomSoundnessProofTraceAt_exposes_linked_rows.
  - intros (sigmaRowDomain & piRowDomain & lowerPi & lowerSigma & hlinked).
    exact
      (raw_dynamicTruthNativeAxiomSoundnessProofTraceAt_of_linked_rows
        M tail predecessorLevel currentGlobalSigma currentGlobalPi
        sigmaDomain piDomain nextSigmaEvidence
        sigmaRowDomain piRowDomain lowerPi lowerSigma hlinked).
Qed.

(** ------------------------------------------------------------------
    Adequacy carried by the same trace. *)

Lemma raw_dynamicTruthNativeAxiomDomain_target_atomically_adequate : forall
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

Lemma raw_dynamicTruthNativeAxiomApplication_target_atomically_adequate :
    forall (M : RawPAModel), RawPASatisfies M -> forall input output,
  RawDynamicTruthNativeAxiomApplication M input output ->
  RawCodedFormulaAtomicallyAdequate M output.
Proof.
  intros M hPA input output
    (first & second & _hfirst & _hsecond & hthird).
  exact (raw_codedFormulaSingleSubstitution_target_atomically_adequate
    M hPA (raw_codedTermOpeningAfterShiftSyntaxStable_of_PA M hPA)
    (rawNumeralValue M
      (termCode dynamicTruthNativeAxiomApplicationThirdReplacement))
    (raw_zero M) (raw_zero M)
    (raw_dynamicTruthApplication_fixedReplacement_syntax
      M hPA dynamicTruthNativeAxiomApplicationThirdReplacement)
    second output hthird).
Qed.

Lemma raw_dynamicTruthNativeAxiomAntecedent_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall sigmaDomain piDomain,
  RawCodedFormulaAtomicallyAdequate M sigmaDomain ->
  RawCodedFormulaAtomicallyAdequate M piDomain ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
      sigmaDomain piDomain).
Proof.
  intros M hPA sigmaDomain piDomain hsigma hpi.
  unfold rawDynamicTruthNativeAxiomSoundnessAntecedentCode,
    rawDynamicTruthNativeAxiomLowerAdmissibleCode.
  apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
  - exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
      (witnessedPAAxiomRecognitionTermAt (tVar 0))).
  - apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
    + exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
        (codedFormulaAtomicallyAdequateTermAt (tVar 0))).
    + apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
      * exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
          (codedAssignmentDefinedThroughTermAt tZero tZero (tVar 0))).
      * exact (raw_formulaOrCode_atomically_adequate
          M hPA sigmaDomain piDomain hsigma hpi).
Qed.

Record RawDynamicTruthNativeAxiomSoundnessTraceAdequacyAt
    (M : RawPAModel)
    (sigmaDomain piDomain nextSigmaEvidence : M) : Prop := {
  rawDynamicTruthNativeAxiomSoundness_sigmaDomain_adequate :
    RawCodedFormulaAtomicallyAdequate M sigmaDomain;
  rawDynamicTruthNativeAxiomSoundness_piDomain_adequate :
    RawCodedFormulaAtomicallyAdequate M piDomain;
  rawDynamicTruthNativeAxiomSoundness_nextSigma_adequate :
    RawCodedFormulaAtomicallyAdequate M nextSigmaEvidence;
  rawDynamicTruthNativeAxiomSoundness_antecedent_adequate :
    RawCodedFormulaAtomicallyAdequate M
      (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
        sigmaDomain piDomain)
}.

Arguments RawDynamicTruthNativeAxiomSoundnessTraceAdequacyAt
  M sigmaDomain piDomain nextSigmaEvidence : clear implicits.

Theorem raw_dynamicTruthNativeAxiomSoundnessLinkedRowsAt_adequacy : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthNativeAxiomSoundnessLinkedRowsAt M tail
    predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence
    sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthNativeAxiomSoundnessTraceAdequacyAt M
    sigmaDomain piDomain nextSigmaEvidence.
Proof.
  intros M hPA tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
    (currentLevel & nextGlobalSigma & nextGlobalPi & currentLevelNumeral &
      localSigmaRow & localPiRow & sigmaNumeral & piNumeral &
      horbit & hlevel & hsigmaNumeral & hsigmaRowDomain & hlowerPi &
      hsigmaRowCode & hpiNumeral & hpiRowDomain & hlowerSigma &
      hpiRowCode & hwrapper & hlevelNumeral & hsigmaDomain & hpiDomain &
      hnextSigma).
  assert (hsigmaDomainAdequate :
      RawCodedFormulaAtomicallyAdequate M sigmaDomain).
  { exact (raw_dynamicTruthNativeAxiomDomain_target_atomically_adequate
      M hPA currentLevel currentLevelNumeral
      (formulaCode dynamicTruthNativeAxiomSigmaDomainTemplate)
      sigmaDomain hlevelNumeral hsigmaDomain). }
  assert (hpiDomainAdequate :
      RawCodedFormulaAtomicallyAdequate M piDomain).
  { exact (raw_dynamicTruthNativeAxiomDomain_target_atomically_adequate
      M hPA currentLevel currentLevelNumeral
      (formulaCode dynamicTruthNativeAxiomPiDomainTemplate)
      piDomain hlevelNumeral hpiDomain). }
  refine
    {| rawDynamicTruthNativeAxiomSoundness_sigmaDomain_adequate :=
         hsigmaDomainAdequate;
       rawDynamicTruthNativeAxiomSoundness_piDomain_adequate :=
         hpiDomainAdequate;
       rawDynamicTruthNativeAxiomSoundness_nextSigma_adequate :=
         raw_dynamicTruthNativeAxiomApplication_target_atomically_adequate
           M hPA nextGlobalSigma nextSigmaEvidence hnextSigma;
       rawDynamicTruthNativeAxiomSoundness_antecedent_adequate :=
         raw_dynamicTruthNativeAxiomAntecedent_atomically_adequate
           M hPA sigmaDomain piDomain
           hsigmaDomainAdequate hpiDomainAdequate |}.
Qed.

(** ------------------------------------------------------------------
    Transparent antecedent and its concrete projection roots. *)

Definition dynamicTruthNativeAxiomWitnessBodyFormula : formula :=
  codedPAAxiomWitnessTermAt (tVar 0) (liftTerm 1 (tVar 0)).

Definition rawDynamicTruthNativeAxiomWitnessBodyCode
    (M : RawPAModel) : M :=
  rawNumeralValue M (formulaCode dynamicTruthNativeAxiomWitnessBodyFormula).

Definition rawDynamicTruthNativeAxiomRecognitionCode
    (M : RawPAModel) : M :=
  rawFormulaExCode M (rawDynamicTruthNativeAxiomWitnessBodyCode M).

Definition rawDynamicTruthNativeAxiomAtomicAdequacyCode
    (M : RawPAModel) : M :=
  rawNumeralValue M
    (formulaCode (codedFormulaAtomicallyAdequateTermAt (tVar 0))).

Definition rawDynamicTruthNativeAxiomAssignmentDefinedCode
    (M : RawPAModel) : M :=
  rawNumeralValue M
    (formulaCode
      (codedAssignmentDefinedThroughTermAt tZero tZero (tVar 0))).

Arguments rawDynamicTruthNativeAxiomWitnessBodyCode M : clear implicits.
Arguments rawDynamicTruthNativeAxiomRecognitionCode M : clear implicits.
Arguments rawDynamicTruthNativeAxiomAtomicAdequacyCode M : clear implicits.
Arguments rawDynamicTruthNativeAxiomAssignmentDefinedCode M
  : clear implicits.

(** The recognition conjunct really is an existential constructor code.
    This equation is what permits the represented Ex-E rule below; merely
    knowing the recognizer's semantics would not suffice. *)
Lemma rawDynamicTruthNativeAxiomRecognitionCode_eq_numeral : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthNativeAxiomRecognitionCode M =
  rawNumeralValue M
    (formulaCode (witnessedPAAxiomRecognitionTermAt (tVar 0))).
Proof.
  intros M hPA.
  unfold rawDynamicTruthNativeAxiomRecognitionCode,
    rawDynamicTruthNativeAxiomWitnessBodyCode,
    dynamicTruthNativeAxiomWitnessBodyFormula,
    witnessedPAAxiomRecognitionTermAt.
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    (codedPAAxiomWitnessTermAt (tVar 0) (liftTerm 1 (tVar 0)))).
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    (pEx
      (codedPAAxiomWitnessTermAt (tVar 0) (liftTerm 1 (tVar 0))))).
  reflexivity.
Qed.

Lemma rawDynamicTruthNativeAxiomSoundnessAntecedentCode_as_components :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain,
  rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
      sigmaDomain piDomain =
  rawFormulaAndCode M
    (rawDynamicTruthNativeAxiomRecognitionCode M)
    (rawFormulaAndCode M
      (rawDynamicTruthNativeAxiomAtomicAdequacyCode M)
      (rawFormulaAndCode M
        (rawDynamicTruthNativeAxiomAssignmentDefinedCode M)
        (rawFormulaOrCode M sigmaDomain piDomain))).
Proof.
  intros M hPA sigmaDomain piDomain.
  unfold rawDynamicTruthNativeAxiomSoundnessAntecedentCode,
    rawDynamicTruthNativeAxiomLowerAdmissibleCode,
    rawDynamicTruthNativeAxiomAtomicAdequacyCode,
    rawDynamicTruthNativeAxiomAssignmentDefinedCode.
  rewrite rawDynamicTruthNativeAxiomRecognitionCode_eq_numeral
    by exact hPA.
  reflexivity.
Qed.

Definition rawDynamicTruthNativeAxiomContextOn
    (M : RawPAModel) (baseContext sigmaDomain piDomain : M) : M :=
  rawListNode M
    (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
      sigmaDomain piDomain)
    baseContext.

Definition rawDynamicTruthNativeAxiomDomainContextOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain domain : M) : M :=
  rawListNode M domain
    (rawDynamicTruthNativeAxiomContextOn M baseContext
      sigmaDomain piDomain).

Arguments rawDynamicTruthNativeAxiomContextOn
  M baseContext sigmaDomain piDomain : clear implicits.
Arguments rawDynamicTruthNativeAxiomDomainContextOn
  M baseContext sigmaDomain piDomain domain : clear implicits.

Definition RawDynamicTruthNativeAxiomAntecedentProjectionRootsOn
    (M : RawPAModel) (baseContext sigmaDomain piDomain : M) : Prop :=
  exists recognitionRoot atomicRoot assignmentRoot domainRoot : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeAxiomContextOn M baseContext
        sigmaDomain piDomain)
      (rawDynamicTruthNativeAxiomRecognitionCode M) recognitionRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeAxiomContextOn M baseContext
        sigmaDomain piDomain)
      (rawDynamicTruthNativeAxiomAtomicAdequacyCode M) atomicRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeAxiomContextOn M baseContext
        sigmaDomain piDomain)
      (rawDynamicTruthNativeAxiomAssignmentDefinedCode M) assignmentRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeAxiomContextOn M baseContext
        sigmaDomain piDomain)
      (rawFormulaOrCode M sigmaDomain piDomain) domainRoot.

Arguments RawDynamicTruthNativeAxiomAntecedentProjectionRootsOn
  M baseContext sigmaDomain piDomain : clear implicits.

Theorem raw_dynamicTruthNativeAxiomAntecedentProjectionRootsOn : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain,
  RawContextListRealizable M baseContext ->
  RawDynamicTruthNativeAxiomAntecedentProjectionRootsOn M
    baseContext sigmaDomain piDomain.
Proof.
  intros M hPA baseContext sigmaDomain piDomain hbase.
  set (recognition := rawDynamicTruthNativeAxiomRecognitionCode M).
  set (atomic := rawDynamicTruthNativeAxiomAtomicAdequacyCode M).
  set (assignment := rawDynamicTruthNativeAxiomAssignmentDefinedCode M).
  set (domain := rawFormulaOrCode M sigmaDomain piDomain).
  unfold RawDynamicTruthNativeAxiomAntecedentProjectionRootsOn,
    rawDynamicTruthNativeAxiomContextOn.
  rewrite
    (rawDynamicTruthNativeAxiomSoundnessAntecedentCode_as_components
      M hPA sigmaDomain piDomain).
  set (context := rawListNode M
    (rawFormulaAndCode M recognition
      (rawFormulaAndCode M atomic
        (rawFormulaAndCode M assignment domain))) baseContext).
  pose proof (raw_codedPALocalProofOf_assumption M hPA baseContext
    (rawFormulaAndCode M recognition
      (rawFormulaAndCode M atomic
        (rawFormulaAndCode M assignment domain))) hbase) as hall.
  change (RawCodedPALocalProofOf M context
    (rawFormulaAndCode M recognition
      (rawFormulaAndCode M atomic
        (rawFormulaAndCode M assignment domain)))
    (rawProofAssumptionRoot M context
      (rawFormulaAndCode M recognition
        (rawFormulaAndCode M atomic
          (rawFormulaAndCode M assignment domain))))) in hall.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA context recognition
    (rawFormulaAndCode M atomic
      (rawFormulaAndCode M assignment domain)) _ hall) as hrecognition.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context recognition
    (rawFormulaAndCode M atomic
      (rawFormulaAndCode M assignment domain)) _ hall) as hrest1.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA context atomic
    (rawFormulaAndCode M assignment domain) _ hrest1) as hatomic.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context atomic
    (rawFormulaAndCode M assignment domain) _ hrest1) as hrest2.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA context assignment
    domain _ hrest2) as hassignment.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context assignment
    domain _ hrest2) as hdomain.
  do 4 eexists.
  split; [exact hrecognition |].
  split; [exact hatomic |].
  split; [exact hassignment | exact hdomain].
Qed.

(** ------------------------------------------------------------------
    Witness-body leaves with their exact binder shifts. *)

Definition rawDynamicTruthNativeAxiomShiftedDomainContext
    (M : RawPAModel)
    (shiftedBase shiftedAntecedent shiftedDomain : M) : M :=
  rawListNode M shiftedDomain
    (rawListNode M shiftedAntecedent shiftedBase).

Definition rawDynamicTruthNativeAxiomWitnessContext
    (M : RawPAModel)
    (shiftedBase shiftedAntecedent shiftedDomain : M) : M :=
  rawListNode M (rawDynamicTruthNativeAxiomWitnessBodyCode M)
    (rawDynamicTruthNativeAxiomShiftedDomainContext M
      shiftedBase shiftedAntecedent shiftedDomain).

Arguments rawDynamicTruthNativeAxiomShiftedDomainContext
  M shiftedBase shiftedAntecedent shiftedDomain : clear implicits.
Arguments rawDynamicTruthNativeAxiomWitnessContext
  M shiftedBase shiftedAntecedent shiftedDomain : clear implicits.

(** Each leaf is accompanied by all four shifts used by its surrounding
    Ex-E construction.  Formula-shift functionality therefore pins the leaf
    to the original antecedent, domain formula, and next-Sigma target. *)
Definition RawDynamicTruthNativeAxiomWitnessDomainLeavesOn
    (M : RawPAModel)
    (baseContext shiftedBaseContext sigmaDomain piDomain
      nextSigmaEvidence : M) : Prop :=
  exists shiftedAntecedent shiftedSigmaDomain shiftedPiDomain
      shiftedNextSigma sigmaLeaf piLeaf : M,
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1)
      (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
        sigmaDomain piDomain)
      shiftedAntecedent /\
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1)
      sigmaDomain shiftedSigmaDomain /\
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1)
      piDomain shiftedPiDomain /\
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1)
      nextSigmaEvidence shiftedNextSigma /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeAxiomWitnessContext M
        shiftedBaseContext shiftedAntecedent shiftedSigmaDomain)
      shiftedNextSigma sigmaLeaf /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeAxiomWitnessContext M
        shiftedBaseContext shiftedAntecedent shiftedPiDomain)
      shiftedNextSigma piLeaf.

Arguments RawDynamicTruthNativeAxiomWitnessDomainLeavesOn
  M baseContext shiftedBaseContext sigmaDomain piDomain nextSigmaEvidence
  : clear implicits.

(** The leaf compiler consumes concrete linked rows, not arbitrary row
    parameters.  The base-context shift is also explicit, which makes the
    interface usable both at the literal empty base and over a witnessed PA
    tail fixed by eigenvariable shift. *)
Definition RawDynamicTruthNativeAxiomLinkedWitnessLeafRootCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication
      baseContext shiftedBaseContext,
    RawDynamicTruthNativeAxiomSoundnessLinkedRowsAt M tail
      predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication ->
    RawContextShift M baseContext shiftedBaseContext ->
    RawDynamicTruthNativeAxiomWitnessDomainLeavesOn M
      baseContext shiftedBaseContext sigmaDomain piDomain
      nextSigmaEvidence.

Arguments RawDynamicTruthNativeAxiomLinkedWitnessLeafRootCompiler M
  : clear implicits.

(** Pointwise form of the genuine residual.  All four formula shifts have
    already been fixed, so the callback returns only the two represented PA
    proof roots.  Its linkage premise retains the exact successor rows which
    generated [nextSigmaEvidence]. *)
Definition RawDynamicTruthNativeAxiomLinkedWitnessBodyLeafRootCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication
      baseContext shiftedBaseContext
      shiftedAntecedent shiftedSigmaDomain shiftedPiDomain
      shiftedNextSigma,
    RawDynamicTruthNativeAxiomSoundnessLinkedRowsAt M tail
      predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication ->
    RawContextShift M baseContext shiftedBaseContext ->
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1)
      (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
        sigmaDomain piDomain)
      shiftedAntecedent ->
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1)
      sigmaDomain shiftedSigmaDomain ->
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1)
      piDomain shiftedPiDomain ->
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1)
      nextSigmaEvidence shiftedNextSigma ->
    exists sigmaLeaf piLeaf : M,
      RawCodedPALocalProofOf M
        (rawDynamicTruthNativeAxiomWitnessContext M
          shiftedBaseContext shiftedAntecedent shiftedSigmaDomain)
        shiftedNextSigma sigmaLeaf /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthNativeAxiomWitnessContext M
          shiftedBaseContext shiftedAntecedent shiftedPiDomain)
        shiftedNextSigma piLeaf.

Arguments RawDynamicTruthNativeAxiomLinkedWitnessBodyLeafRootCompiler M
  : clear implicits.

(** Shift totality discharges every binder-renaming witness.  The only data
    requested from [hbody] are the two proof roots themselves. *)
Theorem
    raw_dynamicTruthNativeAxiomLinkedWitnessLeafRootCompiler_of_body_leaf_compiler :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeAxiomLinkedWitnessBodyLeafRootCompiler M ->
  RawDynamicTruthNativeAxiomLinkedWitnessLeafRootCompiler M.
Proof.
  intros M hPA hbody tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication
    baseContext shiftedBaseContext hlinked hbaseShift.
  pose proof (raw_dynamicTruthNativeAxiomSoundnessLinkedRowsAt_adequacy
    M hPA tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence
    sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication hlinked) as hadequacy.
  destruct (raw_codedFormulaUnitShift_exists M hPA
    (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
      sigmaDomain piDomain)
    (rawDynamicTruthNativeAxiomSoundness_antecedent_adequate
      M sigmaDomain piDomain nextSigmaEvidence hadequacy)) as
    [shiftedAntecedent hantecedentShift].
  destruct (raw_codedFormulaUnitShift_exists M hPA sigmaDomain
    (rawDynamicTruthNativeAxiomSoundness_sigmaDomain_adequate
      M sigmaDomain piDomain nextSigmaEvidence hadequacy)) as
    [shiftedSigmaDomain hsigmaShift].
  destruct (raw_codedFormulaUnitShift_exists M hPA piDomain
    (rawDynamicTruthNativeAxiomSoundness_piDomain_adequate
      M sigmaDomain piDomain nextSigmaEvidence hadequacy)) as
    [shiftedPiDomain hpiShift].
  destruct (raw_codedFormulaUnitShift_exists M hPA nextSigmaEvidence
    (rawDynamicTruthNativeAxiomSoundness_nextSigma_adequate
      M sigmaDomain piDomain nextSigmaEvidence hadequacy)) as
    [shiftedNextSigma hnextShift].
  destruct (hbody tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication
    baseContext shiftedBaseContext shiftedAntecedent
    shiftedSigmaDomain shiftedPiDomain shiftedNextSigma
    hlinked hbaseShift hantecedentShift hsigmaShift hpiShift hnextShift) as
    (sigmaLeaf & piLeaf & hsigmaLeaf & hpiLeaf).
  exists shiftedAntecedent, shiftedSigmaDomain, shiftedPiDomain,
    shiftedNextSigma, sigmaLeaf, piLeaf.
  split; [exact hantecedentShift |].
  split; [exact hsigmaShift |].
  split; [exact hpiShift |].
  split; [exact hnextShift |].
  split; [exact hsigmaLeaf | exact hpiLeaf].
Qed.

(** ------------------------------------------------------------------
    Structural assembly of Ex-E in each domain case and Or-E outside. *)

Definition RawDynamicTruthNativeAxiomLocalRootOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain nextSigmaEvidence : M) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeAxiomContextOn M baseContext
        sigmaDomain piDomain)
      nextSigmaEvidence root.

Arguments RawDynamicTruthNativeAxiomLocalRootOn
  M baseContext sigmaDomain piDomain nextSigmaEvidence : clear implicits.

Theorem raw_dynamicTruthNativeAxiomLocalRootOn_of_witness_domain_leaves :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      baseContext shiftedBaseContext sigmaDomain piDomain
      nextSigmaEvidence,
  RawContextListRealizable M baseContext ->
  RawContextShift M baseContext shiftedBaseContext ->
  RawCodedFormulaAtomicallyAdequate M sigmaDomain ->
  RawCodedFormulaAtomicallyAdequate M piDomain ->
  RawDynamicTruthNativeAxiomWitnessDomainLeavesOn M
    baseContext shiftedBaseContext sigmaDomain piDomain
    nextSigmaEvidence ->
  RawDynamicTruthNativeAxiomLocalRootOn M baseContext
    sigmaDomain piDomain nextSigmaEvidence.
Proof.
  intros M hPA baseContext shiftedBaseContext sigmaDomain piDomain
    nextSigmaEvidence hbase hbaseShift hsigmaAdequate hpiAdequate
    (shiftedAntecedent & shiftedSigmaDomain & shiftedPiDomain &
      shiftedNextSigma & sigmaLeaf & piLeaf &
      hantecedentShift & hsigmaShift & hpiShift & hnextShift &
      hsigmaLeaf & hpiLeaf).
  destruct (raw_dynamicTruthNativeAxiomAntecedentProjectionRootsOn
    M hPA baseContext sigmaDomain piDomain hbase) as
    (recognitionRoot & atomicRoot & assignmentRoot & domainRoot &
      hrecognition & hatomic & hassignment & hdomain).
  set (context := rawDynamicTruthNativeAxiomContextOn M baseContext
    sigmaDomain piDomain).
  assert (hcontext : RawContextListRealizable M context).
  { unfold context, rawDynamicTruthNativeAxiomContextOn.
    exact (raw_contextList_cons_realizable M hPA baseContext
      (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
        sigmaDomain piDomain) hbase). }

  (** The recognition projection is first weakened into each domain case.
      The guarded transplant is legitimate because the trace has certified
      both domain formulae as adequate syntax. *)
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA context sigmaDomain
    (rawDynamicTruthNativeAxiomRecognitionCode M) recognitionRoot
    hsigmaAdequate hcontext hrecognition) as
    [recognitionAtSigma hrecognitionAtSigma].
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA context piDomain
    (rawDynamicTruthNativeAxiomRecognitionCode M) recognitionRoot
    hpiAdequate hcontext hrecognition) as
    [recognitionAtPi hrecognitionAtPi].

  assert (hcontextShift : RawContextShift M context
      (rawListNode M shiftedAntecedent shiftedBaseContext)).
  { unfold context, rawDynamicTruthNativeAxiomContextOn.
    exact (raw_contextShift_cons M hPA
      baseContext shiftedBaseContext
      (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
        sigmaDomain piDomain)
      shiftedAntecedent hbaseShift hantecedentShift). }
  assert (hsigmaContextShift : RawContextShift M
      (rawDynamicTruthNativeAxiomDomainContextOn M baseContext
        sigmaDomain piDomain sigmaDomain)
      (rawDynamicTruthNativeAxiomShiftedDomainContext M
        shiftedBaseContext shiftedAntecedent shiftedSigmaDomain)).
  { unfold rawDynamicTruthNativeAxiomDomainContextOn,
      rawDynamicTruthNativeAxiomShiftedDomainContext.
    exact (raw_contextShift_cons M hPA
      context (rawListNode M shiftedAntecedent shiftedBaseContext)
      sigmaDomain shiftedSigmaDomain hcontextShift hsigmaShift). }
  assert (hpiContextShift : RawContextShift M
      (rawDynamicTruthNativeAxiomDomainContextOn M baseContext
        sigmaDomain piDomain piDomain)
      (rawDynamicTruthNativeAxiomShiftedDomainContext M
        shiftedBaseContext shiftedAntecedent shiftedPiDomain)).
  { unfold rawDynamicTruthNativeAxiomDomainContextOn,
      rawDynamicTruthNativeAxiomShiftedDomainContext.
    exact (raw_contextShift_cons M hPA
      context (rawListNode M shiftedAntecedent shiftedBaseContext)
      piDomain shiftedPiDomain hcontextShift hpiShift). }

  set (sigmaExRoot := rawProofExERoot M
    (rawDynamicTruthNativeAxiomDomainContextOn M baseContext
      sigmaDomain piDomain sigmaDomain)
    (rawDynamicTruthNativeAxiomWitnessBodyCode M)
    nextSigmaEvidence recognitionAtSigma sigmaLeaf).
  set (piExRoot := rawProofExERoot M
    (rawDynamicTruthNativeAxiomDomainContextOn M baseContext
      sigmaDomain piDomain piDomain)
    (rawDynamicTruthNativeAxiomWitnessBodyCode M)
    nextSigmaEvidence recognitionAtPi piLeaf).
  assert (hsigmaCase : RawCodedPALocalProofOf M
      (rawDynamicTruthNativeAxiomDomainContextOn M baseContext
        sigmaDomain piDomain sigmaDomain)
      nextSigmaEvidence sigmaExRoot).
  { unfold sigmaExRoot.
    apply (raw_codedPALocalProofOf_exE M hPA
      (rawDynamicTruthNativeAxiomDomainContextOn M baseContext
        sigmaDomain piDomain sigmaDomain)
      (rawDynamicTruthNativeAxiomShiftedDomainContext M
        shiftedBaseContext shiftedAntecedent shiftedSigmaDomain)
      (rawDynamicTruthNativeAxiomWitnessBodyCode M)
      nextSigmaEvidence shiftedNextSigma
      recognitionAtSigma sigmaLeaf).
    - exact hrecognitionAtSigma.
    - exact hsigmaContextShift.
    - exact hnextShift.
    - exact hsigmaLeaf. }
  assert (hpiCase : RawCodedPALocalProofOf M
      (rawDynamicTruthNativeAxiomDomainContextOn M baseContext
        sigmaDomain piDomain piDomain)
      nextSigmaEvidence piExRoot).
  { unfold piExRoot.
    apply (raw_codedPALocalProofOf_exE M hPA
      (rawDynamicTruthNativeAxiomDomainContextOn M baseContext
        sigmaDomain piDomain piDomain)
      (rawDynamicTruthNativeAxiomShiftedDomainContext M
        shiftedBaseContext shiftedAntecedent shiftedPiDomain)
      (rawDynamicTruthNativeAxiomWitnessBodyCode M)
      nextSigmaEvidence shiftedNextSigma
      recognitionAtPi piLeaf).
    - exact hrecognitionAtPi.
    - exact hpiContextShift.
    - exact hnextShift.
    - exact hpiLeaf. }

  exists (rawProofOrERoot M context sigmaDomain piDomain
    nextSigmaEvidence domainRoot sigmaExRoot piExRoot).
  exact (raw_codedPALocalProofOf_orE M hPA
    context sigmaDomain piDomain nextSigmaEvidence
    domainRoot sigmaExRoot piExRoot
    hdomain hsigmaCase hpiCase).
Qed.

(** Pointwise use of the exact linked compiler over any base whose shift is
    known.  This theorem is the reusable nonempty-tail endpoint. *)
Theorem raw_dynamicTruthNativeAxiomLocalRootOn_of_linked_compiler : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeAxiomLinkedWitnessLeafRootCompiler M ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence
      baseContext shiftedBaseContext,
  RawDynamicTruthNativeAxiomSoundnessProofTraceAt M tail
    predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence ->
  RawContextListRealizable M baseContext ->
  RawContextShift M baseContext shiftedBaseContext ->
  RawDynamicTruthNativeAxiomLocalRootOn M baseContext
    sigmaDomain piDomain nextSigmaEvidence.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence baseContext shiftedBaseContext htrace hbase hshift.
  destruct
    (raw_dynamicTruthNativeAxiomSoundnessProofTraceAt_exposes_linked_rows
      M tail predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence htrace) as
    (sigmaRowDomain & piRowDomain & lowerPi & lowerSigma & hlinked).
  pose proof (raw_dynamicTruthNativeAxiomSoundnessLinkedRowsAt_adequacy
    M hPA tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma hlinked) as hadequacy.
  exact
    (raw_dynamicTruthNativeAxiomLocalRootOn_of_witness_domain_leaves
      M hPA baseContext shiftedBaseContext sigmaDomain piDomain
      nextSigmaEvidence hbase hshift
      (rawDynamicTruthNativeAxiomSoundness_sigmaDomain_adequate
        M sigmaDomain piDomain nextSigmaEvidence hadequacy)
      (rawDynamicTruthNativeAxiomSoundness_piDomain_adequate
        M sigmaDomain piDomain nextSigmaEvidence hadequacy)
      (hcompiler tail predecessorLevel
        currentGlobalSigma currentGlobalPi sigmaDomain piDomain
        nextSigmaEvidence sigmaRowDomain piRowDomain lowerPi lowerSigma
        baseContext shiftedBaseContext hlinked hshift)).
Qed.

(** A witnessed PA tail is its own target shift.  This corollary is
    intentionally stated with the same [baseContext] on both sides rather
    than replacing it by zero. *)
Corollary
    raw_dynamicTruthNativeAxiomLocalRootOn_witnessed_context_of_compiler :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeAxiomLinkedWitnessLeafRootCompiler M ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence
      witnessList baseContext,
  RawDynamicTruthNativeAxiomSoundnessProofTraceAt M tail
    predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawDynamicTruthNativeAxiomLocalRootOn M baseContext
    sigmaDomain piDomain nextSigmaEvidence.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence witnessList baseContext htrace hwitness.
  exact (raw_dynamicTruthNativeAxiomLocalRootOn_of_linked_compiler
    M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence baseContext baseContext htrace
    (raw_codedPAAxiomWitnessContext_context_realizable
      M witnessList baseContext hwitness)
    (raw_codedPAAxiomWitnessContext_selfShift
      M hPA witnessList baseContext hwitness)).
Qed.

(** ------------------------------------------------------------------
    Literal-empty adapter to the compiler required by the old shell. *)

Definition
    RawDynamicTruthNativeAxiomLinkedWitnessLeafRootInterfaceAtEmptyBase
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence,
    RawDynamicTruthNativeAxiomSoundnessProofTraceAt M tail
      predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence ->
    exists sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication : M,
      RawDynamicTruthNativeAxiomSoundnessLinkedRowsAt M tail
        predecessorLevel currentGlobalSigma currentGlobalPi
        sigmaDomain piDomain nextSigmaEvidence
        sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication /\
      RawDynamicTruthNativeAxiomWitnessDomainLeavesOn M
        (raw_zero M) (raw_zero M)
        sigmaDomain piDomain nextSigmaEvidence.

Arguments
  RawDynamicTruthNativeAxiomLinkedWitnessLeafRootInterfaceAtEmptyBase M
  : clear implicits.

Theorem
    raw_dynamicTruthNativeAxiomLinkedWitnessLeafRootInterfaceAtEmptyBase_of_compiler :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeAxiomLinkedWitnessLeafRootCompiler M ->
  RawDynamicTruthNativeAxiomLinkedWitnessLeafRootInterfaceAtEmptyBase M.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence htrace.
  destruct
    (raw_dynamicTruthNativeAxiomSoundnessProofTraceAt_exposes_linked_rows
      M tail predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence htrace) as
    (sigmaRowDomain & piRowDomain & lowerPi & lowerSigma & hlinked).
  exists sigmaRowDomain, piRowDomain, lowerPi, lowerSigma.
  split; [exact hlinked |].
  exact (hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence sigmaRowDomain piRowDomain lowerPi lowerSigma
    (raw_zero M) (raw_zero M) hlinked
    (raw_contextShift_empty M hPA)).
Qed.

Lemma raw_dynamicTruthNativeAxiomLocalRootAt_of_empty_base : forall
    (M : RawPAModel) sigmaDomain piDomain nextSigmaEvidence,
  RawDynamicTruthNativeAxiomLocalRootOn M (raw_zero M)
    sigmaDomain piDomain nextSigmaEvidence ->
  RawDynamicTruthNativeAxiomSoundnessLocalRootAt M
    sigmaDomain piDomain nextSigmaEvidence.
Proof.
  intros M sigmaDomain piDomain nextSigmaEvidence hroot.
  exact hroot.
Qed.

(** This is the exact reduction of the original missing compiler.  Its only
    premise supplies two witness-body leaves at shifts selected from the
    same trace-linked successor data. *)
Theorem
    raw_dynamicTruthNativeAxiomSoundnessLocalRootCompiler_of_linked_empty_base_witness_leaves :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeAxiomLinkedWitnessLeafRootInterfaceAtEmptyBase M ->
  RawDynamicTruthNativeAxiomSoundnessLocalRootCompiler M.
Proof.
  intros M hPA hleaves tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence htrace.
  destruct (hleaves tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence htrace) as
    (sigmaRowDomain & piRowDomain & lowerPi & lowerSigma &
      hlinked & hwitnessLeaves).
  pose proof (raw_dynamicTruthNativeAxiomSoundnessLinkedRowsAt_adequacy
    M hPA tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma hlinked) as hadequacy.
  apply raw_dynamicTruthNativeAxiomLocalRootAt_of_empty_base.
  exact
    (raw_dynamicTruthNativeAxiomLocalRootOn_of_witness_domain_leaves
      M hPA (raw_zero M) (raw_zero M)
      sigmaDomain piDomain nextSigmaEvidence
      (raw_contextList_empty_realizable M hPA)
      (raw_contextShift_empty M hPA)
      (rawDynamicTruthNativeAxiomSoundness_sigmaDomain_adequate
        M sigmaDomain piDomain nextSigmaEvidence hadequacy)
      (rawDynamicTruthNativeAxiomSoundness_piDomain_adequate
        M sigmaDomain piDomain nextSigmaEvidence hadequacy)
      hwitnessLeaves).
Qed.

Corollary
    raw_dynamicTruthNativeAxiomSoundnessLocalRootCompiler_of_linked_witness_leaf_compiler :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeAxiomLinkedWitnessLeafRootCompiler M ->
  RawDynamicTruthNativeAxiomSoundnessLocalRootCompiler M.
Proof.
  intros M hPA hcompiler.
  exact
    (raw_dynamicTruthNativeAxiomSoundnessLocalRootCompiler_of_linked_empty_base_witness_leaves
      M hPA
      (raw_dynamicTruthNativeAxiomLinkedWitnessLeafRootInterfaceAtEmptyBase_of_compiler
        M hPA hcompiler)).
Qed.

(** Most reduced public endpoint: formula-shift witnesses, projections,
    context transports, both Ex-E nodes, the Or-E node, and the old
    All/Imp shell are all compiled outside the remaining two leaves. *)
Corollary
    raw_dynamicTruthNativeAxiomSoundnessLocalRootCompiler_of_linked_witness_body_leaves :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeAxiomLinkedWitnessBodyLeafRootCompiler M ->
  RawDynamicTruthNativeAxiomSoundnessLocalRootCompiler M.
Proof.
  intros M hPA hbody.
  exact
    (raw_dynamicTruthNativeAxiomSoundnessLocalRootCompiler_of_linked_witness_leaf_compiler
      M hPA
      (raw_dynamicTruthNativeAxiomLinkedWitnessLeafRootCompiler_of_body_leaf_compiler
        M hPA hbody)).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeAxiomSoundnessLeafRootCompilation.
