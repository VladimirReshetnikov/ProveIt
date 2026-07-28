(**
  Trace-linked leaf compilation for native adjacent-level coherence.

  The cross-level proof shell asks for four directional roots.  This file
  performs two reductions which are important for keeping that request
  honest.

  First, [RawDynamicTruthNativeCrossLevelLinkedRowsAt] exposes the *actual*
  Sigma and Pi successor rows hidden in the paired global-successor edge.
  The row domains, lower applications, global wrapper, and all four ternary
  applications are kept in one relation, so none of the parameters supplied
  to a later proof compiler can drift away from the original trace.

  Second, one guarded-equivalence root per polarity is enough.  Context
  insertion, assumption leaves, implication elimination, and conjunction
  projections compile each guarded root into its two directional leaves.
  The construction is parameterized by a literal base context; specializing
  that base to [raw_zero M] recovers exactly the contexts required by
  [RawDynamicTruthNativeCrossLevelLocalRootCompiler].

  The two trace-linked guarded roots remain explicit.  They are the genuine
  object-arithmetic coherence step: the existing successor-row and global-
  wrapper relations are semantic/code-construction traces, not represented
  PA proofs of their own correctness.  No witnessed nonempty context is
  erased, and no validity, completeness, proof irrelevance, or choice
  principle is used below.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedAssignment
  RawCodedNumeralTermCode
  RawCodedFixedLevelTruthTotality
  RawCodedRestrictedProofStandardAdequacy
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedProofAssumptionLeaf
  RawCodedProofBinaryConstructors
  RawCodedProofAndEConstructors
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPairedSuccessorRowGraph
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthPairedSuccessorAdequacy
  RawCodedDynamicTruthGlobalSuccessorRootClosure
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeCrossLevelPositiveGraph
  RawCodedDynamicTruthNativeCrossLevelProofCompilation.

Module PABoundedRawCodedDynamicTruthNativeCrossLevelLeafRootCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedRestrictedProofStandardAdequacy.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofAndEConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
Import PABoundedRawCodedDynamicTruthGlobalSuccessorRootClosure.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelProofCompilation.

(** ------------------------------------------------------------------
    The exact successor rows linked to a cross-level trace. *)

(** Every parameter below belongs to the same successor witness.  In
    particular, the row-code equalities are accompanied by the numeral,
    domain-substitution, and lower-application traces which generated them. *)
Definition RawDynamicTruthNativeCrossLevelLinkedRowsAt
    (M : RawPAModel) (tail : nat -> M)
    (predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
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
        (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
      sigmaDomain /\
    RawCodedFormulaSingleSubstitution M currentLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalPiInputDomainTemplate))
      piDomain /\
    RawDynamicTruthLocalTernaryApplication M
      currentGlobalSigma currentSigma /\
    RawDynamicTruthLocalTernaryApplication M
      currentGlobalPi currentPi /\
    RawDynamicTruthLocalTernaryApplication M
      nextGlobalSigma nextSigma /\
    RawDynamicTruthLocalTernaryApplication M
      nextGlobalPi nextPi.

Arguments RawDynamicTruthNativeCrossLevelLinkedRowsAt
  M tail predecessorLevel currentGlobalSigma currentGlobalPi
  sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
  sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
  : clear implicits.

(** Destructing the paired successor is enough to expose the synchronized
    row parameters; no choice operation selects a second successor. *)
Theorem raw_dynamicTruthNativeCrossLevelProofTraceAt_exposes_linked_rows :
    forall (M : RawPAModel) (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi,
  RawDynamicTruthNativeCrossLevelProofTraceAt M tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    currentSigma currentPi nextSigma nextPi ->
  exists sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication : M,
    RawDynamicTruthNativeCrossLevelLinkedRowsAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      currentSigma currentPi nextSigma nextPi
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication.
Proof.
  intros M tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
    (horbit & currentLevel & nextGlobalSigma & nextGlobalPi &
      currentLevelNumeral & hlevel & hsuccessor & hlevelNumeral &
      hsigmaDomain & hpiDomain & hcurrentSigma & hcurrentPi &
      hnextSigma & hnextPi).
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
  split; [exact hpiDomain |].
  split; [exact hcurrentSigma |].
  split; [exact hcurrentPi |].
  split; [exact hnextSigma | exact hnextPi].
Qed.

(** Conversely the linked relation reconstructs the original trace.  Thus
    making the local rows visible loses no information. *)
Theorem raw_dynamicTruthNativeCrossLevelProofTraceAt_of_linked_rows :
    forall (M : RawPAModel) (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthNativeCrossLevelLinkedRowsAt M tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    currentSigma currentPi nextSigma nextPi
    sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthNativeCrossLevelProofTraceAt M tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    currentSigma currentPi nextSigma nextPi.
Proof.
  intros M tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
    (currentLevel & nextGlobalSigma & nextGlobalPi & currentLevelNumeral &
      localSigmaRow & localPiRow & sigmaNumeral & piNumeral &
      horbit & hlevel & hsigmaNumeral & hsigmaDomain & hlowerPi &
      hsigmaRow & hpiNumeral & hpiDomain & hlowerSigma & hpiRow &
      hwrapper & hlevelNumeral & hinputSigmaDomain & hinputPiDomain &
      hcurrentSigma & hcurrentPi & hnextSigma & hnextPi).
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

Corollary raw_dynamicTruthNativeCrossLevelProofTraceAt_linked_rows_iff :
    forall (M : RawPAModel) (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi,
  RawDynamicTruthNativeCrossLevelProofTraceAt M tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    currentSigma currentPi nextSigma nextPi <->
  exists sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication : M,
    RawDynamicTruthNativeCrossLevelLinkedRowsAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      currentSigma currentPi nextSigma nextPi
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication.
Proof.
  intros. split.
  - apply raw_dynamicTruthNativeCrossLevelProofTraceAt_exposes_linked_rows.
  - intros (sigmaRowDomain & piRowDomain & lowerPi & lowerSigma & hlinked).
    exact (raw_dynamicTruthNativeCrossLevelProofTraceAt_of_linked_rows
      M tail predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      sigmaRowDomain piRowDomain lowerPi lowerSigma hlinked).
Qed.

(** ------------------------------------------------------------------
    Atomic adequacy carried by the exact trace. *)

(** The last checked substitution of the fixed ternary application already
    certifies atomic adequacy of its output. *)
Lemma raw_dynamicTruthLocalTernaryApplication_target_atomically_adequate :
    forall (M : RawPAModel), RawPASatisfies M -> forall input output,
  RawDynamicTruthLocalTernaryApplication M input output ->
  RawCodedFormulaAtomicallyAdequate M output.
Proof.
  intros M hPA input output
    (first & second & _ & _ & hthird).
  exact (raw_fixedReplacement_substitution_target_atomically_adequate
    M hPA dynamicTruthLocalApplicationThirdReplacement
    second output hthird).
Qed.

Lemma raw_dynamicTruthLocalAdmissibleCode_atomically_adequate :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall sigmaDomain piDomain,
  RawCodedFormulaAtomicallyAdequate M sigmaDomain ->
  RawCodedFormulaAtomicallyAdequate M piDomain ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain).
Proof.
  intros M hPA sigmaDomain piDomain hsigma hpi.
  unfold rawDynamicTruthLocalAdmissibleCode.
  apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
  - exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
      (codedFormulaAtomicallyAdequateTermAt (tVar 2))).
  - apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
    + exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
        (codedAssignmentDefinedThroughTermAt
          (tVar 1) (tVar 0) (tVar 2))).
    + exact (raw_formulaOrCode_atomically_adequate
        M hPA sigmaDomain piDomain hsigma hpi).
Qed.

Record RawDynamicTruthNativeCrossLevelTraceAdequacyAt
    (M : RawPAModel)
    (currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi : M)
    : Prop := {
  rawDynamicTruthNativeCrossLevel_currentGlobalSigma_adequate :
    RawCodedFormulaAtomicallyAdequate M currentGlobalSigma;
  rawDynamicTruthNativeCrossLevel_currentGlobalPi_adequate :
    RawCodedFormulaAtomicallyAdequate M currentGlobalPi;
  rawDynamicTruthNativeCrossLevel_nextGlobalSigma_adequate :
    RawCodedFormulaAtomicallyAdequate M nextGlobalSigma;
  rawDynamicTruthNativeCrossLevel_nextGlobalPi_adequate :
    RawCodedFormulaAtomicallyAdequate M nextGlobalPi;
  rawDynamicTruthNativeCrossLevel_sigmaDomain_adequate :
    RawCodedFormulaAtomicallyAdequate M sigmaDomain;
  rawDynamicTruthNativeCrossLevel_piDomain_adequate :
    RawCodedFormulaAtomicallyAdequate M piDomain;
  rawDynamicTruthNativeCrossLevel_currentSigma_adequate :
    RawCodedFormulaAtomicallyAdequate M currentSigma;
  rawDynamicTruthNativeCrossLevel_currentPi_adequate :
    RawCodedFormulaAtomicallyAdequate M currentPi;
  rawDynamicTruthNativeCrossLevel_nextSigma_adequate :
    RawCodedFormulaAtomicallyAdequate M nextSigma;
  rawDynamicTruthNativeCrossLevel_nextPi_adequate :
    RawCodedFormulaAtomicallyAdequate M nextPi;
  rawDynamicTruthNativeCrossLevel_admissible_adequate :
    RawCodedFormulaAtomicallyAdequate M
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
}.

Arguments RawDynamicTruthNativeCrossLevelTraceAdequacyAt
  M currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi
  sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
  : clear implicits.

(** This theorem derives every adequacy fact from the synchronized linked
    edge.  In particular, next-global adequacy travels through the actual
    successor rows and their actual global wrapper. *)
Theorem raw_dynamicTruthNativeCrossLevelLinkedRowsAt_adequacy :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthNativeCrossLevelLinkedRowsAt M tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    currentSigma currentPi nextSigma nextPi
    sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication ->
  exists nextGlobalSigma nextGlobalPi : M,
    RawDynamicTruthNativeCrossLevelTraceAdequacyAt M
      currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi.
Proof.
  intros M hPA tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
    (currentLevel & nextGlobalSigma & nextGlobalPi & currentLevelNumeral &
      localSigmaRow & localPiRow & sigmaNumeral & piNumeral &
      horbit & hlevel & hsigmaNumeral & hsigmaRowDomain & hlowerPi &
      hsigmaRowCode & hpiNumeral & hpiRowDomain & hlowerSigma &
      hpiRowCode & hwrapper & hlevelNumeral & hsigmaDomain & hpiDomain &
      hcurrentSigma & hcurrentPi & hnextSigma & hnextPi).
  destruct (proj1
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M tail
      (raw_succ M predecessorLevel) currentGlobalSigma currentGlobalPi)
    horbit) as [_ [hcurrentGlobalSigma hcurrentGlobalPi]].
  assert (hrows : RawDynamicTruthPairedSuccessorRowAt M
      currentGlobalSigma currentGlobalPi currentLevel
      localSigmaRow localPiRow).
  {
    split.
    - exists sigmaNumeral, sigmaRowDomain, lowerPiApplication.
      repeat split; assumption.
    - exists piNumeral, piRowDomain, lowerSigmaApplication.
      repeat split; assumption.
  }
  destruct (rawDynamicTruthPairedSuccessorRowAt_atomically_adequate
    M hPA currentGlobalSigma currentGlobalPi currentLevel
    localSigmaRow localPiRow hrows) as [hlocalSigma hlocalPi].
  destruct (dynamicTruthPairedGlobalWrapperGraph_adequacy
    M hPA localSigmaRow localPiRow nextGlobalSigma nextGlobalPi
    hwrapper hlocalSigma hlocalPi) as
    [hnextGlobalSigma hnextGlobalPi].
  assert (hsigmaDomainAdequate :
      RawCodedFormulaAtomicallyAdequate M sigmaDomain).
  { exact (raw_dynamicTruthDomain_target_atomically_adequate
      M hPA currentLevel currentLevelNumeral
      (formulaCode dynamicTruthLocalSigmaInputDomainTemplate)
      sigmaDomain hlevelNumeral hsigmaDomain). }
  assert (hpiDomainAdequate :
      RawCodedFormulaAtomicallyAdequate M piDomain).
  { exact (raw_dynamicTruthDomain_target_atomically_adequate
      M hPA currentLevel currentLevelNumeral
      (formulaCode dynamicTruthLocalPiInputDomainTemplate)
      piDomain hlevelNumeral hpiDomain). }
  exists nextGlobalSigma, nextGlobalPi.
  refine
    {| rawDynamicTruthNativeCrossLevel_currentGlobalSigma_adequate :=
         hcurrentGlobalSigma;
       rawDynamicTruthNativeCrossLevel_currentGlobalPi_adequate :=
         hcurrentGlobalPi;
       rawDynamicTruthNativeCrossLevel_nextGlobalSigma_adequate :=
         hnextGlobalSigma;
       rawDynamicTruthNativeCrossLevel_nextGlobalPi_adequate :=
         hnextGlobalPi;
       rawDynamicTruthNativeCrossLevel_sigmaDomain_adequate :=
         hsigmaDomainAdequate;
       rawDynamicTruthNativeCrossLevel_piDomain_adequate :=
         hpiDomainAdequate;
       rawDynamicTruthNativeCrossLevel_currentSigma_adequate :=
         raw_dynamicTruthLocalTernaryApplication_target_atomically_adequate
           M hPA currentGlobalSigma currentSigma hcurrentSigma;
       rawDynamicTruthNativeCrossLevel_currentPi_adequate :=
         raw_dynamicTruthLocalTernaryApplication_target_atomically_adequate
           M hPA currentGlobalPi currentPi hcurrentPi;
       rawDynamicTruthNativeCrossLevel_nextSigma_adequate :=
         raw_dynamicTruthLocalTernaryApplication_target_atomically_adequate
           M hPA nextGlobalSigma nextSigma hnextSigma;
       rawDynamicTruthNativeCrossLevel_nextPi_adequate :=
         raw_dynamicTruthLocalTernaryApplication_target_atomically_adequate
           M hPA nextGlobalPi nextPi hnextPi;
       rawDynamicTruthNativeCrossLevel_admissible_adequate :=
         raw_dynamicTruthLocalAdmissibleCode_atomically_adequate
           M hPA sigmaDomain piDomain
           hsigmaDomainAdequate hpiDomainAdequate |}.
Qed.

(** A projection which hides the row and wrapper witnesses again, useful to
    clients that need only the six field-code adequacy facts. *)
Corollary raw_dynamicTruthNativeCrossLevelProofTraceAt_formula_adequacy :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi,
  RawDynamicTruthNativeCrossLevelProofTraceAt M tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    currentSigma currentPi nextSigma nextPi ->
  RawCodedFormulaAtomicallyAdequate M sigmaDomain /\
  RawCodedFormulaAtomicallyAdequate M piDomain /\
  RawCodedFormulaAtomicallyAdequate M currentSigma /\
  RawCodedFormulaAtomicallyAdequate M currentPi /\
  RawCodedFormulaAtomicallyAdequate M nextSigma /\
  RawCodedFormulaAtomicallyAdequate M nextPi /\
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain).
Proof.
  intros M hPA tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi htrace.
  destruct
    (raw_dynamicTruthNativeCrossLevelProofTraceAt_exposes_linked_rows
      M tail predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      htrace) as
    (sigmaRowDomain & piRowDomain & lowerPi & lowerSigma & hlinked).
  destruct (raw_dynamicTruthNativeCrossLevelLinkedRowsAt_adequacy
    M hPA tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
    sigmaRowDomain piRowDomain lowerPi lowerSigma hlinked) as
    (nextGlobalSigma & nextGlobalPi & hadequacy).
  repeat split.
  - exact (rawDynamicTruthNativeCrossLevel_sigmaDomain_adequate
      M currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      hadequacy).
  - exact (rawDynamicTruthNativeCrossLevel_piDomain_adequate
      M currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      hadequacy).
  - exact (rawDynamicTruthNativeCrossLevel_currentSigma_adequate
      M currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      hadequacy).
  - exact (rawDynamicTruthNativeCrossLevel_currentPi_adequate
      M currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      hadequacy).
  - exact (rawDynamicTruthNativeCrossLevel_nextSigma_adequate
      M currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      hadequacy).
  - exact (rawDynamicTruthNativeCrossLevel_nextPi_adequate
      M currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      hadequacy).
  - exact (rawDynamicTruthNativeCrossLevel_admissible_adequate
      M currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      hadequacy).
Qed.

(** ------------------------------------------------------------------
    Guard-root compilation over an arbitrary literal base context. *)

Definition rawDynamicTruthNativeCrossLevelAdmissibleContextOn
    (M : RawPAModel) (baseContext sigmaDomain piDomain : M) : M :=
  rawListNode M
    (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
    baseContext.

Definition rawDynamicTruthNativeCrossLevelDomainContextOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain domain : M) : M :=
  rawListNode M domain
    (rawDynamicTruthNativeCrossLevelAdmissibleContextOn M
      baseContext sigmaDomain piDomain).

Definition rawDynamicTruthNativeCrossLevelDirectionalContextOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain domain assumption : M) : M :=
  rawListNode M assumption
    (rawDynamicTruthNativeCrossLevelDomainContextOn M
      baseContext sigmaDomain piDomain domain).

Arguments rawDynamicTruthNativeCrossLevelAdmissibleContextOn
  M baseContext sigmaDomain piDomain : clear implicits.
Arguments rawDynamicTruthNativeCrossLevelDomainContextOn
  M baseContext sigmaDomain piDomain domain : clear implicits.
Arguments rawDynamicTruthNativeCrossLevelDirectionalContextOn
  M baseContext sigmaDomain piDomain domain assumption : clear implicits.

Definition RawDynamicTruthNativeCrossLevelGuardRootOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain domain current next : M) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeCrossLevelAdmissibleContextOn M
        baseContext sigmaDomain piDomain)
      (rawDynamicTruthNativeCrossLevelGuardedEquivalenceCode M
        domain current next) root.

Definition RawDynamicTruthNativeCrossLevelDirectionalRootsOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain domain current next : M) : Prop :=
  exists currentToNextRoot nextToCurrentRoot : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeCrossLevelDirectionalContextOn M
        baseContext sigmaDomain piDomain domain current)
      next currentToNextRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeCrossLevelDirectionalContextOn M
        baseContext sigmaDomain piDomain domain next)
      current nextToCurrentRoot.

Arguments RawDynamicTruthNativeCrossLevelGuardRootOn
  M baseContext sigmaDomain piDomain domain current next : clear implicits.
Arguments RawDynamicTruthNativeCrossLevelDirectionalRootsOn
  M baseContext sigmaDomain piDomain domain current next : clear implicits.

(** The complete structural compiler.  It first applies the guarded theorem
    to the domain assumption, projects the two implication directions, then
    applies each implication to its freshly inserted evidence assumption. *)
Theorem raw_dynamicTruthNativeCrossLevelDirectionalRootsOn_of_guard_root :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall baseContext sigmaDomain piDomain domain current next,
  RawContextListRealizable M baseContext ->
  RawCodedFormulaAtomicallyAdequate M domain ->
  RawCodedFormulaAtomicallyAdequate M current ->
  RawCodedFormulaAtomicallyAdequate M next ->
  RawDynamicTruthNativeCrossLevelGuardRootOn M
    baseContext sigmaDomain piDomain domain current next ->
  RawDynamicTruthNativeCrossLevelDirectionalRootsOn M
    baseContext sigmaDomain piDomain domain current next.
Proof.
  intros M hPA baseContext sigmaDomain piDomain domain current next
    hbase hdomain hcurrent hnext (guardRoot & hguard).
  set (admissibleContext :=
    rawDynamicTruthNativeCrossLevelAdmissibleContextOn M
      baseContext sigmaDomain piDomain).
  set (domainContext :=
    rawDynamicTruthNativeCrossLevelDomainContextOn M
      baseContext sigmaDomain piDomain domain).
  set (pairCode := rawFormulaAndCode M
    (rawFormulaImpCode M current next)
    (rawFormulaImpCode M next current)).
  assert (hadmissibleContext :
      RawContextListRealizable M admissibleContext).
  { unfold admissibleContext,
      rawDynamicTruthNativeCrossLevelAdmissibleContextOn.
    exact (raw_contextList_cons_realizable M hPA baseContext
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain) hbase). }
  assert (hdomainContext : RawContextListRealizable M domainContext).
  { unfold domainContext,
      rawDynamicTruthNativeCrossLevelDomainContextOn.
    exact (raw_contextList_cons_realizable M hPA admissibleContext
      domain hadmissibleContext). }
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA admissibleContext domain
    (rawDynamicTruthNativeCrossLevelGuardedEquivalenceCode M
      domain current next) guardRoot
    hdomain hadmissibleContext hguard) as
    [guardAtDomain hguardAtDomain].
  pose proof (raw_codedPALocalProofOf_assumption
    M hPA admissibleContext domain hadmissibleContext) as hdomainRoot.
  pose proof (raw_codedPALocalProofOf_impE M hPA
    domainContext domain pairCode guardAtDomain
    (rawProofAssumptionRoot M domainContext domain)
    hguardAtDomain hdomainRoot) as hpair.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA domainContext
    (rawFormulaImpCode M current next)
    (rawFormulaImpCode M next current)
    (rawProofImpERoot M domainContext domain pairCode
      guardAtDomain (rawProofAssumptionRoot M domainContext domain))
    hpair) as hforwardImp.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA domainContext
    (rawFormulaImpCode M current next)
    (rawFormulaImpCode M next current)
    (rawProofImpERoot M domainContext domain pairCode
      guardAtDomain (rawProofAssumptionRoot M domainContext domain))
    hpair) as hbackwardImp.
  set (forwardImpRoot := rawProofAndERoot M RawAndLeft domainContext
    (rawFormulaImpCode M current next)
    (rawFormulaImpCode M next current)
    (rawProofImpERoot M domainContext domain pairCode
      guardAtDomain (rawProofAssumptionRoot M domainContext domain))).
  set (backwardImpRoot := rawProofAndERoot M RawAndRight domainContext
    (rawFormulaImpCode M current next)
    (rawFormulaImpCode M next current)
    (rawProofImpERoot M domainContext domain pairCode
      guardAtDomain (rawProofAssumptionRoot M domainContext domain))).
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA domainContext current (rawFormulaImpCode M current next)
    forwardImpRoot hcurrent hdomainContext hforwardImp) as
    [forwardImpAtAssumption hforwardImpAtAssumption].
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA domainContext next (rawFormulaImpCode M next current)
    backwardImpRoot hnext hdomainContext hbackwardImp) as
    [backwardImpAtAssumption hbackwardImpAtAssumption].
  pose proof (raw_codedPALocalProofOf_assumption
    M hPA domainContext current hdomainContext) as hcurrentRoot.
  pose proof (raw_codedPALocalProofOf_assumption
    M hPA domainContext next hdomainContext) as hnextRoot.
  exists
    (rawProofImpERoot M
      (rawDynamicTruthNativeCrossLevelDirectionalContextOn M
        baseContext sigmaDomain piDomain domain current)
      current next forwardImpAtAssumption
      (rawProofAssumptionRoot M
        (rawDynamicTruthNativeCrossLevelDirectionalContextOn M
          baseContext sigmaDomain piDomain domain current) current)),
    (rawProofImpERoot M
      (rawDynamicTruthNativeCrossLevelDirectionalContextOn M
        baseContext sigmaDomain piDomain domain next)
      next current backwardImpAtAssumption
      (rawProofAssumptionRoot M
        (rawDynamicTruthNativeCrossLevelDirectionalContextOn M
          baseContext sigmaDomain piDomain domain next) next)).
  split.
  - exact (raw_codedPALocalProofOf_impE M hPA
      (rawDynamicTruthNativeCrossLevelDirectionalContextOn M
        baseContext sigmaDomain piDomain domain current)
      current next forwardImpAtAssumption
      (rawProofAssumptionRoot M
        (rawDynamicTruthNativeCrossLevelDirectionalContextOn M
          baseContext sigmaDomain piDomain domain current) current)
      hforwardImpAtAssumption hcurrentRoot).
  - exact (raw_codedPALocalProofOf_impE M hPA
      (rawDynamicTruthNativeCrossLevelDirectionalContextOn M
        baseContext sigmaDomain piDomain domain next)
      next current backwardImpAtAssumption
      (rawProofAssumptionRoot M
        (rawDynamicTruthNativeCrossLevelDirectionalContextOn M
          baseContext sigmaDomain piDomain domain next) next)
      hbackwardImpAtAssumption hnextRoot).
Qed.

(** Polarity-specific names make the final compiler signature match the
    two packages used by the original cross-level shell. *)
Definition RawDynamicTruthNativeCrossLevelSigmaGuardRootOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain currentSigma nextSigma : M) : Prop :=
  RawDynamicTruthNativeCrossLevelGuardRootOn M baseContext
    sigmaDomain piDomain sigmaDomain currentSigma nextSigma.

Definition RawDynamicTruthNativeCrossLevelPiGuardRootOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain currentPi nextPi : M) : Prop :=
  RawDynamicTruthNativeCrossLevelGuardRootOn M baseContext
    sigmaDomain piDomain piDomain currentPi nextPi.

Definition RawDynamicTruthNativeCrossLevelSigmaLocalRootsOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain currentSigma nextSigma : M) : Prop :=
  RawDynamicTruthNativeCrossLevelDirectionalRootsOn M baseContext
    sigmaDomain piDomain sigmaDomain currentSigma nextSigma.

Definition RawDynamicTruthNativeCrossLevelPiLocalRootsOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain currentPi nextPi : M) : Prop :=
  RawDynamicTruthNativeCrossLevelDirectionalRootsOn M baseContext
    sigmaDomain piDomain piDomain currentPi nextPi.

Arguments RawDynamicTruthNativeCrossLevelSigmaGuardRootOn
  M baseContext sigmaDomain piDomain currentSigma nextSigma
  : clear implicits.
Arguments RawDynamicTruthNativeCrossLevelPiGuardRootOn
  M baseContext sigmaDomain piDomain currentPi nextPi
  : clear implicits.
Arguments RawDynamicTruthNativeCrossLevelSigmaLocalRootsOn
  M baseContext sigmaDomain piDomain currentSigma nextSigma
  : clear implicits.
Arguments RawDynamicTruthNativeCrossLevelPiLocalRootsOn
  M baseContext sigmaDomain piDomain currentPi nextPi
  : clear implicits.

Corollary raw_dynamicTruthNativeCrossLevelSigmaLocalRootsOn_of_guard_root :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall baseContext sigmaDomain piDomain currentSigma nextSigma,
  RawContextListRealizable M baseContext ->
  RawCodedFormulaAtomicallyAdequate M sigmaDomain ->
  RawCodedFormulaAtomicallyAdequate M currentSigma ->
  RawCodedFormulaAtomicallyAdequate M nextSigma ->
  RawDynamicTruthNativeCrossLevelSigmaGuardRootOn M baseContext
    sigmaDomain piDomain currentSigma nextSigma ->
  RawDynamicTruthNativeCrossLevelSigmaLocalRootsOn M baseContext
    sigmaDomain piDomain currentSigma nextSigma.
Proof.
  intros. exact
    (raw_dynamicTruthNativeCrossLevelDirectionalRootsOn_of_guard_root
      M H baseContext sigmaDomain piDomain sigmaDomain
      currentSigma nextSigma H0 H1 H2 H3 H4).
Qed.

Corollary raw_dynamicTruthNativeCrossLevelPiLocalRootsOn_of_guard_root :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall baseContext sigmaDomain piDomain currentPi nextPi,
  RawContextListRealizable M baseContext ->
  RawCodedFormulaAtomicallyAdequate M piDomain ->
  RawCodedFormulaAtomicallyAdequate M currentPi ->
  RawCodedFormulaAtomicallyAdequate M nextPi ->
  RawDynamicTruthNativeCrossLevelPiGuardRootOn M baseContext
    sigmaDomain piDomain currentPi nextPi ->
  RawDynamicTruthNativeCrossLevelPiLocalRootsOn M baseContext
    sigmaDomain piDomain currentPi nextPi.
Proof.
  intros. exact
    (raw_dynamicTruthNativeCrossLevelDirectionalRootsOn_of_guard_root
      M H baseContext sigmaDomain piDomain piDomain
      currentPi nextPi H0 H1 H2 H3 H4).
Qed.

(** At the literal empty base, the generalized contexts reduce
    definitionally to the contexts of the original proof shell. *)
Lemma raw_dynamicTruthNativeCrossLevelSigmaLocalRootsAt_of_empty_base :
    forall (M : RawPAModel) sigmaDomain piDomain currentSigma nextSigma,
  RawDynamicTruthNativeCrossLevelSigmaLocalRootsOn M (raw_zero M)
    sigmaDomain piDomain currentSigma nextSigma ->
  RawDynamicTruthNativeCrossLevelSigmaLocalRootsAt M
    sigmaDomain piDomain currentSigma nextSigma.
Proof.
  intros M sigmaDomain piDomain currentSigma nextSigma hroots.
  exact hroots.
Qed.

Lemma raw_dynamicTruthNativeCrossLevelPiLocalRootsAt_of_empty_base :
    forall (M : RawPAModel) sigmaDomain piDomain currentPi nextPi,
  RawDynamicTruthNativeCrossLevelPiLocalRootsOn M (raw_zero M)
    sigmaDomain piDomain currentPi nextPi ->
  RawDynamicTruthNativeCrossLevelPiLocalRootsAt M
    sigmaDomain piDomain currentPi nextPi.
Proof.
  intros M sigmaDomain piDomain currentPi nextPi hroots.
  exact hroots.
Qed.

(** ------------------------------------------------------------------
    The exact remaining trace-linked root interface. *)

(** The successor rows are exposed existentially and returned together with
    the two guarded roots.  This prevents an implementation from proving a
    root for row parameters unrelated to the supplied trace. *)
Definition
    RawDynamicTruthNativeCrossLevelLinkedGuardRootInterfaceAtEmptyBase
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi,
    RawDynamicTruthNativeCrossLevelProofTraceAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      currentSigma currentPi nextSigma nextPi ->
    exists sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication : M,
      RawDynamicTruthNativeCrossLevelLinkedRowsAt M tail predecessorLevel
        currentGlobalSigma currentGlobalPi sigmaDomain piDomain
        currentSigma currentPi nextSigma nextPi
        sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication /\
      RawDynamicTruthNativeCrossLevelSigmaGuardRootOn M (raw_zero M)
        sigmaDomain piDomain currentSigma nextSigma /\
      RawDynamicTruthNativeCrossLevelPiGuardRootOn M (raw_zero M)
        sigmaDomain piDomain currentPi nextPi.

Arguments
  RawDynamicTruthNativeCrossLevelLinkedGuardRootInterfaceAtEmptyBase M
  : clear implicits.

(** A pointwise implementation may consume the concrete linked rows.  This
    adapter performs the existential selection once, from the original
    successor witness. *)
Definition RawDynamicTruthNativeCrossLevelLinkedGuardRootCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication,
    RawDynamicTruthNativeCrossLevelLinkedRowsAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      currentSigma currentPi nextSigma nextPi
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication ->
    RawDynamicTruthNativeCrossLevelSigmaGuardRootOn M (raw_zero M)
      sigmaDomain piDomain currentSigma nextSigma /\
    RawDynamicTruthNativeCrossLevelPiGuardRootOn M (raw_zero M)
      sigmaDomain piDomain currentPi nextPi.

Arguments RawDynamicTruthNativeCrossLevelLinkedGuardRootCompiler M
  : clear implicits.

Theorem
    raw_dynamicTruthNativeCrossLevelLinkedGuardRootInterface_of_compiler :
    forall (M : RawPAModel),
  RawDynamicTruthNativeCrossLevelLinkedGuardRootCompiler M ->
  RawDynamicTruthNativeCrossLevelLinkedGuardRootInterfaceAtEmptyBase M.
Proof.
  intros M hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    currentSigma currentPi nextSigma nextPi htrace.
  destruct
    (raw_dynamicTruthNativeCrossLevelProofTraceAt_exposes_linked_rows
      M tail predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      htrace) as
    (sigmaRowDomain & piRowDomain & lowerPi & lowerSigma & hlinked).
  exists sigmaRowDomain, piRowDomain, lowerPi, lowerSigma.
  split; [exact hlinked |].
  exact (hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    currentSigma currentPi nextSigma nextPi
    sigmaRowDomain piRowDomain lowerPi lowerSigma hlinked).
Qed.

(** This closes the original four-leaf compiler from precisely two
    trace-linked guarded roots.  All other work in the proof is structural. *)
Theorem raw_dynamicTruthNativeCrossLevelLocalRootCompiler_of_linked_guards :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeCrossLevelLinkedGuardRootInterfaceAtEmptyBase M ->
  RawDynamicTruthNativeCrossLevelLocalRootCompiler M.
Proof.
  intros M hPA hguards tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    currentSigma currentPi nextSigma nextPi htrace.
  destruct (hguards tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    currentSigma currentPi nextSigma nextPi htrace) as
    (sigmaRowDomain & piRowDomain & lowerPi & lowerSigma &
      hlinked & hsigmaGuard & hpiGuard).
  destruct (raw_dynamicTruthNativeCrossLevelLinkedRowsAt_adequacy
    M hPA tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
    sigmaRowDomain piRowDomain lowerPi lowerSigma hlinked) as
    (nextGlobalSigma & nextGlobalPi & hadequacy).
  pose proof (raw_contextList_empty_realizable M hPA) as hempty.
  split.
  - apply raw_dynamicTruthNativeCrossLevelSigmaLocalRootsAt_of_empty_base.
    exact (raw_dynamicTruthNativeCrossLevelSigmaLocalRootsOn_of_guard_root
      M hPA (raw_zero M) sigmaDomain piDomain currentSigma nextSigma
      hempty
      (rawDynamicTruthNativeCrossLevel_sigmaDomain_adequate
        M currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi
        sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
        hadequacy)
      (rawDynamicTruthNativeCrossLevel_currentSigma_adequate
        M currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi
        sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
        hadequacy)
      (rawDynamicTruthNativeCrossLevel_nextSigma_adequate
        M currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi
        sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
        hadequacy)
      hsigmaGuard).
  - apply raw_dynamicTruthNativeCrossLevelPiLocalRootsAt_of_empty_base.
    exact (raw_dynamicTruthNativeCrossLevelPiLocalRootsOn_of_guard_root
      M hPA (raw_zero M) sigmaDomain piDomain currentPi nextPi
      hempty
      (rawDynamicTruthNativeCrossLevel_piDomain_adequate
        M currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi
        sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
        hadequacy)
      (rawDynamicTruthNativeCrossLevel_currentPi_adequate
        M currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi
        sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
        hadequacy)
      (rawDynamicTruthNativeCrossLevel_nextPi_adequate
        M currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi
        sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
        hadequacy)
      hpiGuard).
Qed.

Corollary
    raw_dynamicTruthNativeCrossLevelLocalRootCompiler_of_linked_compiler :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeCrossLevelLinkedGuardRootCompiler M ->
  RawDynamicTruthNativeCrossLevelLocalRootCompiler M.
Proof.
  intros M hPA hcompiler.
  exact
    (raw_dynamicTruthNativeCrossLevelLocalRootCompiler_of_linked_guards
      M hPA
      (raw_dynamicTruthNativeCrossLevelLinkedGuardRootInterface_of_compiler
        M hcompiler)).
Qed.

End PABoundedRawCodedDynamicTruthNativeCrossLevelLeafRootCompilation.
