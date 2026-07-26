(**
  The carrier-indexed positive formula-substitution-invariance field.

  At predecessor [p], the positive master coordinate is the closed native
  formula-substitution Tarski law for the current truth level [S p].  The graph
  selects the genuine paired global Sigma/Pi formula codes from the orbit at
  [S p], applies them to the source and target formula/assignment triples,
  instantiates the current-level source domains, retains the represented
  formula-substitution and assignment-substitution relations literally, and builds the
  exact seven-variable universal closure used by the fixed-level field.

  All exact graph semantics is law free.  PA is used only for syntax
  totality, orbit adequacy, and represented proofs of externally fixed
  standard instances.  No semantic-validity-to-proof inference occurs; the
  remaining arbitrary-carrier proof compiler is isolated at the end.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPAProvability
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedAssignment
  RawCodedFormulaOperations
  RawCodedNumeralTermCode
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthOperationTransport
  RawCodedFixedLevelTruthOperationTarskiPositive
  RawCodedDynamicTruthTernaryApplicationTotality
  RawCodedTermOpeningAfterShiftSyntaxStability
  RawCodedDynamicTruthPairedSuccessorAdequacy
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeSubstitutionCarrier
  RawCodedOutputFirstPairedFormulaGraphComposition.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthNativeSubstitutionPositiveGraph.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPAProvability.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthOperationTransport.
Import PABoundedRawCodedFixedLevelTruthOperationTarskiPositive.
Import PABoundedRawCodedDynamicTruthTernaryApplicationTotality.
Import PABoundedRawCodedTermOpeningAfterShiftSyntaxStability.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionCarrier.
Import PABoundedRawCodedOutputFirstPairedFormulaGraphComposition.

(** ------------------------------------------------------------------
    Represented applications in the seven-variable substitution layout.

    Sequential one-variable substitution must account for each newly opened
    existential binder.  To obtain the source application [#1,#3,#4], its
    literal replacement terms are therefore [#3,#4,#4].  Likewise the
    target application [#2,#5,#6] uses [#4,#6,#6].  Keeping these six terms
    named makes the de Bruijn adjustment visible at the graph boundary. *)

Definition dynamicTruthNativeSubstitutionSourceFirstReplacement : term := tVar 3.
Definition dynamicTruthNativeSubstitutionSourceSecondReplacement : term := tVar 4.
Definition dynamicTruthNativeSubstitutionSourceThirdReplacement : term := tVar 4.

Definition dynamicTruthNativeSubstitutionTargetFirstReplacement : term := tVar 4.
Definition dynamicTruthNativeSubstitutionTargetSecondReplacement : term := tVar 6.
Definition dynamicTruthNativeSubstitutionTargetThirdReplacement : term := tVar 6.

Definition dynamicTruthNativeSubstitutionApplicationTermAt
    (firstReplacement secondReplacement thirdReplacement : term)
    (input output : term) : formula :=
  pEx (pEx
    (pAnd
      (codedFormulaSingleSubstitutionTermAt
        (Term.numeral (termCode firstReplacement))
        (liftTerm 2 input) (tVar 1))
      (pAnd
        (codedFormulaSingleSubstitutionTermAt
          (Term.numeral (termCode secondReplacement))
          (tVar 1) (tVar 0))
        (codedFormulaSingleSubstitutionTermAt
          (Term.numeral (termCode thirdReplacement))
          (tVar 0) (liftTerm 2 output))))).

Definition RawDynamicTruthNativeSubstitutionApplication (M : RawPAModel)
    (firstReplacement secondReplacement thirdReplacement : term)
    (input output : M) : Prop :=
  exists firstResult secondResult : M,
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M (termCode firstReplacement))
      input firstResult /\
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M (termCode secondReplacement))
      firstResult secondResult /\
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M (termCode thirdReplacement))
      secondResult output.

Arguments RawDynamicTruthNativeSubstitutionApplication
  M firstReplacement secondReplacement thirdReplacement input output
  : clear implicits.

Theorem raw_sat_dynamicTruthNativeSubstitutionApplicationTermAt_iff : forall
    (M : RawPAModel) e firstReplacement secondReplacement thirdReplacement
      input output,
  raw_formula_sat M e
    (dynamicTruthNativeSubstitutionApplicationTermAt
      firstReplacement secondReplacement thirdReplacement input output) <->
  RawDynamicTruthNativeSubstitutionApplication M
    firstReplacement secondReplacement thirdReplacement
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros.
  unfold dynamicTruthNativeSubstitutionApplicationTermAt,
    RawDynamicTruthNativeSubstitutionApplication.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_codedFormulaSingleSubstitutionTermAt_iff.
  repeat setoid_rewrite raw_term_eval_numeral.
  repeat setoid_rewrite raw_fixedLevel_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_dynamicTruthNativeSubstitutionApplication_exists_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      firstReplacement secondReplacement thirdReplacement input,
  RawCodedFormulaAtomicallyAdequate M input ->
  exists output,
    RawDynamicTruthNativeSubstitutionApplication M
      firstReplacement secondReplacement thirdReplacement input output /\
    RawCodedFormulaAtomicallyAdequate M output.
Proof.
  intros M hPA firstReplacement secondReplacement thirdReplacement
    input hinput.
  destruct (raw_codedFormulaSingleSubstitution_three_exists_total M hPA
    input hinput
    (rawNumeralValue M (termCode firstReplacement))
    (raw_zero M) (raw_zero M)
    (raw_dynamicTruthApplication_fixedReplacement_syntax M hPA
      firstReplacement)
    (rawNumeralValue M (termCode secondReplacement))
    (raw_zero M) (raw_zero M)
    (raw_dynamicTruthApplication_fixedReplacement_syntax M hPA
      secondReplacement)
    (rawNumeralValue M (termCode thirdReplacement))
    (raw_zero M) (raw_zero M)
    (raw_dynamicTruthApplication_fixedReplacement_syntax M hPA
      thirdReplacement)) as
    (firstResult & secondResult & output & hfirst & _hfirstAdequate &
     hsecond & _hsecondAdequate & hthird & houtputAdequate).
  exists output. split; [|exact houtputAdequate].
  exists firstResult, secondResult. repeat split; assumption.
Qed.

(** The carrier module already proves the exact standard-level quotation and
    object-proof facts.  These transparent aliases deliberately re-export
    them from the positive-graph surface: the graph's predecessor [p] is
    aligned with truth level [S p], and the represented proof is a genuine
    PA proof of that literal seven-variable closure. *)
Definition
    rawDynamicTruthNativeSubstitutionPositiveFieldCode_standard_alignment :=
  rawDynamicTruthNativeSubstitutionFieldCode_quoted_successor_level.

Definition
    rawDynamicTruthNativeSubstitutionPositiveFieldCode_standard_proof :=
  rawDynamicTruthNativeSubstitutionFieldCode_standard_proof.

(** ------------------------------------------------------------------
    The genuine paired orbit at current level [S p]. *)

Definition dynamicTruthNativeSubstitutionInputOrbitGraph : formula :=
  dynamicTruthNativeLocalInputOrbitGraph.

Definition RawDynamicTruthNativeSubstitutionInputOrbitAt
    (M : RawPAModel) (tail : nat -> M)
    (predecessorLevel globalSigma globalPi : M) : Prop :=
  RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
    tail (raw_succ M predecessorLevel) globalSigma globalPi.

Arguments RawDynamicTruthNativeSubstitutionInputOrbitAt
  M tail predecessorLevel globalSigma globalPi : clear implicits.

Theorem raw_sat_dynamicTruthNativeSubstitutionInputOrbitGraph_iff : forall
    (M : RawPAModel) tail predecessorLevel globalSigma globalPi,
  raw_formula_sat M
    (scons M globalSigma (scons M globalPi
      (scons M predecessorLevel tail)))
    dynamicTruthNativeSubstitutionInputOrbitGraph <->
  RawDynamicTruthNativeSubstitutionInputOrbitAt M
    tail predecessorLevel globalSigma globalPi.
Proof.
  intros.
  unfold dynamicTruthNativeSubstitutionInputOrbitGraph,
    RawDynamicTruthNativeSubstitutionInputOrbitAt.
  exact (raw_sat_dynamicTruthNativeLocalInputOrbitGraph_iff
    M tail predecessorLevel globalSigma globalPi).
Qed.

Corollary raw_sat_dynamicTruthNativeSubstitutionInputOrbitGraph_standard_iff : forall
    (M : RawPAModel) tail predecessor globalSigma globalPi,
  raw_formula_sat M
    (scons M globalSigma (scons M globalPi
      (scons M (rawNumeralValue M predecessor) tail)))
    dynamicTruthNativeSubstitutionInputOrbitGraph <->
  RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
    tail (rawNumeralValue M (S predecessor)) globalSigma globalPi.
Proof.
  intros.
  unfold dynamicTruthNativeSubstitutionInputOrbitGraph.
  exact (raw_sat_dynamicTruthNativeLocalInputOrbitGraph_standard_iff
    M tail predecessor globalSigma globalPi).
Qed.

(** ------------------------------------------------------------------
    Transform the current orbit pair into the substitution field.

    Beneath the eight witnesses the environment is

      targetPi :: sourcePi :: targetSigma :: sourceSigma ::
      piDomain :: sigmaDomain :: currentLevelNumeral :: currentLevel ::
      fieldCode :: currentGlobalSigma :: currentGlobalPi ::
      predecessorLevel :: tail. *)

Definition dynamicTruthNativeSubstitutionAnd8
    (a b c d e f g h : formula) : formula :=
  pAnd a (pAnd b (pAnd c (pAnd d (pAnd e (pAnd f (pAnd g h)))))).

Definition dynamicTruthNativeSubstitutionFieldTransformGraph : formula :=
  fixedLevelEx8
    (pAnd
      (pEq (tVar 7) (tSucc (tVar 11)))
      (dynamicTruthNativeSubstitutionAnd8
        (numeralTermCodeAtTermAt (tVar 7) (tVar 6))
        (codedFormulaSingleSubstitutionTermAt
          (tVar 6)
          (Term.numeral
            (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
          (tVar 5))
        (codedFormulaSingleSubstitutionTermAt
          (tVar 6)
          (Term.numeral
            (formulaCode dynamicTruthLocalPiInputDomainTemplate))
          (tVar 4))
        (dynamicTruthNativeSubstitutionApplicationTermAt
          dynamicTruthNativeSubstitutionSourceFirstReplacement
          dynamicTruthNativeSubstitutionSourceSecondReplacement
          dynamicTruthNativeSubstitutionSourceThirdReplacement
          (tVar 9) (tVar 3))
        (dynamicTruthNativeSubstitutionApplicationTermAt
          dynamicTruthNativeSubstitutionTargetFirstReplacement
          dynamicTruthNativeSubstitutionTargetSecondReplacement
          dynamicTruthNativeSubstitutionTargetThirdReplacement
          (tVar 9) (tVar 2))
        (dynamicTruthNativeSubstitutionApplicationTermAt
          dynamicTruthNativeSubstitutionSourceFirstReplacement
          dynamicTruthNativeSubstitutionSourceSecondReplacement
          dynamicTruthNativeSubstitutionSourceThirdReplacement
          (tVar 10) (tVar 1))
        (dynamicTruthNativeSubstitutionApplicationTermAt
          dynamicTruthNativeSubstitutionTargetFirstReplacement
          dynamicTruthNativeSubstitutionTargetSecondReplacement
          dynamicTruthNativeSubstitutionTargetThirdReplacement
          (tVar 10) (tVar 0))
        (dynamicTruthNativeSubstitutionFieldCodeTermAt
          (tVar 8) (tVar 5) (tVar 4) (tVar 3) (tVar 2)
          (tVar 1) (tVar 0)))).

Definition RawDynamicTruthNativeSubstitutionFieldTransformAt
    (M : RawPAModel)
    (currentGlobalSigma currentGlobalPi predecessorLevel fieldCode : M)
    : Prop :=
  exists currentLevel currentLevelNumeral sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi : M,
    currentLevel = raw_succ M predecessorLevel /\
    RawNumeralTermCodeAt M currentLevel currentLevelNumeral /\
    RawCodedFormulaSingleSubstitution M currentLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
      sigmaDomain /\
    RawCodedFormulaSingleSubstitution M currentLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalPiInputDomainTemplate))
      piDomain /\
    RawDynamicTruthNativeSubstitutionApplication M
      dynamicTruthNativeSubstitutionSourceFirstReplacement
      dynamicTruthNativeSubstitutionSourceSecondReplacement
      dynamicTruthNativeSubstitutionSourceThirdReplacement
      currentGlobalSigma sourceSigma /\
    RawDynamicTruthNativeSubstitutionApplication M
      dynamicTruthNativeSubstitutionTargetFirstReplacement
      dynamicTruthNativeSubstitutionTargetSecondReplacement
      dynamicTruthNativeSubstitutionTargetThirdReplacement
      currentGlobalSigma targetSigma /\
    RawDynamicTruthNativeSubstitutionApplication M
      dynamicTruthNativeSubstitutionSourceFirstReplacement
      dynamicTruthNativeSubstitutionSourceSecondReplacement
      dynamicTruthNativeSubstitutionSourceThirdReplacement
      currentGlobalPi sourcePi /\
    RawDynamicTruthNativeSubstitutionApplication M
      dynamicTruthNativeSubstitutionTargetFirstReplacement
      dynamicTruthNativeSubstitutionTargetSecondReplacement
      dynamicTruthNativeSubstitutionTargetThirdReplacement
      currentGlobalPi targetPi /\
    fieldCode = rawDynamicTruthNativeSubstitutionFieldCode M
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi.

Arguments RawDynamicTruthNativeSubstitutionFieldTransformAt
  M currentGlobalSigma currentGlobalPi predecessorLevel fieldCode
  : clear implicits.

Local Opaque dynamicTruthNativeSubstitutionApplicationTermAt.

Theorem raw_sat_dynamicTruthNativeSubstitutionFieldTransformGraph_iff : forall
    (M : RawPAModel) tail
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode,
  raw_formula_sat M
    (scons M fieldCode (scons M currentGlobalSigma
      (scons M currentGlobalPi (scons M predecessorLevel tail))))
    dynamicTruthNativeSubstitutionFieldTransformGraph <->
  RawDynamicTruthNativeSubstitutionFieldTransformAt M
    currentGlobalSigma currentGlobalPi predecessorLevel fieldCode.
Proof.
  intros M tail currentGlobalSigma currentGlobalPi predecessorLevel fieldCode.
  unfold dynamicTruthNativeSubstitutionFieldTransformGraph,
    RawDynamicTruthNativeSubstitutionFieldTransformAt,
    fixedLevelEx8, dynamicTruthNativeSubstitutionAnd8.
  cbn [raw_formula_sat].
  split.
  - intros (currentLevel & currentLevelNumeral & sigmaDomain & piDomain &
      sourceSigma & targetSigma & sourcePi & targetPi & hlevel & hnumeral &
      hsigmaDomain & hpiDomain & hsourceSigma & htargetSigma &
      hsourcePi & htargetPi & hfield).
    change (currentLevel = raw_succ M predecessorLevel) in hlevel.
    apply (proj1 (raw_sat_numeralTermCodeAtTermAt_iff M _
      (tVar 7) (tVar 6))) in hnumeral.
    cbn [raw_term_eval scons] in hnumeral.
    apply (proj1 (raw_sat_codedFormulaSingleSubstitutionTermAt_iff M _
      (tVar 6)
      (Term.numeral
        (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
      (tVar 5))) in hsigmaDomain.
    rewrite raw_term_eval_numeral in hsigmaDomain.
    cbn [raw_term_eval scons] in hsigmaDomain.
    apply (proj1 (raw_sat_codedFormulaSingleSubstitutionTermAt_iff M _
      (tVar 6)
      (Term.numeral
        (formulaCode dynamicTruthLocalPiInputDomainTemplate))
      (tVar 4))) in hpiDomain.
    rewrite raw_term_eval_numeral in hpiDomain.
    cbn [raw_term_eval scons] in hpiDomain.
    apply (proj1 (raw_sat_dynamicTruthNativeSubstitutionApplicationTermAt_iff M _
      dynamicTruthNativeSubstitutionSourceFirstReplacement
      dynamicTruthNativeSubstitutionSourceSecondReplacement
      dynamicTruthNativeSubstitutionSourceThirdReplacement
      (tVar 9) (tVar 3))) in hsourceSigma.
    cbn [raw_term_eval scons] in hsourceSigma.
    apply (proj1 (raw_sat_dynamicTruthNativeSubstitutionApplicationTermAt_iff M _
      dynamicTruthNativeSubstitutionTargetFirstReplacement
      dynamicTruthNativeSubstitutionTargetSecondReplacement
      dynamicTruthNativeSubstitutionTargetThirdReplacement
      (tVar 9) (tVar 2))) in htargetSigma.
    cbn [raw_term_eval scons] in htargetSigma.
    apply (proj1 (raw_sat_dynamicTruthNativeSubstitutionApplicationTermAt_iff M _
      dynamicTruthNativeSubstitutionSourceFirstReplacement
      dynamicTruthNativeSubstitutionSourceSecondReplacement
      dynamicTruthNativeSubstitutionSourceThirdReplacement
      (tVar 10) (tVar 1))) in hsourcePi.
    cbn [raw_term_eval scons] in hsourcePi.
    apply (proj1 (raw_sat_dynamicTruthNativeSubstitutionApplicationTermAt_iff M _
      dynamicTruthNativeSubstitutionTargetFirstReplacement
      dynamicTruthNativeSubstitutionTargetSecondReplacement
      dynamicTruthNativeSubstitutionTargetThirdReplacement
      (tVar 10) (tVar 0))) in htargetPi.
    cbn [raw_term_eval scons] in htargetPi.
    apply (proj1 (raw_sat_dynamicTruthNativeSubstitutionFieldCodeTermAt_iff M _
      (tVar 8) (tVar 5) (tVar 4) (tVar 3) (tVar 2)
      (tVar 1) (tVar 0))) in hfield.
    cbn [raw_term_eval scons] in hfield.
    exists currentLevel, currentLevelNumeral, sigmaDomain, piDomain,
      sourceSigma, targetSigma, sourcePi, targetPi.
    split; [exact hlevel |].
    split; [exact hnumeral |].
    split; [exact hsigmaDomain |].
    split; [exact hpiDomain |].
    split; [exact hsourceSigma |].
    split; [exact htargetSigma |].
    split; [exact hsourcePi |].
    split; [exact htargetPi | exact hfield].
  - intros (currentLevel & currentLevelNumeral & sigmaDomain & piDomain &
      sourceSigma & targetSigma & sourcePi & targetPi & hlevel & hnumeral &
      hsigmaDomain & hpiDomain & hsourceSigma & htargetSigma &
      hsourcePi & htargetPi & hfield).
    exists currentLevel, currentLevelNumeral, sigmaDomain, piDomain,
      sourceSigma, targetSigma, sourcePi, targetPi.
    repeat split.
    + change (currentLevel = raw_succ M predecessorLevel). exact hlevel.
    + apply (proj2 (raw_sat_numeralTermCodeAtTermAt_iff M _
        (tVar 7) (tVar 6))).
      cbn [raw_term_eval scons]. exact hnumeral.
    + apply (proj2
        (raw_sat_codedFormulaSingleSubstitutionTermAt_iff M _
          (tVar 6)
          (Term.numeral
            (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
          (tVar 5))).
      rewrite raw_term_eval_numeral.
      cbn [raw_term_eval scons]. exact hsigmaDomain.
    + apply (proj2
        (raw_sat_codedFormulaSingleSubstitutionTermAt_iff M _
          (tVar 6)
          (Term.numeral
            (formulaCode dynamicTruthLocalPiInputDomainTemplate))
          (tVar 4))).
      rewrite raw_term_eval_numeral.
      cbn [raw_term_eval scons]. exact hpiDomain.
    + apply (proj2 (raw_sat_dynamicTruthNativeSubstitutionApplicationTermAt_iff M _
        dynamicTruthNativeSubstitutionSourceFirstReplacement
        dynamicTruthNativeSubstitutionSourceSecondReplacement
        dynamicTruthNativeSubstitutionSourceThirdReplacement
        (tVar 9) (tVar 3))).
      cbn [raw_term_eval scons]. exact hsourceSigma.
    + apply (proj2 (raw_sat_dynamicTruthNativeSubstitutionApplicationTermAt_iff M _
        dynamicTruthNativeSubstitutionTargetFirstReplacement
        dynamicTruthNativeSubstitutionTargetSecondReplacement
        dynamicTruthNativeSubstitutionTargetThirdReplacement
        (tVar 9) (tVar 2))).
      cbn [raw_term_eval scons]. exact htargetSigma.
    + apply (proj2 (raw_sat_dynamicTruthNativeSubstitutionApplicationTermAt_iff M _
        dynamicTruthNativeSubstitutionSourceFirstReplacement
        dynamicTruthNativeSubstitutionSourceSecondReplacement
        dynamicTruthNativeSubstitutionSourceThirdReplacement
        (tVar 10) (tVar 1))).
      cbn [raw_term_eval scons]. exact hsourcePi.
    + apply (proj2 (raw_sat_dynamicTruthNativeSubstitutionApplicationTermAt_iff M _
        dynamicTruthNativeSubstitutionTargetFirstReplacement
        dynamicTruthNativeSubstitutionTargetSecondReplacement
        dynamicTruthNativeSubstitutionTargetThirdReplacement
        (tVar 10) (tVar 0))).
      cbn [raw_term_eval scons]. exact htargetPi.
    + apply (proj2 (raw_sat_dynamicTruthNativeSubstitutionFieldCodeTermAt_iff M _
        (tVar 8) (tVar 5) (tVar 4) (tVar 3) (tVar 2)
        (tVar 1) (tVar 0))).
      cbn [raw_term_eval scons]. exact hfield.
Qed.

(** Constructor closure makes the selected field itself atomically adequate. *)
Lemma rawDynamicTruthNativeSubstitutionFieldCode_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  RawCodedFormulaAtomicallyAdequate M sigmaDomain ->
  RawCodedFormulaAtomicallyAdequate M piDomain ->
  RawCodedFormulaAtomicallyAdequate M sourceSigma ->
  RawCodedFormulaAtomicallyAdequate M targetSigma ->
  RawCodedFormulaAtomicallyAdequate M sourcePi ->
  RawCodedFormulaAtomicallyAdequate M targetPi ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthNativeSubstitutionFieldCode M
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi).
Proof.
  intros M hPA sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    hsigmaDomain hpiDomain hsourceSigma htargetSigma hsourcePi htargetPi.
  unfold rawDynamicTruthNativeSubstitutionFieldCode,
    rawDynamicTruthNativeSubstitutionFormulaAll7Code,
    rawDynamicTruthNativeSubstitutionFormulaAnd5Code,
    rawDynamicTruthNativeSubstitutionFormulaIffCode,
    rawDynamicTruthNativeSubstitutionSourceAdmissibleCode.
  apply raw_formulaAllCode_atomically_adequate; [exact hPA |].
  apply raw_formulaAllCode_atomically_adequate; [exact hPA |].
  apply raw_formulaAllCode_atomically_adequate; [exact hPA |].
  apply raw_formulaAllCode_atomically_adequate; [exact hPA |].
  apply raw_formulaAllCode_atomically_adequate; [exact hPA |].
  apply raw_formulaAllCode_atomically_adequate; [exact hPA |].
  apply raw_formulaAllCode_atomically_adequate; [exact hPA |].
  apply raw_formulaImpCode_atomically_adequate; [exact hPA | |].
  - apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
    + exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
        (codedFormulaSingleSubstitutionTermAt
          (tVar 0) (tVar 1) (tVar 2))).
    + apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
      * exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
          (codedFormulaSubstitutionAssignmentRelationTermAt
            (tVar 0) (tVar 1) (tVar 3) (tVar 4)
            (tVar 5) (tVar 6))).
      * apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
        -- apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
           ++ exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
                (codedFormulaAtomicallyAdequateTermAt (tVar 1))).
           ++ apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
              ** exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
                   (codedAssignmentDefinedThroughTermAt
                     (tVar 3) (tVar 4) (tVar 1))).
              ** apply raw_formulaOrCode_atomically_adequate;
                   [exact hPA | exact hsigmaDomain | exact hpiDomain].
        -- apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
           ++ exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
                (codedFormulaTargetAdmissibilityDataTermAt
                  (tVar 2) (tVar 5) (tVar 6))).
           ++ exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
                (codedFormulaRankAgreementTermAt (tVar 1) (tVar 2))).
  - apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
    + apply raw_formulaAndCode_atomically_adequate; [exact hPA | |];
        apply raw_formulaImpCode_atomically_adequate;
        try exact hPA; assumption.
    + apply raw_formulaAndCode_atomically_adequate; [exact hPA | |];
        apply raw_formulaImpCode_atomically_adequate;
        try exact hPA; assumption.
Qed.

(** ------------------------------------------------------------------
    Adequacy-preserving relational totality of the transform.

    The selected domain and application codes are produced by represented
    syntax relations.  Their adequacy invariants are retained long enough to
    prove that the transparent field polynomial is itself a formula code. *)

Definition RawDynamicTruthNativeSubstitutionFieldTransformTotalOnAdequate
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) currentGlobalSigma currentGlobalPi
      predecessorLevel,
    RawCodedFormulaAtomicallyAdequate M currentGlobalSigma ->
    RawCodedFormulaAtomicallyAdequate M currentGlobalPi ->
    exists fieldCode : M,
      raw_formula_sat M
        (scons M fieldCode (scons M currentGlobalSigma
          (scons M currentGlobalPi (scons M predecessorLevel tail))))
        dynamicTruthNativeSubstitutionFieldTransformGraph /\
      RawCodedFormulaAtomicallyAdequate M fieldCode.

Arguments RawDynamicTruthNativeSubstitutionFieldTransformTotalOnAdequate M
  : clear implicits.

Theorem
    dynamicTruthNativeSubstitutionFieldTransformGraph_raw_total_on_adequate :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeSubstitutionFieldTransformTotalOnAdequate M.
Proof.
  intros M hPA tail currentGlobalSigma currentGlobalPi predecessorLevel
    hcurrentSigma hcurrentPi.
  set (currentLevel := raw_succ M predecessorLevel).
  destruct (raw_numeralTermCodeExists_all M hPA currentLevel) as
    [currentLevelNumeral hcurrentLevelNumeral].
  destruct (raw_dynamicTruthLocalInputDomain_exists_adequate
    M hPA currentLevel currentLevelNumeral
    dynamicTruthLocalSigmaInputDomainTemplate hcurrentLevelNumeral) as
    (sigmaDomain & hsigmaDomain & hsigmaDomainAdequate).
  destruct (raw_dynamicTruthLocalInputDomain_exists_adequate
    M hPA currentLevel currentLevelNumeral
    dynamicTruthLocalPiInputDomainTemplate hcurrentLevelNumeral) as
    (piDomain & hpiDomain & hpiDomainAdequate).
  destruct (raw_dynamicTruthNativeSubstitutionApplication_exists_adequate
    M hPA dynamicTruthNativeSubstitutionSourceFirstReplacement
    dynamicTruthNativeSubstitutionSourceSecondReplacement
    dynamicTruthNativeSubstitutionSourceThirdReplacement
    currentGlobalSigma hcurrentSigma) as
    (sourceSigma & hsourceSigma & hsourceSigmaAdequate).
  destruct (raw_dynamicTruthNativeSubstitutionApplication_exists_adequate
    M hPA dynamicTruthNativeSubstitutionTargetFirstReplacement
    dynamicTruthNativeSubstitutionTargetSecondReplacement
    dynamicTruthNativeSubstitutionTargetThirdReplacement
    currentGlobalSigma hcurrentSigma) as
    (targetSigma & htargetSigma & htargetSigmaAdequate).
  destruct (raw_dynamicTruthNativeSubstitutionApplication_exists_adequate
    M hPA dynamicTruthNativeSubstitutionSourceFirstReplacement
    dynamicTruthNativeSubstitutionSourceSecondReplacement
    dynamicTruthNativeSubstitutionSourceThirdReplacement
    currentGlobalPi hcurrentPi) as
    (sourcePi & hsourcePi & hsourcePiAdequate).
  destruct (raw_dynamicTruthNativeSubstitutionApplication_exists_adequate
    M hPA dynamicTruthNativeSubstitutionTargetFirstReplacement
    dynamicTruthNativeSubstitutionTargetSecondReplacement
    dynamicTruthNativeSubstitutionTargetThirdReplacement
    currentGlobalPi hcurrentPi) as
    (targetPi & htargetPi & htargetPiAdequate).
  exists (rawDynamicTruthNativeSubstitutionFieldCode M
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi).
  split.
  - apply (proj2
      (raw_sat_dynamicTruthNativeSubstitutionFieldTransformGraph_iff M tail
        currentGlobalSigma currentGlobalPi predecessorLevel _)).
    exists currentLevel, currentLevelNumeral, sigmaDomain, piDomain,
      sourceSigma, targetSigma, sourcePi, targetPi.
    split; [unfold currentLevel; reflexivity |].
    split; [exact hcurrentLevelNumeral |].
    split; [exact hsigmaDomain |].
    split; [exact hpiDomain |].
    split; [exact hsourceSigma |].
    split; [exact htargetSigma |].
    split; [exact hsourcePi |].
    split; [exact htargetPi | reflexivity].
  - exact (rawDynamicTruthNativeSubstitutionFieldCode_atomically_adequate M hPA
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      hsigmaDomainAdequate hpiDomainAdequate
      hsourceSigmaAdequate htargetSigmaAdequate
      hsourcePiAdequate htargetPiAdequate).
Qed.

(** ------------------------------------------------------------------
    Output-first composition with the genuine current-level orbit. *)

Definition dynamicTruthNativeSubstitutionPositiveGraph : formula :=
  outputFirstPairedFormulaGraphComposition
    dynamicTruthNativeSubstitutionInputOrbitGraph
    dynamicTruthNativeSubstitutionFieldTransformGraph.

Definition RawDynamicTruthNativeSubstitutionPositiveAt
    (M : RawPAModel) (tail : nat -> M)
    (predecessorLevel fieldCode : M) : Prop :=
  exists currentGlobalSigma currentGlobalPi : M,
    RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
      tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi /\
    RawDynamicTruthNativeSubstitutionFieldTransformAt M
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode.

Arguments RawDynamicTruthNativeSubstitutionPositiveAt
  M tail predecessorLevel fieldCode : clear implicits.

Theorem raw_sat_dynamicTruthNativeSubstitutionPositiveGraph_iff : forall
    (M : RawPAModel) tail predecessorLevel fieldCode,
  raw_formula_sat M
    (scons M fieldCode (scons M predecessorLevel tail))
    dynamicTruthNativeSubstitutionPositiveGraph <->
  RawDynamicTruthNativeSubstitutionPositiveAt M
    tail predecessorLevel fieldCode.
Proof.
  intros M tail predecessorLevel fieldCode.
  unfold dynamicTruthNativeSubstitutionPositiveGraph,
    RawDynamicTruthNativeSubstitutionPositiveAt.
  rewrite raw_sat_outputFirstPairedFormulaGraphComposition_iff.
  unfold RawOutputFirstPairedFormulaGraphCompositionAt.
  split.
  - intros (currentGlobalSigma & currentGlobalPi & horbit & htransform).
    exists currentGlobalSigma, currentGlobalPi. split.
    + apply (proj1
        (raw_sat_dynamicTruthNativeSubstitutionInputOrbitGraph_iff M tail
          predecessorLevel currentGlobalSigma currentGlobalPi)).
      exact horbit.
    + apply (proj1
        (raw_sat_dynamicTruthNativeSubstitutionFieldTransformGraph_iff M tail
          currentGlobalSigma currentGlobalPi predecessorLevel fieldCode)).
      exact htransform.
  - intros (currentGlobalSigma & currentGlobalPi & horbit & htransform).
    exists currentGlobalSigma, currentGlobalPi. split.
    + apply (proj2
        (raw_sat_dynamicTruthNativeSubstitutionInputOrbitGraph_iff M tail
          predecessorLevel currentGlobalSigma currentGlobalPi)).
      exact horbit.
    + apply (proj2
        (raw_sat_dynamicTruthNativeSubstitutionFieldTransformGraph_iff M tail
          currentGlobalSigma currentGlobalPi predecessorLevel fieldCode)).
      exact htransform.
Qed.

(** Totality keeps the formula-code invariant in its public conclusion. *)
Definition RawDynamicTruthNativeSubstitutionPositiveAdequateTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel,
    exists fieldCode : M,
      raw_formula_sat M
        (scons M fieldCode (scons M predecessorLevel tail))
        dynamicTruthNativeSubstitutionPositiveGraph /\
      RawCodedFormulaAtomicallyAdequate M fieldCode.

Arguments RawDynamicTruthNativeSubstitutionPositiveAdequateTotal M
  : clear implicits.

Theorem dynamicTruthNativeSubstitutionPositiveGraph_raw_adequate_total :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeSubstitutionPositiveAdequateTotal M.
Proof.
  intros M hPA tail predecessorLevel.
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail (raw_succ M predecessorLevel)) as
    (currentGlobalSigma & currentGlobalPi & horbit &
     hcurrentSigma & hcurrentPi).
  destruct
    (dynamicTruthNativeSubstitutionFieldTransformGraph_raw_total_on_adequate
      M hPA tail currentGlobalSigma currentGlobalPi predecessorLevel
      hcurrentSigma hcurrentPi) as
    (fieldCode & htransform & hfieldAdequate).
  exists fieldCode. split; [|exact hfieldAdequate].
  apply (proj2 (raw_sat_dynamicTruthNativeSubstitutionPositiveGraph_iff
    M tail predecessorLevel fieldCode)).
  exists currentGlobalSigma, currentGlobalPi. split.
  - apply (proj1
      (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M tail
        (raw_succ M predecessorLevel)
        currentGlobalSigma currentGlobalPi)).
    exact horbit.
  - apply (proj1
      (raw_sat_dynamicTruthNativeSubstitutionFieldTransformGraph_iff M tail
        currentGlobalSigma currentGlobalPi predecessorLevel fieldCode)).
    exact htransform.
Qed.

Definition RawDynamicTruthNativeSubstitutionPositiveTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel,
    exists fieldCode : M,
      raw_formula_sat M
        (scons M fieldCode (scons M predecessorLevel tail))
        dynamicTruthNativeSubstitutionPositiveGraph.

Arguments RawDynamicTruthNativeSubstitutionPositiveTotal M : clear implicits.

Corollary dynamicTruthNativeSubstitutionPositiveGraph_raw_total :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeSubstitutionPositiveTotal M.
Proof.
  intros M hPA tail predecessorLevel.
  destruct (dynamicTruthNativeSubstitutionPositiveGraph_raw_adequate_total
    M hPA tail predecessorLevel) as (fieldCode & hfield & _).
  now exists fieldCode.
Qed.

(** ------------------------------------------------------------------
    Exact remaining object-proof compiler seam.

    The fixed-level theorem above supplies genuine represented PA proofs for
    every externally fixed standard level.  At an arbitrary carrier index,
    relational syntax totality alone cannot manufacture a represented proof.
    The following premise therefore asks only for the missing uniform
    compiler on the exact adequate orbit witness and exact transform trace;
    it assumes neither semantic validity nor model-theoretic soundness. *)

Definition RawDynamicTruthNativeSubstitutionProofCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi fieldCode,
    RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi ->
    RawDynamicTruthNativeSubstitutionFieldTransformAt M
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode ->
    exists certificate : M,
      RawCodedPAProofOf M fieldCode certificate.

Arguments RawDynamicTruthNativeSubstitutionProofCompiler M : clear implicits.

Definition RawDynamicTruthNativeSubstitutionPositiveProofTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel,
    exists fieldCode certificate : M,
      raw_formula_sat M
        (scons M fieldCode (scons M predecessorLevel tail))
        dynamicTruthNativeSubstitutionPositiveGraph /\
      RawCodedFormulaAtomicallyAdequate M fieldCode /\
      RawCodedPAProofOf M fieldCode certificate.

Arguments RawDynamicTruthNativeSubstitutionPositiveProofTotal M : clear implicits.

Theorem dynamicTruthNativeSubstitutionPositiveGraph_raw_proof_total_of_compiler :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeSubstitutionProofCompiler M ->
  RawDynamicTruthNativeSubstitutionPositiveProofTotal M.
Proof.
  intros M hPA hcompiler tail predecessorLevel.
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail (raw_succ M predecessorLevel)) as
    (currentGlobalSigma & currentGlobalPi & horbit &
     hcurrentSigma & hcurrentPi).
  assert (hadequateOrbit :
      RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
        tail (raw_succ M predecessorLevel)
        currentGlobalSigma currentGlobalPi).
  {
    apply (proj2
      (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M tail
        (raw_succ M predecessorLevel)
        currentGlobalSigma currentGlobalPi)).
    split.
    - apply (proj1
        (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M tail
          (raw_succ M predecessorLevel)
          currentGlobalSigma currentGlobalPi)).
      exact horbit.
    - split; assumption.
  }
  destruct
    (dynamicTruthNativeSubstitutionFieldTransformGraph_raw_total_on_adequate
      M hPA tail currentGlobalSigma currentGlobalPi predecessorLevel
      hcurrentSigma hcurrentPi) as
    (fieldCode & htransformSat & hfieldAdequate).
  pose proof (proj1
    (raw_sat_dynamicTruthNativeSubstitutionFieldTransformGraph_iff M tail
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode)
    htransformSat) as htransform.
  destruct (hcompiler tail predecessorLevel currentGlobalSigma
    currentGlobalPi fieldCode hadequateOrbit htransform) as
    [certificate hcertificate].
  exists fieldCode, certificate.
  split.
  - apply (proj2 (raw_sat_dynamicTruthNativeSubstitutionPositiveGraph_iff
      M tail predecessorLevel fieldCode)).
    exists currentGlobalSigma, currentGlobalPi. split.
    + apply (proj1
        (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M tail
          (raw_succ M predecessorLevel)
          currentGlobalSigma currentGlobalPi)).
      exact hadequateOrbit.
    + exact htransform.
  - split; assumption.
Qed.

End PABoundedRawCodedDynamicTruthNativeSubstitutionPositiveGraph.
