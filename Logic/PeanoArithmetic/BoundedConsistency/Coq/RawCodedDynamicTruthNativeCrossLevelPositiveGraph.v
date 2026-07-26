(**
  The carrier-indexed positive adjacent-level coherence field.

  The positive master coordinate is indexed by a predecessor [p].  It must
  describe the native coherence law at the current level [S p], hence between
  the current global Sigma/Pi predicates at [S p] and their genuine native
  successors at [S (S p)].  No carrier element is decoded as a metatheoretic
  natural number.

  The construction below therefore

    1. selects the genuine paired global formula-code orbit at [S p];
    2. runs the genuine paired global successor graph at lower level [S p];
    3. applies all four current/next global predicates to the three input
       variables of the fixed coherence formula;
    4. instantiates both current-level domain templates with the represented
       numeral for [S p]; and
    5. builds the exact universally closed, admissibility-guarded pair of
       Sigma/Pi biconditionals used by the fixed-level coherence coordinate.

  Exact graph semantics is law free.  PA is used for relational totality and
  for quoting each externally fixed standard coherence theorem.  The latter
  does not by itself compile a proof at a possibly nonstandard carrier index;
  the final section isolates that remaining object-proof compiler precisely
  and never infers represented provability from semantic validity.
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
  RawCodedFixedLevelTruthCoherence
  RawCodedFixedLevelTruthAdmissibleCoherence
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPairedSuccessorRowGraph
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedOutputFirstPairedFormulaGraphComposition.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthNativeCrossLevelPositiveGraph.

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
Import PABoundedRawCodedFixedLevelTruthCoherence.
Import PABoundedRawCodedFixedLevelTruthAdmissibleCoherence.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedOutputFirstPairedFormulaGraphComposition.

(** ------------------------------------------------------------------
    Exact native target formula. *)

Definition dynamicTruthNativeCrossLevelGuardedEquivalenceFormula
    (domain current next : formula) : formula :=
  pImp domain
    (pAnd (pImp current next) (pImp next current)).

Definition dynamicTruthNativeCrossLevelCoherenceCarrierFormula
    (sigmaDomain piDomain currentSigma currentPi nextSigma nextPi : formula)
    : formula :=
  pAll (pAll (pAll
    (pImp
      (dynamicTruthLocalAdmissibleFormula sigmaDomain piDomain)
      (pAnd
        (dynamicTruthNativeCrossLevelGuardedEquivalenceFormula
          sigmaDomain currentSigma nextSigma)
        (dynamicTruthNativeCrossLevelGuardedEquivalenceFormula
          piDomain currentPi nextPi))))).

(** This is a literal presentation theorem, not merely a semantic
    equivalence.  It fixes the current/next convention used by the graph. *)
Lemma dynamicTruthNativeCrossLevelCoherenceCarrierFormula_fixedLevel :
  forall currentLevel,
  dynamicTruthNativeCrossLevelCoherenceCarrierFormula
    (fixedLevelSigmaDomainTermAt currentLevel (tVar 2))
    (fixedLevelPiDomainTermAt currentLevel (tVar 2))
    (fixedLevelSigmaTruthCertificateTermAt currentLevel
      (tVar 2) (tVar 1) (tVar 0))
    (fixedLevelPiFalsityCertificateTermAt currentLevel
      (tVar 2) (tVar 1) (tVar 0))
    (fixedLevelSigmaTruthCertificateTermAt (S currentLevel)
      (tVar 2) (tVar 1) (tVar 0))
    (fixedLevelPiFalsityCertificateTermAt (S currentLevel)
      (tVar 2) (tVar 1) (tVar 0)) =
  fixedLevelAdmissibleTruthCertificateCoherenceFormula currentLevel.
Proof.
  intro currentLevel.
  unfold dynamicTruthNativeCrossLevelCoherenceCarrierFormula,
    dynamicTruthNativeCrossLevelGuardedEquivalenceFormula,
    dynamicTruthLocalAdmissibleFormula,
    fixedLevelAdmissibleTruthCertificateCoherenceFormula,
    fixedLevelTruthAdmissibleTermAt.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Transparent carrier polynomial for the coherence target. *)

Definition dynamicTruthNativeCrossLevelGuardedEquivalenceCodeTerm
    (domain current next : term) : term :=
  dynamicTruthLocalFormulaImpCodeTerm domain
    (dynamicTruthLocalFormulaAndCodeTerm
      (dynamicTruthLocalFormulaImpCodeTerm current next)
      (dynamicTruthLocalFormulaImpCodeTerm next current)).

Definition dynamicTruthNativeCrossLevelCoherenceFieldCodeTerm
    (sigmaDomain piDomain currentSigma currentPi nextSigma nextPi : term)
    : term :=
  dynamicTruthLocalFormulaAll3CodeTerm
    (dynamicTruthLocalFormulaImpCodeTerm
      (dynamicTruthLocalAdmissibleCodeTerm sigmaDomain piDomain)
      (dynamicTruthLocalFormulaAndCodeTerm
        (dynamicTruthNativeCrossLevelGuardedEquivalenceCodeTerm
          sigmaDomain currentSigma nextSigma)
        (dynamicTruthNativeCrossLevelGuardedEquivalenceCodeTerm
          piDomain currentPi nextPi))).

Definition rawDynamicTruthNativeCrossLevelGuardedEquivalenceCode
    (M : RawPAModel) (domain current next : M) : M :=
  rawFormulaImpCode M domain
    (rawFormulaAndCode M
      (rawFormulaImpCode M current next)
      (rawFormulaImpCode M next current)).

Definition rawDynamicTruthNativeCrossLevelCoherenceFieldCode
    (M : RawPAModel)
    (sigmaDomain piDomain currentSigma currentPi nextSigma nextPi : M) : M :=
  rawDynamicTruthLocalFormulaAll3Code M
    (rawFormulaImpCode M
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
      (rawFormulaAndCode M
        (rawDynamicTruthNativeCrossLevelGuardedEquivalenceCode M
          sigmaDomain currentSigma nextSigma)
        (rawDynamicTruthNativeCrossLevelGuardedEquivalenceCode M
          piDomain currentPi nextPi))).

Lemma raw_eval_dynamicTruthNativeCrossLevelGuardedEquivalenceCodeTerm :
    forall (M : RawPAModel) e domain current next,
  raw_term_eval M e
    (dynamicTruthNativeCrossLevelGuardedEquivalenceCodeTerm
      domain current next) =
  rawDynamicTruthNativeCrossLevelGuardedEquivalenceCode M
    (raw_term_eval M e domain) (raw_term_eval M e current)
    (raw_term_eval M e next).
Proof.
  intros.
  unfold dynamicTruthNativeCrossLevelGuardedEquivalenceCodeTerm,
    rawDynamicTruthNativeCrossLevelGuardedEquivalenceCode.
  rewrite !raw_eval_dynamicTruthLocalFormulaImpCodeTerm,
    raw_eval_dynamicTruthLocalFormulaAndCodeTerm.
  reflexivity.
Qed.

Lemma raw_eval_dynamicTruthNativeCrossLevelCoherenceFieldCodeTerm :
    forall (M : RawPAModel) e
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi,
  raw_term_eval M e
    (dynamicTruthNativeCrossLevelCoherenceFieldCodeTerm
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi) =
  rawDynamicTruthNativeCrossLevelCoherenceFieldCode M
    (raw_term_eval M e sigmaDomain) (raw_term_eval M e piDomain)
    (raw_term_eval M e currentSigma) (raw_term_eval M e currentPi)
    (raw_term_eval M e nextSigma) (raw_term_eval M e nextPi).
Proof.
  intros.
  unfold dynamicTruthNativeCrossLevelCoherenceFieldCodeTerm,
    rawDynamicTruthNativeCrossLevelCoherenceFieldCode.
  rewrite raw_eval_dynamicTruthLocalFormulaAll3CodeTerm,
    raw_eval_dynamicTruthLocalFormulaImpCodeTerm,
    raw_eval_dynamicTruthLocalAdmissibleCodeTerm,
    raw_eval_dynamicTruthLocalFormulaAndCodeTerm,
    !raw_eval_dynamicTruthNativeCrossLevelGuardedEquivalenceCodeTerm.
  reflexivity.
Qed.

Definition dynamicTruthNativeCrossLevelCoherenceFieldCodeTermAt
    (output sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      : term) : formula :=
  pEq output
    (dynamicTruthNativeCrossLevelCoherenceFieldCodeTerm
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi).

Lemma raw_sat_dynamicTruthNativeCrossLevelCoherenceFieldCodeTermAt_iff :
    forall (M : RawPAModel) e
      output sigmaDomain piDomain currentSigma currentPi nextSigma nextPi,
  raw_formula_sat M e
    (dynamicTruthNativeCrossLevelCoherenceFieldCodeTermAt
      output sigmaDomain piDomain currentSigma currentPi nextSigma nextPi) <->
  raw_term_eval M e output =
    rawDynamicTruthNativeCrossLevelCoherenceFieldCode M
      (raw_term_eval M e sigmaDomain) (raw_term_eval M e piDomain)
      (raw_term_eval M e currentSigma) (raw_term_eval M e currentPi)
      (raw_term_eval M e nextSigma) (raw_term_eval M e nextPi).
Proof.
  intros.
  unfold dynamicTruthNativeCrossLevelCoherenceFieldCodeTermAt.
  change (raw_term_eval M e output =
      raw_term_eval M e
        (dynamicTruthNativeCrossLevelCoherenceFieldCodeTerm
          sigmaDomain piDomain currentSigma currentPi nextSigma nextPi) <->
    raw_term_eval M e output =
      rawDynamicTruthNativeCrossLevelCoherenceFieldCode M
        (raw_term_eval M e sigmaDomain) (raw_term_eval M e piDomain)
        (raw_term_eval M e currentSigma) (raw_term_eval M e currentPi)
        (raw_term_eval M e nextSigma) (raw_term_eval M e nextPi)).
  rewrite raw_eval_dynamicTruthNativeCrossLevelCoherenceFieldCodeTerm.
  reflexivity.
Qed.

Theorem rawDynamicTruthNativeCrossLevelCoherenceFieldCode_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi,
  rawDynamicTruthNativeCrossLevelCoherenceFieldCode M
    (rawQuotedFormulaCode M sigmaDomain)
    (rawQuotedFormulaCode M piDomain)
    (rawQuotedFormulaCode M currentSigma)
    (rawQuotedFormulaCode M currentPi)
    (rawQuotedFormulaCode M nextSigma)
    (rawQuotedFormulaCode M nextPi) =
  rawQuotedFormulaCode M
    (dynamicTruthNativeCrossLevelCoherenceCarrierFormula
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi).
Proof.
  intros M hPA sigmaDomain piDomain currentSigma currentPi nextSigma nextPi.
  unfold rawDynamicTruthNativeCrossLevelCoherenceFieldCode,
    rawDynamicTruthNativeCrossLevelGuardedEquivalenceCode,
    rawDynamicTruthLocalFormulaAll3Code,
    rawDynamicTruthLocalAdmissibleCode,
    dynamicTruthNativeCrossLevelCoherenceCarrierFormula,
    dynamicTruthNativeCrossLevelGuardedEquivalenceFormula,
    dynamicTruthLocalAdmissibleFormula.
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    (codedFormulaAtomicallyAdequateTermAt (tVar 2))).
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    (codedAssignmentDefinedThroughTermAt
      (tVar 1) (tVar 0) (tVar 2))).
  reflexivity.
Qed.

(** A predecessor [p] targets coherence at current level [S p], comparing
    the orbit predicates at [S p] and [S (S p)]. *)
Corollary
    rawDynamicTruthNativeCrossLevelCoherenceFieldCode_quoted_successor_levels :
  forall (M : RawPAModel), RawPASatisfies M -> forall predecessor,
  rawDynamicTruthNativeCrossLevelCoherenceFieldCode M
    (rawQuotedFormulaCode M
      (fixedLevelSigmaDomainTermAt (S predecessor) (tVar 2)))
    (rawQuotedFormulaCode M
      (fixedLevelPiDomainTermAt (S predecessor) (tVar 2)))
    (rawQuotedFormulaCode M
      (fixedLevelSigmaTruthCertificateTermAt (S predecessor)
        (tVar 2) (tVar 1) (tVar 0)))
    (rawQuotedFormulaCode M
      (fixedLevelPiFalsityCertificateTermAt (S predecessor)
        (tVar 2) (tVar 1) (tVar 0)))
    (rawQuotedFormulaCode M
      (fixedLevelSigmaTruthCertificateTermAt (S (S predecessor))
        (tVar 2) (tVar 1) (tVar 0)))
    (rawQuotedFormulaCode M
      (fixedLevelPiFalsityCertificateTermAt (S (S predecessor))
        (tVar 2) (tVar 1) (tVar 0))) =
  rawQuotedFormulaCode M
    (fixedLevelAdmissibleTruthCertificateCoherenceFormula (S predecessor)).
Proof.
  intros M hPA predecessor.
  rewrite rawDynamicTruthNativeCrossLevelCoherenceFieldCode_quoted
    by exact hPA.
  rewrite dynamicTruthNativeCrossLevelCoherenceCarrierFormula_fixedLevel.
  reflexivity.
Qed.

(** The externally fixed theorem genuinely has a represented PA proof.  This
    is the maximal result furnished by the existing fixed-level compiler: its
    [currentLevel] is a Rocq natural, not an arbitrary carrier element. *)
Theorem raw_fixedLevelCrossLevelCoherence_quoted_proof : forall
    (M : RawPAModel), RawPASatisfies M -> forall currentLevel,
  exists certificate : M,
    RawCodedPAProofOf M
      (rawQuotedFormulaCode M
        (fixedLevelAdmissibleTruthCertificateCoherenceFormula currentLevel))
      certificate.
Proof.
  intros M hPA currentLevel.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    (fixedLevelAdmissibleTruthCertificateCoherenceFormula currentLevel)
    (PA_proves_fixedLevelAdmissibleTruthCertificateCoherenceFormula
      currentLevel)) as [certificate hcertificate].
  exists certificate.
  rewrite rawQuotedFormulaCode_standard by exact hPA.
  exact hcertificate.
Qed.

Corollary
    rawDynamicTruthNativeCrossLevelCoherenceFieldCode_standard_proof :
  forall (M : RawPAModel), RawPASatisfies M -> forall predecessor,
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthNativeCrossLevelCoherenceFieldCode M
        (rawQuotedFormulaCode M
          (fixedLevelSigmaDomainTermAt (S predecessor) (tVar 2)))
        (rawQuotedFormulaCode M
          (fixedLevelPiDomainTermAt (S predecessor) (tVar 2)))
        (rawQuotedFormulaCode M
          (fixedLevelSigmaTruthCertificateTermAt (S predecessor)
            (tVar 2) (tVar 1) (tVar 0)))
        (rawQuotedFormulaCode M
          (fixedLevelPiFalsityCertificateTermAt (S predecessor)
            (tVar 2) (tVar 1) (tVar 0)))
        (rawQuotedFormulaCode M
          (fixedLevelSigmaTruthCertificateTermAt (S (S predecessor))
            (tVar 2) (tVar 1) (tVar 0)))
        (rawQuotedFormulaCode M
          (fixedLevelPiFalsityCertificateTermAt (S (S predecessor))
            (tVar 2) (tVar 1) (tVar 0))))
      certificate.
Proof.
  intros M hPA predecessor.
  rewrite rawDynamicTruthNativeCrossLevelCoherenceFieldCode_quoted_successor_levels
    by exact hPA.
  exact (raw_fixedLevelCrossLevelCoherence_quoted_proof
    M hPA (S predecessor)).
Qed.

(** ------------------------------------------------------------------
    The shifted genuine paired orbit. *)

Definition dynamicTruthNativeCrossLevelInputOrbitGraph : formula :=
  dynamicTruthNativeLocalInputOrbitGraph.

Definition RawDynamicTruthNativeCrossLevelInputOrbitAt
    (M : RawPAModel) (tail : nat -> M)
    (predecessorLevel globalSigma globalPi : M) : Prop :=
  RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
    tail (raw_succ M predecessorLevel) globalSigma globalPi.

Arguments RawDynamicTruthNativeCrossLevelInputOrbitAt
  M tail predecessorLevel globalSigma globalPi : clear implicits.

Theorem raw_sat_dynamicTruthNativeCrossLevelInputOrbitGraph_iff : forall
    (M : RawPAModel) tail predecessorLevel globalSigma globalPi,
  raw_formula_sat M
    (scons M globalSigma (scons M globalPi
      (scons M predecessorLevel tail)))
    dynamicTruthNativeCrossLevelInputOrbitGraph <->
  RawDynamicTruthNativeCrossLevelInputOrbitAt M
    tail predecessorLevel globalSigma globalPi.
Proof.
  intros.
  unfold dynamicTruthNativeCrossLevelInputOrbitGraph,
    RawDynamicTruthNativeCrossLevelInputOrbitAt.
  exact (raw_sat_dynamicTruthNativeLocalInputOrbitGraph_iff
    M tail predecessorLevel globalSigma globalPi).
Qed.

Corollary
    raw_sat_dynamicTruthNativeCrossLevelInputOrbitGraph_standard_iff : forall
    (M : RawPAModel) tail predecessor globalSigma globalPi,
  raw_formula_sat M
    (scons M globalSigma (scons M globalPi
      (scons M (rawNumeralValue M predecessor) tail)))
    dynamicTruthNativeCrossLevelInputOrbitGraph <->
  RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
    tail (rawNumeralValue M (S predecessor)) globalSigma globalPi.
Proof.
  intros.
  unfold dynamicTruthNativeCrossLevelInputOrbitGraph.
  exact (raw_sat_dynamicTruthNativeLocalInputOrbitGraph_standard_iff
    M tail predecessor globalSigma globalPi).
Qed.

(** ------------------------------------------------------------------
    Transform the current orbit pair into the adjacent-level target.

    Beneath the ten witnesses the environment is

      nextPiEvidence :: nextSigmaEvidence ::
      currentPiEvidence :: currentSigmaEvidence ::
      piDomain :: sigmaDomain :: currentLevelNumeral ::
      nextGlobalPi :: nextGlobalSigma :: currentLevel ::
      fieldCode :: currentGlobalSigma :: currentGlobalPi ::
      predecessorLevel :: tail.

    The successor subgraph consumes the current pair at [currentLevel] and
    produces the next pair.  The checked equation
    [currentLevel = S predecessorLevel] pins the positive splice. *)

Definition dynamicTruthNativeCrossLevelAnd8
    (a b c d e f g h : formula) : formula :=
  pAnd a (pAnd b (pAnd c (pAnd d (pAnd e (pAnd f (pAnd g h)))))).

Definition dynamicTruthNativeCrossLevelSuccessorRenaming
    (index : nat) : nat :=
  match index with
  | 0 => 8
  | 1 => 7
  | 2 => 11
  | 3 => 12
  | 4 => 9
  | S (S (S (S (S tailIndex)))) => 14 + tailIndex
  end.

Definition dynamicTruthNativeCrossLevelTransformEnvironment
    (M : RawPAModel)
    (nextPiEvidence nextSigmaEvidence currentPiEvidence currentSigmaEvidence
      piDomain sigmaDomain currentLevelNumeral nextGlobalPi nextGlobalSigma
      currentLevel fieldCode currentGlobalSigma currentGlobalPi
      predecessorLevel : M)
    (tail : nat -> M) : nat -> M :=
  scons M nextPiEvidence (scons M nextSigmaEvidence
    (scons M currentPiEvidence (scons M currentSigmaEvidence
      (scons M piDomain (scons M sigmaDomain
        (scons M currentLevelNumeral
          (scons M nextGlobalPi (scons M nextGlobalSigma
            (scons M currentLevel (scons M fieldCode
              (scons M currentGlobalSigma (scons M currentGlobalPi
                (scons M predecessorLevel tail))))))))))))).

Definition dynamicTruthNativeCrossLevelSuccessorBodyGraph : formula :=
  Formula.rename dynamicTruthNativeCrossLevelSuccessorRenaming
    dynamicTruthPairedGlobalSuccessorGraph.

Lemma raw_sat_dynamicTruthNativeCrossLevelSuccessorBodyGraph_iff : forall
    (M : RawPAModel) tail
      nextPiEvidence nextSigmaEvidence currentPiEvidence currentSigmaEvidence
      piDomain sigmaDomain currentLevelNumeral nextGlobalPi nextGlobalSigma
      currentLevel fieldCode currentGlobalSigma currentGlobalPi
      predecessorLevel,
  raw_formula_sat M
    (dynamicTruthNativeCrossLevelTransformEnvironment M
      nextPiEvidence nextSigmaEvidence currentPiEvidence currentSigmaEvidence
      piDomain sigmaDomain currentLevelNumeral nextGlobalPi nextGlobalSigma
      currentLevel fieldCode currentGlobalSigma currentGlobalPi
      predecessorLevel tail)
    dynamicTruthNativeCrossLevelSuccessorBodyGraph <->
  raw_formula_sat M
    (scons M nextGlobalSigma (scons M nextGlobalPi
      (scons M currentGlobalSigma (scons M currentGlobalPi
        (scons M currentLevel tail)))))
    dynamicTruthPairedGlobalSuccessorGraph.
Proof.
  intros.
  unfold dynamicTruthNativeCrossLevelSuccessorBodyGraph.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro index.
  destruct index as [|[|[|[|[|tailIndex]]]]];
    cbn [dynamicTruthNativeCrossLevelTransformEnvironment
      dynamicTruthNativeCrossLevelSuccessorRenaming scons]; reflexivity.
Qed.

Local Opaque dynamicTruthNativeCrossLevelSuccessorBodyGraph.
Local Opaque dynamicTruthPairedGlobalSuccessorGraph.
Local Opaque dynamicTruthLocalTernaryApplicationTermAt.

Definition dynamicTruthNativeCrossLevelFieldTransformGraph : formula :=
  fixedTruthTraversalEx10
    (pAnd
      (pEq (tVar 9) (tSucc (tVar 13)))
      (pAnd
        dynamicTruthNativeCrossLevelSuccessorBodyGraph
        (dynamicTruthNativeCrossLevelAnd8
          (numeralTermCodeAtTermAt (tVar 9) (tVar 6))
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
          (dynamicTruthLocalTernaryApplicationTermAt
            (tVar 11) (tVar 3))
          (dynamicTruthLocalTernaryApplicationTermAt
            (tVar 12) (tVar 2))
          (dynamicTruthLocalTernaryApplicationTermAt
            (tVar 8) (tVar 1))
          (dynamicTruthLocalTernaryApplicationTermAt
            (tVar 7) (tVar 0))
          (dynamicTruthNativeCrossLevelCoherenceFieldCodeTermAt
            (tVar 10) (tVar 5) (tVar 4) (tVar 3) (tVar 2)
            (tVar 1) (tVar 0))))).

Definition RawDynamicTruthNativeCrossLevelFieldTransformAt
    (M : RawPAModel)
    (currentGlobalSigma currentGlobalPi predecessorLevel fieldCode : M)
    : Prop :=
  exists currentLevel nextGlobalSigma nextGlobalPi currentLevelNumeral
      sigmaDomain piDomain currentSigmaEvidence currentPiEvidence
      nextSigmaEvidence nextPiEvidence : M,
    currentLevel = raw_succ M predecessorLevel /\
    RawDynamicTruthPairedGlobalSuccessorAt M
      currentGlobalSigma currentGlobalPi currentLevel
      nextGlobalSigma nextGlobalPi /\
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
      currentGlobalSigma currentSigmaEvidence /\
    RawDynamicTruthLocalTernaryApplication M
      currentGlobalPi currentPiEvidence /\
    RawDynamicTruthLocalTernaryApplication M
      nextGlobalSigma nextSigmaEvidence /\
    RawDynamicTruthLocalTernaryApplication M
      nextGlobalPi nextPiEvidence /\
    fieldCode = rawDynamicTruthNativeCrossLevelCoherenceFieldCode M
      sigmaDomain piDomain currentSigmaEvidence currentPiEvidence
      nextSigmaEvidence nextPiEvidence.

Arguments RawDynamicTruthNativeCrossLevelFieldTransformAt
  M currentGlobalSigma currentGlobalPi predecessorLevel fieldCode
  : clear implicits.

Theorem raw_sat_dynamicTruthNativeCrossLevelFieldTransformGraph_iff : forall
    (M : RawPAModel) tail
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode,
  raw_formula_sat M
    (scons M fieldCode (scons M currentGlobalSigma
      (scons M currentGlobalPi (scons M predecessorLevel tail))))
    dynamicTruthNativeCrossLevelFieldTransformGraph <->
  RawDynamicTruthNativeCrossLevelFieldTransformAt M
    currentGlobalSigma currentGlobalPi predecessorLevel fieldCode.
Proof.
  intros M tail currentGlobalSigma currentGlobalPi predecessorLevel fieldCode.
  unfold dynamicTruthNativeCrossLevelFieldTransformGraph,
    RawDynamicTruthNativeCrossLevelFieldTransformAt,
    fixedTruthTraversalEx10, fixedLevelEx8,
    dynamicTruthNativeCrossLevelAnd8.
  cbn [raw_formula_sat].
  (** As in the local graph, transporting conjuncts explicitly keeps Rocq
      from unfolding the large native successor formula under ten binders. *)
  split.
  - intros (currentLevel & nextGlobalSigma & nextGlobalPi &
      currentLevelNumeral & sigmaDomain & piDomain & currentSigmaEvidence &
      currentPiEvidence & nextSigmaEvidence & nextPiEvidence & hlevel &
      hsuccessor & hnumeral & hsigmaDomain & hpiDomain & hcurrentSigma &
      hcurrentPi & hnextSigma & hnextPi & hfield).
    change (currentLevel = raw_succ M predecessorLevel) in hlevel.
    apply (proj1
      (raw_sat_dynamicTruthNativeCrossLevelSuccessorBodyGraph_iff M tail
        nextPiEvidence nextSigmaEvidence currentPiEvidence
        currentSigmaEvidence piDomain sigmaDomain currentLevelNumeral
        nextGlobalPi nextGlobalSigma currentLevel fieldCode
        currentGlobalSigma currentGlobalPi predecessorLevel)) in hsuccessor.
    apply (proj1
      (raw_sat_dynamicTruthPairedGlobalSuccessorGraph_iff M tail currentLevel
        currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi))
      in hsuccessor.
    apply (proj1 (raw_sat_numeralTermCodeAtTermAt_iff M _
      (tVar 9) (tVar 6))) in hnumeral.
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
    apply (proj1 (raw_sat_dynamicTruthLocalTernaryApplicationTermAt_iff
      M _ (tVar 11) (tVar 3))) in hcurrentSigma.
    cbn [raw_term_eval scons] in hcurrentSigma.
    apply (proj1 (raw_sat_dynamicTruthLocalTernaryApplicationTermAt_iff
      M _ (tVar 12) (tVar 2))) in hcurrentPi.
    cbn [raw_term_eval scons] in hcurrentPi.
    apply (proj1 (raw_sat_dynamicTruthLocalTernaryApplicationTermAt_iff
      M _ (tVar 8) (tVar 1))) in hnextSigma.
    cbn [raw_term_eval scons] in hnextSigma.
    apply (proj1 (raw_sat_dynamicTruthLocalTernaryApplicationTermAt_iff
      M _ (tVar 7) (tVar 0))) in hnextPi.
    cbn [raw_term_eval scons] in hnextPi.
    apply (proj1
      (raw_sat_dynamicTruthNativeCrossLevelCoherenceFieldCodeTermAt_iff M _
        (tVar 10) (tVar 5) (tVar 4) (tVar 3) (tVar 2)
        (tVar 1) (tVar 0))) in hfield.
    cbn [raw_term_eval scons] in hfield.
    exists currentLevel, nextGlobalSigma, nextGlobalPi,
      currentLevelNumeral, sigmaDomain, piDomain, currentSigmaEvidence,
      currentPiEvidence, nextSigmaEvidence, nextPiEvidence.
    split; [exact hlevel |].
    split; [exact hsuccessor |].
    split; [exact hnumeral |].
    split; [exact hsigmaDomain |].
    split; [exact hpiDomain |].
    split; [exact hcurrentSigma |].
    split; [exact hcurrentPi |].
    split; [exact hnextSigma |].
    split; [exact hnextPi | exact hfield].
  - intros (currentLevel & nextGlobalSigma & nextGlobalPi &
      currentLevelNumeral & sigmaDomain & piDomain & currentSigmaEvidence &
      currentPiEvidence & nextSigmaEvidence & nextPiEvidence & hlevel &
      hsuccessor & hnumeral & hsigmaDomain & hpiDomain & hcurrentSigma &
      hcurrentPi & hnextSigma & hnextPi & hfield).
    exists currentLevel, nextGlobalSigma, nextGlobalPi,
      currentLevelNumeral, sigmaDomain, piDomain, currentSigmaEvidence,
      currentPiEvidence, nextSigmaEvidence, nextPiEvidence.
    repeat split.
    + change (currentLevel = raw_succ M predecessorLevel).
      exact hlevel.
    + apply (proj2
        (raw_sat_dynamicTruthNativeCrossLevelSuccessorBodyGraph_iff M tail
          nextPiEvidence nextSigmaEvidence currentPiEvidence
          currentSigmaEvidence piDomain sigmaDomain currentLevelNumeral
          nextGlobalPi nextGlobalSigma currentLevel fieldCode
          currentGlobalSigma currentGlobalPi predecessorLevel)).
      apply (proj2
        (raw_sat_dynamicTruthPairedGlobalSuccessorGraph_iff M tail
          currentLevel currentGlobalSigma currentGlobalPi
          nextGlobalSigma nextGlobalPi)).
      exact hsuccessor.
    + apply (proj2 (raw_sat_numeralTermCodeAtTermAt_iff M _
        (tVar 9) (tVar 6))).
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
    + apply (proj2
        (raw_sat_dynamicTruthLocalTernaryApplicationTermAt_iff M _
          (tVar 11) (tVar 3))).
      cbn [raw_term_eval scons]. exact hcurrentSigma.
    + apply (proj2
        (raw_sat_dynamicTruthLocalTernaryApplicationTermAt_iff M _
          (tVar 12) (tVar 2))).
      cbn [raw_term_eval scons]. exact hcurrentPi.
    + apply (proj2
        (raw_sat_dynamicTruthLocalTernaryApplicationTermAt_iff M _
          (tVar 8) (tVar 1))).
      cbn [raw_term_eval scons]. exact hnextSigma.
    + apply (proj2
        (raw_sat_dynamicTruthLocalTernaryApplicationTermAt_iff M _
          (tVar 7) (tVar 0))).
      cbn [raw_term_eval scons]. exact hnextPi.
    + apply (proj2
        (raw_sat_dynamicTruthNativeCrossLevelCoherenceFieldCodeTermAt_iff M _
          (tVar 10) (tVar 5) (tVar 4) (tVar 3) (tVar 2)
          (tVar 1) (tVar 0))).
      cbn [raw_term_eval scons]. exact hfield.
Qed.

(** The transform exposes the genuine native Sigma-Or7/Pi-Or6 successor
    rows at current level [S p], rather than treating the next predicates as
    unrelated opaque codes. *)
Theorem raw_dynamicTruthNativeCrossLevelFieldTransformAt_exposes_rows :
  forall (M : RawPAModel) currentGlobalSigma currentGlobalPi
      predecessorLevel fieldCode,
  RawDynamicTruthNativeCrossLevelFieldTransformAt M
    currentGlobalSigma currentGlobalPi predecessorLevel fieldCode ->
  exists currentLevel nextGlobalSigma nextGlobalPi
      localSigmaRow localPiRow : M,
    currentLevel = raw_succ M predecessorLevel /\
    RawDynamicTruthPairedSuccessorRowAt M
      currentGlobalSigma currentGlobalPi currentLevel
      localSigmaRow localPiRow /\
    RawDynamicTruthPairedGlobalWrapperAt M
      localSigmaRow localPiRow nextGlobalSigma nextGlobalPi.
Proof.
  intros M currentGlobalSigma currentGlobalPi predecessorLevel fieldCode
    (currentLevel & nextGlobalSigma & nextGlobalPi &
     currentLevelNumeral & sigmaDomain & piDomain & currentSigmaEvidence &
     currentPiEvidence & nextSigmaEvidence & nextPiEvidence & hlevel &
     hsuccessor & _).
  destruct hsuccessor as
    [localSigmaRow [localPiRow [hrows hwrapper]]].
  exists currentLevel, nextGlobalSigma, nextGlobalPi,
    localSigmaRow, localPiRow.
  split; [exact hlevel |].
  split; [exact hrows | exact hwrapper].
Qed.

Corollary
    raw_dynamicTruthNativeCrossLevelFieldTransformAt_row_code_polynomials :
  forall (M : RawPAModel) currentGlobalSigma currentGlobalPi
      predecessorLevel fieldCode,
  RawDynamicTruthNativeCrossLevelFieldTransformAt M
    currentGlobalSigma currentGlobalPi predecessorLevel fieldCode ->
  exists currentLevel localSigmaRow localPiRow
      sigmaNumeral sigmaDomain sigmaLowerApplication
      piNumeral piDomain piLowerApplication : M,
    currentLevel = raw_succ M predecessorLevel /\
    RawNumeralTermCodeAt M (raw_succ M currentLevel) sigmaNumeral /\
    RawCodedFormulaSingleSubstitution M sigmaNumeral
      (rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode)
      sigmaDomain /\
    RawDynamicTruthCoqLowerApplication M
      currentGlobalPi sigmaLowerApplication /\
    localSigmaRow = rawDynamicTruthSigmaSuccessorRowCode M
      sigmaDomain sigmaLowerApplication /\
    RawNumeralTermCodeAt M (raw_succ M currentLevel) piNumeral /\
    RawCodedFormulaSingleSubstitution M piNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthPiRowDomainTemplate)) piDomain /\
    RawDynamicTruthPiCoqLowerApplication M
      currentGlobalSigma piLowerApplication /\
    localPiRow = rawDynamicTruthPiSuccessorRowCode M
      piDomain piLowerApplication.
Proof.
  intros M currentGlobalSigma currentGlobalPi predecessorLevel fieldCode h.
  destruct (raw_dynamicTruthNativeCrossLevelFieldTransformAt_exposes_rows
    M currentGlobalSigma currentGlobalPi predecessorLevel fieldCode h) as
    (currentLevel & nextGlobalSigma & nextGlobalPi &
     localSigmaRow & localPiRow & hlevel & [hsigma hpi] & _).
  destruct hsigma as
    (sigmaNumeral & sigmaDomain & sigmaLowerApplication &
     hsigmaNumeral & hsigmaDomain & hsigmaLower & hsigmaRow).
  destruct hpi as
    (piNumeral & piDomain & piLowerApplication &
     hpiNumeral & hpiDomain & hpiLower & hpiRow).
  exists currentLevel, localSigmaRow, localPiRow,
    sigmaNumeral, sigmaDomain, sigmaLowerApplication,
    piNumeral, piDomain, piLowerApplication.
  repeat split; assumption.
Qed.

(** ------------------------------------------------------------------
    Adequacy-preserving relational totality of the transform. *)

Definition RawDynamicTruthNativeCrossLevelFieldTransformTotalOnAdequate
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) currentGlobalSigma currentGlobalPi
      predecessorLevel,
    RawCodedFormulaAtomicallyAdequate M currentGlobalSigma ->
    RawCodedFormulaAtomicallyAdequate M currentGlobalPi ->
    exists fieldCode : M,
      raw_formula_sat M
        (scons M fieldCode (scons M currentGlobalSigma
          (scons M currentGlobalPi (scons M predecessorLevel tail))))
        dynamicTruthNativeCrossLevelFieldTransformGraph.

Arguments RawDynamicTruthNativeCrossLevelFieldTransformTotalOnAdequate M
  : clear implicits.

Theorem
    dynamicTruthNativeCrossLevelFieldTransformGraph_raw_total_on_adequate :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeCrossLevelFieldTransformTotalOnAdequate M.
Proof.
  intros M hPA tail currentGlobalSigma currentGlobalPi predecessorLevel
    hcurrentSigmaAdequate hcurrentPiAdequate.
  set (currentLevel := raw_succ M predecessorLevel).
  destruct (dynamicTruthPairedGlobalSuccessorGraph_raw_adequate_total
    M hPA tail currentLevel currentGlobalSigma currentGlobalPi
    hcurrentSigmaAdequate hcurrentPiAdequate) as
    (nextGlobalSigma & nextGlobalPi & hsuccessor &
     hnextSigmaAdequate & hnextPiAdequate).
  pose proof (proj1
    (raw_sat_dynamicTruthPairedGlobalSuccessorGraph_iff M tail currentLevel
      currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi)
    hsuccessor) as hsuccessorAt.
  destruct (raw_numeralTermCodeExists_all M hPA currentLevel) as
    [currentLevelNumeral hcurrentLevelNumeral].
  destruct (raw_dynamicTruthLocalInputDomain_exists_adequate
    M hPA currentLevel currentLevelNumeral
    dynamicTruthLocalSigmaInputDomainTemplate hcurrentLevelNumeral) as
    (sigmaDomain & hsigmaDomain & _hsigmaDomainAdequate).
  destruct (raw_dynamicTruthLocalInputDomain_exists_adequate
    M hPA currentLevel currentLevelNumeral
    dynamicTruthLocalPiInputDomainTemplate hcurrentLevelNumeral) as
    (piDomain & hpiDomain & _hpiDomainAdequate).
  destruct (raw_dynamicTruthLocalTernaryApplication_exists_adequate
    M hPA currentGlobalSigma hcurrentSigmaAdequate) as
    (currentSigmaEvidence & hcurrentSigma & _hcurrentSigmaEvidenceAdequate).
  destruct (raw_dynamicTruthLocalTernaryApplication_exists_adequate
    M hPA currentGlobalPi hcurrentPiAdequate) as
    (currentPiEvidence & hcurrentPi & _hcurrentPiEvidenceAdequate).
  destruct (raw_dynamicTruthLocalTernaryApplication_exists_adequate
    M hPA nextGlobalSigma hnextSigmaAdequate) as
    (nextSigmaEvidence & hnextSigma & _hnextSigmaEvidenceAdequate).
  destruct (raw_dynamicTruthLocalTernaryApplication_exists_adequate
    M hPA nextGlobalPi hnextPiAdequate) as
    (nextPiEvidence & hnextPi & _hnextPiEvidenceAdequate).
  exists (rawDynamicTruthNativeCrossLevelCoherenceFieldCode M
    sigmaDomain piDomain currentSigmaEvidence currentPiEvidence
    nextSigmaEvidence nextPiEvidence).
  apply (proj2
    (raw_sat_dynamicTruthNativeCrossLevelFieldTransformGraph_iff M tail
      currentGlobalSigma currentGlobalPi predecessorLevel _)).
  exists currentLevel, nextGlobalSigma, nextGlobalPi,
    currentLevelNumeral, sigmaDomain, piDomain, currentSigmaEvidence,
    currentPiEvidence, nextSigmaEvidence, nextPiEvidence.
  split; [unfold currentLevel; reflexivity |].
  split; [exact hsuccessorAt |].
  split; [exact hcurrentLevelNumeral |].
  split; [exact hsigmaDomain |].
  split; [exact hpiDomain |].
  split; [exact hcurrentSigma |].
  split; [exact hcurrentPi |].
  split; [exact hnextSigma |].
  split; [exact hnextPi | reflexivity].
Qed.

(** ------------------------------------------------------------------
    Output-first composition with the genuine current-level orbit. *)

Definition dynamicTruthNativeCrossLevelPositiveGraph : formula :=
  outputFirstPairedFormulaGraphComposition
    dynamicTruthNativeCrossLevelInputOrbitGraph
    dynamicTruthNativeCrossLevelFieldTransformGraph.

Definition RawDynamicTruthNativeCrossLevelPositiveAt
    (M : RawPAModel) (tail : nat -> M)
    (predecessorLevel fieldCode : M) : Prop :=
  exists currentGlobalSigma currentGlobalPi : M,
    RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
      tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi /\
    RawDynamicTruthNativeCrossLevelFieldTransformAt M
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode.

Arguments RawDynamicTruthNativeCrossLevelPositiveAt
  M tail predecessorLevel fieldCode : clear implicits.

Theorem raw_sat_dynamicTruthNativeCrossLevelPositiveGraph_iff : forall
    (M : RawPAModel) tail predecessorLevel fieldCode,
  raw_formula_sat M
    (scons M fieldCode (scons M predecessorLevel tail))
    dynamicTruthNativeCrossLevelPositiveGraph <->
  RawDynamicTruthNativeCrossLevelPositiveAt M
    tail predecessorLevel fieldCode.
Proof.
  intros M tail predecessorLevel fieldCode.
  unfold dynamicTruthNativeCrossLevelPositiveGraph,
    RawDynamicTruthNativeCrossLevelPositiveAt.
  rewrite raw_sat_outputFirstPairedFormulaGraphComposition_iff.
  unfold RawOutputFirstPairedFormulaGraphCompositionAt.
  split.
  - intros (currentGlobalSigma & currentGlobalPi & horbit & htransform).
    exists currentGlobalSigma, currentGlobalPi. split.
    + apply (proj1
        (raw_sat_dynamicTruthNativeCrossLevelInputOrbitGraph_iff M tail
          predecessorLevel currentGlobalSigma currentGlobalPi)).
      exact horbit.
    + apply (proj1
        (raw_sat_dynamicTruthNativeCrossLevelFieldTransformGraph_iff M tail
          currentGlobalSigma currentGlobalPi predecessorLevel fieldCode)).
      exact htransform.
  - intros (currentGlobalSigma & currentGlobalPi & horbit & htransform).
    exists currentGlobalSigma, currentGlobalPi. split.
    + apply (proj2
        (raw_sat_dynamicTruthNativeCrossLevelInputOrbitGraph_iff M tail
          predecessorLevel currentGlobalSigma currentGlobalPi)).
      exact horbit.
    + apply (proj2
        (raw_sat_dynamicTruthNativeCrossLevelFieldTransformGraph_iff M tail
          currentGlobalSigma currentGlobalPi predecessorLevel fieldCode)).
      exact htransform.
Qed.

Definition RawDynamicTruthNativeCrossLevelPositiveTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel,
    exists fieldCode : M,
      raw_formula_sat M
        (scons M fieldCode (scons M predecessorLevel tail))
        dynamicTruthNativeCrossLevelPositiveGraph.

Arguments RawDynamicTruthNativeCrossLevelPositiveTotal M : clear implicits.

Theorem dynamicTruthNativeCrossLevelPositiveGraph_raw_total :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeCrossLevelPositiveTotal M.
Proof.
  intros M hPA tail predecessorLevel.
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail (raw_succ M predecessorLevel)) as
    (currentGlobalSigma & currentGlobalPi & horbit &
     hcurrentSigmaAdequate & hcurrentPiAdequate).
  destruct
    (dynamicTruthNativeCrossLevelFieldTransformGraph_raw_total_on_adequate
      M hPA tail currentGlobalSigma currentGlobalPi predecessorLevel
      hcurrentSigmaAdequate hcurrentPiAdequate) as [fieldCode htransform].
  exists fieldCode.
  apply (proj2 (raw_sat_dynamicTruthNativeCrossLevelPositiveGraph_iff
    M tail predecessorLevel fieldCode)).
  exists currentGlobalSigma, currentGlobalPi. split.
  - apply (proj1
      (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M tail
        (raw_succ M predecessorLevel)
        currentGlobalSigma currentGlobalPi)).
    exact horbit.
  - apply (proj1
      (raw_sat_dynamicTruthNativeCrossLevelFieldTransformGraph_iff M tail
        currentGlobalSigma currentGlobalPi predecessorLevel fieldCode)).
    exact htransform.
Qed.

(** ------------------------------------------------------------------
    Exact remaining object-proof compiler seam.

    The theorem [raw_fixedLevelCrossLevelCoherence_quoted_proof] above
    discharges every externally fixed standard level.  It cannot be applied
    to a nonstandard [predecessorLevel : M].  The following premise asks only
    for the missing uniform compiler on the exact adequate orbit and exact
    transform trace.  In particular it does not assume semantic validity and
    does not turn model truth into a represented PA proof. *)

Definition RawDynamicTruthNativeCrossLevelCoherenceProofCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi fieldCode,
    RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi ->
    RawDynamicTruthNativeCrossLevelFieldTransformAt M
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode ->
    exists certificate : M,
      RawCodedPAProofOf M fieldCode certificate.

Arguments RawDynamicTruthNativeCrossLevelCoherenceProofCompiler M
  : clear implicits.

Definition RawDynamicTruthNativeCrossLevelPositiveProofTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel,
    exists fieldCode certificate : M,
      raw_formula_sat M
        (scons M fieldCode (scons M predecessorLevel tail))
        dynamicTruthNativeCrossLevelPositiveGraph /\
      RawCodedPAProofOf M fieldCode certificate.

Arguments RawDynamicTruthNativeCrossLevelPositiveProofTotal M
  : clear implicits.

Theorem
    dynamicTruthNativeCrossLevelPositiveGraph_raw_proof_total_of_compiler :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeCrossLevelCoherenceProofCompiler M ->
  RawDynamicTruthNativeCrossLevelPositiveProofTotal M.
Proof.
  intros M hPA hcompiler tail predecessorLevel.
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail (raw_succ M predecessorLevel)) as
    (currentGlobalSigma & currentGlobalPi & horbit &
     hcurrentSigmaAdequate & hcurrentPiAdequate).
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
    (dynamicTruthNativeCrossLevelFieldTransformGraph_raw_total_on_adequate
      M hPA tail currentGlobalSigma currentGlobalPi predecessorLevel
      hcurrentSigmaAdequate hcurrentPiAdequate) as [fieldCode htransformSat].
  pose proof (proj1
    (raw_sat_dynamicTruthNativeCrossLevelFieldTransformGraph_iff M tail
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode)
    htransformSat) as htransform.
  destruct (hcompiler tail predecessorLevel currentGlobalSigma
    currentGlobalPi fieldCode hadequateOrbit htransform) as
    [certificate hcertificate].
  exists fieldCode, certificate. split; [|exact hcertificate].
  apply (proj2 (raw_sat_dynamicTruthNativeCrossLevelPositiveGraph_iff
    M tail predecessorLevel fieldCode)).
  exists currentGlobalSigma, currentGlobalPi. split.
  - apply (proj1
      (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M tail
        (raw_succ M predecessorLevel)
        currentGlobalSigma currentGlobalPi)).
    exact hadequateOrbit.
  - exact htransform.
Qed.

End PABoundedRawCodedDynamicTruthNativeCrossLevelPositiveGraph.
