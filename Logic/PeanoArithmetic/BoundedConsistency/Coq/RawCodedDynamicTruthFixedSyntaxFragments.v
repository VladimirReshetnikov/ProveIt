(**
  Fixed syntax fragments for a carrier-indexed partial-truth successor.

  The Lean development represents a local truth state by an HFS record and
  tests membership of that record in one HFS certificate.  The Rocq
  development uses a different, already established certificate format: the
  mode, formula code, assignment code, and assignment step are stored in four
  synchronized Goedel-beta tables.  Consequently the two developments have
  the same local state data and constructor cases, but their concrete record
  and certificate codes are intentionally not identified.

  This module names the exact Rocq counterparts needed by a future dynamic
  successor graph.  In particular, the rank-domain formula below accepts a
  *term-valued* level, rather than the metatheoretic [nat] used by
  [fixedLevelSigmaDomainTermAt].  It therefore remains meaningful when the
  level is a nonstandard element of a model of PA.

  Variable-order correspondence for the base truth predicate is

      Lean: bound environment, free environment, formula code
      Rocq: formula code, assignment beta code, assignment beta step.

  Rocq combines the two Lean environments into one beta-coded de Bruijn
  assignment.  The final two arguments are the two components of that
  assignment, not two independent environments.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedFormulaRankStep RawCodedFormulaRankTraversal
  RawCodedRankZeroTruthTraversal RawCodedFixedLevelTruth
  RawCodedDynamicLocalFieldGraph RawCodedStandardClosedFormulaCodeGraph
  RawCodedDynamicTruthTernaryApplicationGraph.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthFixedSyntaxFragments.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedRankZeroTruthTraversal.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedDynamicLocalFieldGraph.
Import PABoundedRawCodedStandardClosedFormulaCodeGraph.
Import PABoundedRawCodedDynamicTruthTernaryApplicationGraph.

(** ------------------------------------------------------------------
    A fixed ternary formula for level-zero truth. *)

Definition dynamicTruthBaseTernaryFormula : formula :=
  fixedLevelSigmaZeroTermAt (tVar 0) (tVar 1) (tVar 2).

Definition RawDynamicTruthBase (M : RawPAModel)
    (code assignmentCode assignmentStep : M) : Prop :=
  RawFixedLevelSigmaZero M code assignmentCode assignmentStep.

Arguments RawDynamicTruthBase M code assignmentCode assignmentStep
  : clear implicits.

(** Exact semantics holds in every raw arithmetic structure; PA laws are not
    needed merely to read the represented predicate. *)
Theorem raw_sat_dynamicTruthBaseTernaryFormula_iff : forall
    (M : RawPAModel) tail code assignmentCode assignmentStep,
  raw_formula_sat M
    (scons M code (scons M assignmentCode (scons M assignmentStep tail)))
    dynamicTruthBaseTernaryFormula <->
  RawDynamicTruthBase M code assignmentCode assignmentStep.
Proof.
  intros M tail code assignmentCode assignmentStep.
  unfold dynamicTruthBaseTernaryFormula, RawDynamicTruthBase.
  rewrite raw_sat_fixedLevelSigmaZeroTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition DynamicTruthBaseTernaryScoped : Prop :=
  forall index, Formula.Free index dynamicTruthBaseTernaryFormula -> index < 3.

(** This syntactic check is deliberately stated independently of semantics:
    the represented ternary-application graph may therefore substitute into
    the base predicate without assuming anything about the ambient model. *)
Theorem dynamicTruthBaseTernaryFormula_scoped :
  DynamicTruthBaseTernaryScoped.
Proof.
  intros index hfree.
  vm_compute in hfree.
  lia.
Qed.

Corollary dynamicTruthBaseTernaryFormula_application_scoped :
  DynamicTruthTernaryScoped dynamicTruthBaseTernaryFormula.
Proof.
  exact dynamicTruthBaseTernaryFormula_scoped.
Qed.

(** The existing represented three-substitution graph can therefore apply
    the concrete base formula at the successor branch's variables
    [#4], [#3], and [#0], with literal quoted syntax as its output. *)
Corollary dynamicTruthBaseTernaryApplicationGraph_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail,
  raw_formula_sat M
    (scons M
      (rawQuotedFormulaCode M
        (Formula.rename dynamicTruthTernaryApplicationRenaming
          dynamicTruthBaseTernaryFormula))
      (scons M
        (rawQuotedFormulaCode M dynamicTruthBaseTernaryFormula) tail))
    dynamicTruthTernaryApplicationGraph.
Proof.
  intros M hPA tail.
  apply dynamicTruthTernaryApplicationGraph_standard_rename;
    [exact hPA |].
  exact dynamicTruthBaseTernaryFormula_application_scoped.
Qed.

(** The canonical fully closed version is useful whenever an ordinary PA
    sentence, rather than a ternary predicate, must be quoted.  [sealPA]
    closes precisely the metatheoretic free-variable bound of the formula. *)
Definition dynamicTruthBaseClosedFormula : formula :=
  Formula.sealPA dynamicTruthBaseTernaryFormula.

Theorem dynamicTruthBaseClosedFormula_sentence :
  Formula.Sentence dynamicTruthBaseClosedFormula.
Proof.
  unfold dynamicTruthBaseClosedFormula.
  apply Formula.sealPA_sentence.
Qed.

(** ------------------------------------------------------------------
    Carrier-level rank domains.

    These are the term-parametric analogues of the externally indexed
    [fixedLevelSigmaDomainTermAt] and [fixedLevelPiDomainTermAt]. *)

Definition dynamicTruthSigmaRecordDomainTermAt
    (upperLevel code : term) : formula :=
  fixedLevelEx2
    (pAnd
      (codedFormulaRankTermAt
        (liftTerm 2 code) (tVar 1) (tVar 0))
      (Formula.leTermAt (tVar 1) (liftTerm 2 upperLevel))).

Definition dynamicTruthPiRecordDomainTermAt
    (lowerLevel code : term) : formula :=
  fixedLevelEx2
    (pAnd
      (codedFormulaRankTermAt
        (liftTerm 2 code) (tVar 1) (tVar 0))
      (Formula.leTermAt (tVar 0) (liftTerm 2 lowerLevel))).

Definition RawDynamicTruthSigmaRecordDomain (M : RawPAModel)
    (upperLevel code : M) : Prop :=
  exists sigma pi : M,
    RawCodedFormulaRank M code sigma pi /\ rawLe M sigma upperLevel.

Definition RawDynamicTruthPiRecordDomain (M : RawPAModel)
    (lowerLevel code : M) : Prop :=
  exists sigma pi : M,
    RawCodedFormulaRank M code sigma pi /\ rawLe M pi lowerLevel.

Arguments RawDynamicTruthSigmaRecordDomain M upperLevel code
  : clear implicits.
Arguments RawDynamicTruthPiRecordDomain M lowerLevel code
  : clear implicits.

Theorem raw_sat_dynamicTruthSigmaRecordDomainTermAt_iff : forall
    (M : RawPAModel) e upperLevel code,
  raw_formula_sat M e
    (dynamicTruthSigmaRecordDomainTermAt upperLevel code) <->
  RawDynamicTruthSigmaRecordDomain M
    (raw_term_eval M e upperLevel) (raw_term_eval M e code).
Proof.
  intros M e upperLevel code.
  unfold dynamicTruthSigmaRecordDomainTermAt, fixedLevelEx2,
    RawDynamicTruthSigmaRecordDomain.
  cbn [raw_formula_sat].
  split.
  - intros [sigma [pi [hrankSat hleSat]]].
    exists sigma, pi. split.
    + apply (proj1 (raw_sat_codedFormulaRankTermAt_iff M
        (scons M pi (scons M sigma e))
        (liftTerm 2 code) (tVar 1) (tVar 0))) in hrankSat.
      rewrite raw_fixedLevel_eval_liftTerm_two in hrankSat.
      cbn [raw_term_eval scons] in hrankSat. exact hrankSat.
    + apply (proj1 (raw_sat_leTermAt_iff_rank M
        (tVar 1) (liftTerm 2 upperLevel)
        (scons M pi (scons M sigma e)))) in hleSat.
      rewrite raw_fixedLevel_eval_liftTerm_two in hleSat.
      cbn [raw_term_eval scons] in hleSat. exact hleSat.
  - intros [sigma [pi [hrank hle]]].
    exists sigma, pi. split.
    + apply (proj2 (raw_sat_codedFormulaRankTermAt_iff M
        (scons M pi (scons M sigma e))
        (liftTerm 2 code) (tVar 1) (tVar 0))).
      rewrite raw_fixedLevel_eval_liftTerm_two.
      cbn [raw_term_eval scons]. exact hrank.
    + apply (proj2 (raw_sat_leTermAt_iff_rank M
        (tVar 1) (liftTerm 2 upperLevel)
        (scons M pi (scons M sigma e)))).
      rewrite raw_fixedLevel_eval_liftTerm_two.
      cbn [raw_term_eval scons]. exact hle.
Qed.

Theorem raw_sat_dynamicTruthPiRecordDomainTermAt_iff : forall
    (M : RawPAModel) e lowerLevel code,
  raw_formula_sat M e
    (dynamicTruthPiRecordDomainTermAt lowerLevel code) <->
  RawDynamicTruthPiRecordDomain M
    (raw_term_eval M e lowerLevel) (raw_term_eval M e code).
Proof.
  intros M e lowerLevel code.
  unfold dynamicTruthPiRecordDomainTermAt, fixedLevelEx2,
    RawDynamicTruthPiRecordDomain.
  cbn [raw_formula_sat].
  split.
  - intros [sigma [pi [hrankSat hleSat]]].
    exists sigma, pi. split.
    + apply (proj1 (raw_sat_codedFormulaRankTermAt_iff M
        (scons M pi (scons M sigma e))
        (liftTerm 2 code) (tVar 1) (tVar 0))) in hrankSat.
      rewrite raw_fixedLevel_eval_liftTerm_two in hrankSat.
      cbn [raw_term_eval scons] in hrankSat. exact hrankSat.
    + apply (proj1 (raw_sat_leTermAt_iff_rank M
        (tVar 0) (liftTerm 2 lowerLevel)
        (scons M pi (scons M sigma e)))) in hleSat.
      rewrite raw_fixedLevel_eval_liftTerm_two in hleSat.
      cbn [raw_term_eval scons] in hleSat. exact hleSat.
  - intros [sigma [pi [hrank hle]]].
    exists sigma, pi. split.
    + apply (proj2 (raw_sat_codedFormulaRankTermAt_iff M
        (scons M pi (scons M sigma e))
        (liftTerm 2 code) (tVar 1) (tVar 0))).
      rewrite raw_fixedLevel_eval_liftTerm_two.
      cbn [raw_term_eval scons]. exact hrank.
    + apply (proj2 (raw_sat_leTermAt_iff_rank M
        (tVar 0) (liftTerm 2 lowerLevel)
        (scons M pi (scons M sigma e)))).
      rewrite raw_fixedLevel_eval_liftTerm_two.
      cbn [raw_term_eval scons]. exact hle.
Qed.

(** ------------------------------------------------------------------
    State and certificate-membership fragments.

    [dynamicTruthStateTermAt] reads one row of the four synchronized tables.
    [dynamicTruthStateMemberTermAt] additionally requires its row index to be
    strictly earlier than the current row.  This is the exact table-based
    counterpart of Lean's [truthState] plus HFS certificate membership. *)

Definition dynamicTruthStateTermAt := fixedLevelStateLookupTermAt.
Definition RawDynamicTruthState := RawFixedLevelStateLookup.

Definition dynamicTruthStateMemberTermAt := fixedLevelEarlierStateTermAt.
Definition RawDynamicTruthStateMember := RawFixedLevelEarlierState.

Theorem raw_sat_dynamicTruthStateTermAt_iff : forall
    (M : RawPAModel) e
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    index mode code assignmentCode assignmentStep,
  raw_formula_sat M e
    (dynamicTruthStateTermAt
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      index mode code assignmentCode assignmentStep) <->
  RawDynamicTruthState M
    (raw_term_eval M e modeCode) (raw_term_eval M e modeStep)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e assignmentCodeCode)
    (raw_term_eval M e assignmentCodeStep)
    (raw_term_eval M e assignmentStepCode)
    (raw_term_eval M e assignmentStepStep)
    (raw_term_eval M e index) (raw_term_eval M e mode)
    (raw_term_eval M e code) (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep).
Proof.
  intros. unfold dynamicTruthStateTermAt, RawDynamicTruthState.
  apply raw_sat_fixedLevelStateLookupTermAt_iff.
Qed.

Theorem raw_sat_dynamicTruthStateMemberTermAt_iff : forall
    (M : RawPAModel) e
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex childIndex expectedMode childCode
    childAssignmentCode childAssignmentStep,
  raw_formula_sat M e
    (dynamicTruthStateMemberTermAt
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      currentIndex childIndex expectedMode childCode
      childAssignmentCode childAssignmentStep) <->
  RawDynamicTruthStateMember M
    (raw_term_eval M e modeCode) (raw_term_eval M e modeStep)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e assignmentCodeCode)
    (raw_term_eval M e assignmentCodeStep)
    (raw_term_eval M e assignmentStepCode)
    (raw_term_eval M e assignmentStepStep)
    (raw_term_eval M e currentIndex) (raw_term_eval M e childIndex)
    (raw_term_eval M e expectedMode) (raw_term_eval M e childCode)
    (raw_term_eval M e childAssignmentCode)
    (raw_term_eval M e childAssignmentStep).
Proof.
  intros. unfold dynamicTruthStateMemberTermAt,
    RawDynamicTruthStateMember.
  apply raw_sat_fixedLevelEarlierStateTermAt_iff.
Qed.

(** ------------------------------------------------------------------
    Lower-independent positive record branches.

    This is the table-based counterpart of Lean's quantifier-free,
    conjunction, disjunction, and existential alternatives.  A child-state
    "membership" is an earlier lookup in the synchronized state tables. *)

Definition dynamicTruthPositiveRecordBranchesTermAt
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      currentIndex code assignmentCode assignmentStep
      leftIndex leftCode rightIndex rightCode
      witness newAssignmentCode newAssignmentStep : term) : formula :=
  pOr
    (rankZeroTruthCertificateTermAt
      code (Term.numeral 1) assignmentCode assignmentStep)
    (pOr
      (fixedLevelAnd3
        (formulaAndCodeTermAt code leftCode rightCode)
        (dynamicTruthStateMemberTermAt
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          currentIndex leftIndex tZero leftCode
          assignmentCode assignmentStep)
        (dynamicTruthStateMemberTermAt
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          currentIndex rightIndex tZero rightCode
          assignmentCode assignmentStep))
      (pOr
        (pAnd
          (formulaOrCodeTermAt code leftCode rightCode)
          (pOr
            (dynamicTruthStateMemberTermAt
              modeCode modeStep formulaCode formulaStep
              assignmentCodeCode assignmentCodeStep
              assignmentStepCode assignmentStepStep
              currentIndex leftIndex tZero leftCode
              assignmentCode assignmentStep)
            (dynamicTruthStateMemberTermAt
              modeCode modeStep formulaCode formulaStep
              assignmentCodeCode assignmentCodeStep
              assignmentStepCode assignmentStepStep
              currentIndex rightIndex tZero rightCode
              assignmentCode assignmentStep)))
        (fixedLevelAnd3
          (formulaExCodeTermAt code leftCode)
          (codedAssignmentPrependTermAt
            assignmentCode assignmentStep witness code
            newAssignmentCode newAssignmentStep)
          (dynamicTruthStateMemberTermAt
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            currentIndex leftIndex tZero leftCode
            newAssignmentCode newAssignmentStep)))).

Definition RawDynamicTruthPositiveRecordBranches (M : RawPAModel)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      currentIndex code assignmentCode assignmentStep
      leftIndex leftCode rightIndex rightCode
      witness newAssignmentCode newAssignmentStep : M) : Prop :=
  RawRankZeroTruthCertificate M code (rawNumeralValue M 1)
      assignmentCode assignmentStep \/
  (code = rawFormulaAndCode M leftCode rightCode /\
    RawDynamicTruthStateMember M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      currentIndex leftIndex (raw_zero M) leftCode
      assignmentCode assignmentStep /\
    RawDynamicTruthStateMember M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      currentIndex rightIndex (raw_zero M) rightCode
      assignmentCode assignmentStep) \/
  (code = rawFormulaOrCode M leftCode rightCode /\
    (RawDynamicTruthStateMember M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      currentIndex leftIndex (raw_zero M) leftCode
      assignmentCode assignmentStep \/
     RawDynamicTruthStateMember M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      currentIndex rightIndex (raw_zero M) rightCode
      assignmentCode assignmentStep)) \/
  (code = rawFormulaExCode M leftCode /\
    RawCodedAssignmentPrepend M assignmentCode assignmentStep witness code
      newAssignmentCode newAssignmentStep /\
    RawDynamicTruthStateMember M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      currentIndex leftIndex (raw_zero M) leftCode
      newAssignmentCode newAssignmentStep).

Arguments RawDynamicTruthPositiveRecordBranches
  M modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep
    leftIndex leftCode rightIndex rightCode
    witness newAssignmentCode newAssignmentStep : clear implicits.

Theorem raw_sat_dynamicTruthPositiveRecordBranchesTermAt_iff : forall
    (M : RawPAModel) e
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep
    leftIndex leftCode rightIndex rightCode
    witness newAssignmentCode newAssignmentStep,
  raw_formula_sat M e
    (dynamicTruthPositiveRecordBranchesTermAt
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      currentIndex code assignmentCode assignmentStep
      leftIndex leftCode rightIndex rightCode
      witness newAssignmentCode newAssignmentStep) <->
  RawDynamicTruthPositiveRecordBranches M
    (raw_term_eval M e modeCode) (raw_term_eval M e modeStep)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e assignmentCodeCode)
    (raw_term_eval M e assignmentCodeStep)
    (raw_term_eval M e assignmentStepCode)
    (raw_term_eval M e assignmentStepStep)
    (raw_term_eval M e currentIndex) (raw_term_eval M e code)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep)
    (raw_term_eval M e leftIndex) (raw_term_eval M e leftCode)
    (raw_term_eval M e rightIndex) (raw_term_eval M e rightCode)
    (raw_term_eval M e witness) (raw_term_eval M e newAssignmentCode)
    (raw_term_eval M e newAssignmentStep).
Proof.
  intros.
  unfold dynamicTruthPositiveRecordBranchesTermAt,
    RawDynamicTruthPositiveRecordBranches, fixedLevelAnd3,
    dynamicTruthStateMemberTermAt, RawDynamicTruthStateMember.
  cbn [raw_formula_sat].
  rewrite raw_sat_rankZeroTruthCertificateTermAt_iff,
    raw_sat_formulaAndCodeTermAt_iff,
    raw_sat_formulaOrCodeTermAt_iff,
    raw_sat_formulaExCodeTermAt_iff,
    !raw_sat_fixedLevelEarlierStateTermAt_iff,
    raw_sat_codedAssignmentPrependTermAt_iff,
    raw_term_eval_numeral.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Universal-leaf prefix and lower-evidence application.

    In Lean the universal leaf negates an application of the lower Sigma
    formula to the negated universal code.  Rocq carries positive evidence
    for *Pi falsity* instead.  Thus its definitionally equivalent local test
    says that no binder extension supplies lower Pi-falsity evidence for the
    universal body. *)

Definition dynamicTruthUniversalPrefixTermAt
    (code child : term) : formula :=
  formulaAllCodeTermAt code child.

Definition RawDynamicTruthUniversalPrefix (M : RawPAModel)
    (code child : M) : Prop :=
  code = rawFormulaAllCode M child.

Arguments RawDynamicTruthUniversalPrefix M code child : clear implicits.

Theorem raw_sat_dynamicTruthUniversalPrefixTermAt_iff : forall
    (M : RawPAModel) e code child,
  raw_formula_sat M e
    (dynamicTruthUniversalPrefixTermAt code child) <->
  RawDynamicTruthUniversalPrefix M
    (raw_term_eval M e code) (raw_term_eval M e child).
Proof.
  intros M e code child.
  unfold dynamicTruthUniversalPrefixTermAt,
    RawDynamicTruthUniversalPrefix.
  apply raw_sat_formulaAllCodeTermAt_iff.
Qed.

Definition dynamicTruthUniversalLowerApplicationTermAt
    (lowerPiEvidence : formula)
    (assignmentCode assignmentStep bound : term) : formula :=
  fixedLevelNoBinderCounterexampleTermAt lowerPiEvidence
    assignmentCode assignmentStep bound.

Definition RawDynamicTruthUniversalLowerApplication (M : RawPAModel)
    (lowerPiEvidence : M -> M -> M -> Prop)
    (assignmentCode assignmentStep bound : M) : Prop :=
  RawFixedLevelNoBinderCounterexample M lowerPiEvidence
    assignmentCode assignmentStep bound.

Arguments RawDynamicTruthUniversalLowerApplication
  M lowerPiEvidence assignmentCode assignmentStep bound : clear implicits.

Theorem raw_sat_dynamicTruthUniversalLowerApplicationTermAt_iff : forall
    (M : RawPAModel) e lowerPiEvidence
    assignmentCode assignmentStep bound,
  raw_formula_sat M e
    (dynamicTruthUniversalLowerApplicationTermAt lowerPiEvidence
      assignmentCode assignmentStep bound) <->
  RawDynamicTruthUniversalLowerApplication M
    (fun binderWitness binderAssignmentCode binderAssignmentStep =>
      raw_formula_sat M
        (scons M binderAssignmentStep
          (scons M binderAssignmentCode (scons M binderWitness e)))
        lowerPiEvidence)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep)
    (raw_term_eval M e bound).
Proof.
  intros M e lowerPiEvidence assignmentCode assignmentStep bound.
  unfold dynamicTruthUniversalLowerApplicationTermAt,
    RawDynamicTruthUniversalLowerApplication.
  apply raw_sat_fixedLevelNoBinderCounterexampleTermAt_iff.
Qed.

Definition dynamicTruthUniversalLeafTermAt
    (lowerPiEvidence : formula)
    (code child assignmentCode assignmentStep : term) : formula :=
  pAnd
    (dynamicTruthUniversalPrefixTermAt code child)
    (dynamicTruthUniversalLowerApplicationTermAt lowerPiEvidence
      assignmentCode assignmentStep code).

Definition RawDynamicTruthUniversalLeaf (M : RawPAModel)
    (lowerPiEvidence : M -> M -> M -> Prop)
    (code child assignmentCode assignmentStep : M) : Prop :=
  RawDynamicTruthUniversalPrefix M code child /\
  RawDynamicTruthUniversalLowerApplication M lowerPiEvidence
    assignmentCode assignmentStep code.

Arguments RawDynamicTruthUniversalLeaf
  M lowerPiEvidence code child assignmentCode assignmentStep : clear implicits.

Theorem raw_sat_dynamicTruthUniversalLeafTermAt_iff : forall
    (M : RawPAModel) e lowerPiEvidence
    code child assignmentCode assignmentStep,
  raw_formula_sat M e
    (dynamicTruthUniversalLeafTermAt lowerPiEvidence
      code child assignmentCode assignmentStep) <->
  RawDynamicTruthUniversalLeaf M
    (fun binderWitness binderAssignmentCode binderAssignmentStep =>
      raw_formula_sat M
        (scons M binderAssignmentStep
          (scons M binderAssignmentCode (scons M binderWitness e)))
        lowerPiEvidence)
    (raw_term_eval M e code) (raw_term_eval M e child)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep).
Proof.
  intros M e lowerPiEvidence code child assignmentCode assignmentStep.
  unfold dynamicTruthUniversalLeafTermAt,
    RawDynamicTruthUniversalLeaf.
  cbn [raw_formula_sat].
  rewrite raw_sat_dynamicTruthUniversalPrefixTermAt_iff,
    raw_sat_dynamicTruthUniversalLowerApplicationTermAt_iff.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Standard quoted code and output-first base graph. *)

Definition dynamicTruthBaseFormulaCodeGraph : formula :=
  standardClosedFormulaCodeGraph dynamicTruthBaseTernaryFormula.

Theorem dynamicTruthBase_quotedCode_standard : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawQuotedFormulaCode M dynamicTruthBaseTernaryFormula =
  rawNumeralValue M (formulaCode dynamicTruthBaseTernaryFormula).
Proof.
  intros M hPA.
  apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

Theorem dynamicTruthBaseFormulaCodeGraph_representation : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail level output,
  raw_formula_sat M (scons M output (scons M level tail))
    dynamicTruthBaseFormulaCodeGraph <->
  output = rawQuotedFormulaCode M dynamicTruthBaseTernaryFormula.
Proof.
  intros M hPA tail level output.
  unfold dynamicTruthBaseFormulaCodeGraph.
  exact (standardClosedFormulaCodeGraph_representation
    M hPA dynamicTruthBaseTernaryFormula tail level output).
Qed.

Theorem dynamicTruthBaseFormulaCodeGraph_raw_total : forall
    (M : RawPAModel) tail level,
  exists output : M,
    raw_formula_sat M (scons M output (scons M level tail))
      dynamicTruthBaseFormulaCodeGraph.
Proof.
  intros M tail level.
  unfold dynamicTruthBaseFormulaCodeGraph.
  apply standardClosedFormulaCodeGraph_raw_total.
Qed.

Corollary dynamicTruthBaseFormulaCodeGraph_dynamic_base_total : forall
    (M : RawPAModel),
  RawDynamicLocalBaseGraphTotal M dynamicTruthBaseFormulaCodeGraph.
Proof.
  intros M tail.
  exact (dynamicTruthBaseFormulaCodeGraph_raw_total
    M tail (raw_zero M)).
Qed.

Theorem dynamicTruthBaseFormulaCodeGraph_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail output,
  raw_formula_sat M
    (scons M output (scons M (raw_zero M) tail))
    dynamicTruthBaseFormulaCodeGraph <->
  output = rawQuotedFormulaCode M dynamicTruthBaseTernaryFormula.
Proof.
  intros M hPA tail output.
  exact (dynamicTruthBaseFormulaCodeGraph_representation
    M hPA tail (raw_zero M) output).
Qed.

End PABoundedRawCodedDynamicTruthFixedSyntaxFragments.
