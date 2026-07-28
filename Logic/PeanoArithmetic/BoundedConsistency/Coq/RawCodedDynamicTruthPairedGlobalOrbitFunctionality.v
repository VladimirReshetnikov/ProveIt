(**
  Functionality of the paired global dynamic-truth successor and orbit.

  The positive native field graphs all select the paired global orbit
  independently.  Totality alone therefore does not justify treating their
  hidden Sigma/Pi pairs as one common truth predicate.  This file proves the
  missing relational determinism without decoding carrier elements and
  without assuming any proof-producing or soundness interface.

  There are two genuinely nonstandard steps.  First, numeral-term codes and
  formula substitutions are functional at arbitrary carrier values by their
  existing represented-induction theorems.  Second, orbit functionality is
  itself propagated through every carrier level by [raw_definable_induction].
  The final coherence theorem then rewrites the five independently exposed
  positive-field orbit pairs to one adequate common pair.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedFormulaOperationCrossTraceFunctionality
  RawCodedDynamicTruthTemplateDirectInputs
  RawCodedDynamicTruthPiTemplateDirectInputs
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPairedSuccessorRowGraph
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeCrossLevelPositiveGraph
  RawCodedDynamicTruthNativeShiftPositiveGraph
  RawCodedDynamicTruthNativeSubstitutionPositiveGraph
  RawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph.

Module PABoundedRawCodedDynamicTruthPairedGlobalOrbitFunctionality.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedFormulaOperationCrossTraceFunctionality.
Import PABoundedRawCodedDynamicTruthTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthPiTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthPairedSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeShiftPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph.

(** ------------------------------------------------------------------
    Determinism of one paired global successor. *)

(** Both base outputs are transparent constructor polynomials in the two
    fixed rank-zero rows, so the base relation is functional without a PA
    hypothesis. *)
Lemma raw_dynamicTruthPairedGlobalBaseAt_functional : forall
    (M : RawPAModel) firstSigma firstPi secondSigma secondPi,
  RawDynamicTruthPairedGlobalBaseAt M firstSigma firstPi ->
  RawDynamicTruthPairedGlobalBaseAt M secondSigma secondPi ->
  firstSigma = secondSigma /\ firstPi = secondPi.
Proof.
  intros M firstSigma firstPi secondSigma secondPi hfirst hsecond.
  unfold RawDynamicTruthPairedGlobalBaseAt,
    RawDynamicTruthPairedGlobalWrapperAt in hfirst, hsecond.
  destruct hfirst as [hfirstSigma hfirstPi].
  destruct hsecond as [hsecondSigma hsecondPi].
  split; congruence.
Qed.

(** The Sigma row contains three witnesses.  The numeral witness is unique
    by represented induction, and both subsequent syntax operations are
    functional on arbitrary model elements. *)
Lemma raw_dynamicTruthSigmaSuccessorRowAt_functional : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      previousPi lowerLevel firstNext secondNext,
  RawDynamicTruthSigmaSuccessorRowAt M
    previousPi lowerLevel firstNext ->
  RawDynamicTruthSigmaSuccessorRowAt M
    previousPi lowerLevel secondNext ->
  firstNext = secondNext.
Proof.
  intros M hPA previousPi lowerLevel firstNext secondNext
    (firstNumeral & firstDomain & firstLower &
      hfirstNumeral & hfirstDomain & hfirstLower & hfirstNext)
    (secondNumeral & secondDomain & secondLower &
      hsecondNumeral & hsecondDomain & hsecondLower & hsecondNext).
  pose proof (raw_numeralTermCodeAt_functional M hPA
    (raw_succ M lowerLevel) firstNumeral secondNumeral
    hfirstNumeral hsecondNumeral) as hnumeral.
  subst secondNumeral.
  pose proof (raw_codedFormulaSingleSubstitution_functional M hPA
    firstNumeral
    (rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode)
    firstDomain secondDomain hfirstDomain hsecondDomain) as hdomain.
  pose proof (raw_dynamicTruthCoqLowerApplication_functional M hPA
    previousPi firstLower secondLower hfirstLower hsecondLower) as hlower.
  rewrite hfirstNext, hsecondNext, hdomain, hlower.
  reflexivity.
Qed.

(** The Pi row has the same witness pattern, using its polarity-specific
    lower-application functionality theorem. *)
Lemma raw_dynamicTruthPiSuccessorRowAt_functional : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      previousSigma lowerLevel firstNext secondNext,
  RawDynamicTruthPiSuccessorRowAt M
    previousSigma lowerLevel firstNext ->
  RawDynamicTruthPiSuccessorRowAt M
    previousSigma lowerLevel secondNext ->
  firstNext = secondNext.
Proof.
  intros M hPA previousSigma lowerLevel firstNext secondNext
    (firstNumeral & firstDomain & firstLower &
      hfirstNumeral & hfirstDomain & hfirstLower & hfirstNext)
    (secondNumeral & secondDomain & secondLower &
      hsecondNumeral & hsecondDomain & hsecondLower & hsecondNext).
  pose proof (raw_numeralTermCodeAt_functional M hPA
    (raw_succ M lowerLevel) firstNumeral secondNumeral
    hfirstNumeral hsecondNumeral) as hnumeral.
  subst secondNumeral.
  pose proof (raw_codedFormulaSingleSubstitution_functional M hPA
    firstNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthPiRowDomainTemplate))
    firstDomain secondDomain hfirstDomain hsecondDomain) as hdomain.
  pose proof (raw_dynamicTruthPiCoqLowerApplication_functional M hPA
    previousSigma firstLower secondLower hfirstLower hsecondLower) as hlower.
  rewrite hfirstNext, hsecondNext, hdomain, hlower.
  reflexivity.
Qed.

Lemma raw_dynamicTruthPairedSuccessorRowAt_functional : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      previousSigma previousPi lowerLevel
      firstNextSigma firstNextPi secondNextSigma secondNextPi,
  RawDynamicTruthPairedSuccessorRowAt M
    previousSigma previousPi lowerLevel firstNextSigma firstNextPi ->
  RawDynamicTruthPairedSuccessorRowAt M
    previousSigma previousPi lowerLevel secondNextSigma secondNextPi ->
  firstNextSigma = secondNextSigma /\ firstNextPi = secondNextPi.
Proof.
  intros M hPA previousSigma previousPi lowerLevel
    firstNextSigma firstNextPi secondNextSigma secondNextPi
    [hfirstSigma hfirstPi] [hsecondSigma hsecondPi].
  split.
  - exact (raw_dynamicTruthSigmaSuccessorRowAt_functional M hPA
      previousPi lowerLevel firstNextSigma secondNextSigma
      hfirstSigma hsecondSigma).
  - exact (raw_dynamicTruthPiSuccessorRowAt_functional M hPA
      previousSigma lowerLevel firstNextPi secondNextPi
      hfirstPi hsecondPi).
Qed.

(** Once the local row pair is unique, the public global pair is uniquely
    determined by the transparent global-wrapper polynomial. *)
Theorem raw_dynamicTruthPairedGlobalSuccessorAt_functional : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      previousSigma previousPi lowerLevel
      firstNextSigma firstNextPi secondNextSigma secondNextPi,
  RawDynamicTruthPairedGlobalSuccessorAt M
    previousSigma previousPi lowerLevel firstNextSigma firstNextPi ->
  RawDynamicTruthPairedGlobalSuccessorAt M
    previousSigma previousPi lowerLevel secondNextSigma secondNextPi ->
  firstNextSigma = secondNextSigma /\ firstNextPi = secondNextPi.
Proof.
  intros M hPA previousSigma previousPi lowerLevel
    firstNextSigma firstNextPi secondNextSigma secondNextPi
    (firstLocalSigma & firstLocalPi & hfirstRows & hfirstWrapper)
    (secondLocalSigma & secondLocalPi & hsecondRows & hsecondWrapper).
  destruct (raw_dynamicTruthPairedSuccessorRowAt_functional M hPA
    previousSigma previousPi lowerLevel
    firstLocalSigma firstLocalPi secondLocalSigma secondLocalPi
    hfirstRows hsecondRows) as [hsigma hpi].
  subst secondLocalSigma. subst secondLocalPi.
  unfold RawDynamicTruthPairedGlobalWrapperAt in
    hfirstWrapper, hsecondWrapper.
  destruct hfirstWrapper as [hfirstSigma hfirstPi].
  destruct hsecondWrapper as [hsecondSigma hsecondPi].
  split; congruence.
Qed.

Corollary raw_sat_dynamicTruthPairedGlobalSuccessorGraph_functional : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      tail previousSigma previousPi lowerLevel
      firstNextSigma firstNextPi secondNextSigma secondNextPi,
  raw_formula_sat M
    (scons M firstNextSigma (scons M firstNextPi
      (scons M previousSigma (scons M previousPi
        (scons M lowerLevel tail)))))
    dynamicTruthPairedGlobalSuccessorGraph ->
  raw_formula_sat M
    (scons M secondNextSigma (scons M secondNextPi
      (scons M previousSigma (scons M previousPi
        (scons M lowerLevel tail)))))
    dynamicTruthPairedGlobalSuccessorGraph ->
  firstNextSigma = secondNextSigma /\ firstNextPi = secondNextPi.
Proof.
  intros M hPA tail previousSigma previousPi lowerLevel
    firstNextSigma firstNextPi secondNextSigma secondNextPi
    hfirst hsecond.
  apply (raw_dynamicTruthPairedGlobalSuccessorAt_functional M hPA
    previousSigma previousPi lowerLevel
    firstNextSigma firstNextPi secondNextSigma secondNextPi).
  - apply (proj1 (raw_sat_dynamicTruthPairedGlobalSuccessorGraph_iff M
      tail lowerLevel previousSigma previousPi
      firstNextSigma firstNextPi)). exact hfirst.
  - apply (proj1 (raw_sat_dynamicTruthPairedGlobalSuccessorGraph_iff M
      tail lowerLevel previousSigma previousPi
      secondNextSigma secondNextPi)). exact hsecond.
Qed.

(** ------------------------------------------------------------------
    A represented functionality invariant for the whole orbit. *)

Definition dynamicTruthPairedGlobalOrbitFunctionalLeftRenaming
    (index : nat) : nat :=
  match index with
  | 0 => 3
  | 1 => 2
  | 2 => 4
  | S (S (S tailIndex)) => 5 + tailIndex
  end.

Definition dynamicTruthPairedGlobalOrbitFunctionalRightRenaming
    (index : nat) : nat :=
  match index with
  | 0 => 1
  | 1 => 0
  | 2 => 4
  | S (S (S tailIndex)) => 5 + tailIndex
  end.

(** Under the four binders the environment is

      rightPi :: rightSigma :: leftPi :: leftSigma :: level :: tail.

    The two renamings retain the same [level] and [tail], while selecting the
    appropriate output pair. *)
Lemma raw_sat_dynamicTruthPairedGlobalOrbitFunctionalLeftRenamed_iff : forall
    (M : RawPAModel) tail level
      leftSigma leftPi rightSigma rightPi,
  raw_formula_sat M
    (scons M rightPi (scons M rightSigma
      (scons M leftPi (scons M leftSigma
        (scons M level tail)))))
    (Formula.rename
      dynamicTruthPairedGlobalOrbitFunctionalLeftRenaming
      dynamicTruthPairedGlobalFormulaCodeOrbitGraph) <->
  raw_formula_sat M
    (scons M leftSigma (scons M leftPi (scons M level tail)))
    dynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Proof.
  intros M tail level leftSigma leftPi rightSigma rightPi.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro index.
  destruct index as [|[|[|tailIndex]]];
    cbn [dynamicTruthPairedGlobalOrbitFunctionalLeftRenaming].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - replace (5 + tailIndex) with
      (S (S (S (S (S tailIndex))))) by lia.
    reflexivity.
Qed.

Lemma raw_sat_dynamicTruthPairedGlobalOrbitFunctionalRightRenamed_iff :
    forall (M : RawPAModel) tail level
      leftSigma leftPi rightSigma rightPi,
  raw_formula_sat M
    (scons M rightPi (scons M rightSigma
      (scons M leftPi (scons M leftSigma
        (scons M level tail)))))
    (Formula.rename
      dynamicTruthPairedGlobalOrbitFunctionalRightRenaming
      dynamicTruthPairedGlobalFormulaCodeOrbitGraph) <->
  raw_formula_sat M
    (scons M rightSigma (scons M rightPi (scons M level tail)))
    dynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Proof.
  intros M tail level leftSigma leftPi rightSigma rightPi.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro index.
  destruct index as [|[|[|tailIndex]]];
    cbn [dynamicTruthPairedGlobalOrbitFunctionalRightRenaming].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - replace (5 + tailIndex) with
      (S (S (S (S (S tailIndex))))) by lia.
    reflexivity.
Qed.

Definition dynamicTruthPairedGlobalOrbitFunctionalFormula : formula :=
  pAll (pAll (pAll (pAll
    (pImp
      (Formula.rename
        dynamicTruthPairedGlobalOrbitFunctionalLeftRenaming
        dynamicTruthPairedGlobalFormulaCodeOrbitGraph)
      (pImp
        (Formula.rename
          dynamicTruthPairedGlobalOrbitFunctionalRightRenaming
          dynamicTruthPairedGlobalFormulaCodeOrbitGraph)
        (pAnd
          (pEq (tVar 3) (tVar 1))
          (pEq (tVar 2) (tVar 0)))))))).

Definition RawDynamicTruthPairedGlobalFormulaCodeOrbitFunctionalAt
    (M : RawPAModel) (tail : nat -> M) (level : M) : Prop :=
  forall leftSigma leftPi rightSigma rightPi,
    RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
      tail level leftSigma leftPi ->
    RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
      tail level rightSigma rightPi ->
    leftSigma = rightSigma /\ leftPi = rightPi.

Arguments RawDynamicTruthPairedGlobalFormulaCodeOrbitFunctionalAt
  M tail level : clear implicits.

(** Keep the large orbit formula folded while reducing the four universal
    binders and the propositional functionality shell. *)
Local Opaque dynamicTruthPairedGlobalFormulaCodeOrbitGraph.

Lemma raw_sat_dynamicTruthPairedGlobalOrbitFunctionalFormula_iff : forall
    (M : RawPAModel) tail level,
  raw_formula_sat M (scons M level tail)
    dynamicTruthPairedGlobalOrbitFunctionalFormula <->
  RawDynamicTruthPairedGlobalFormulaCodeOrbitFunctionalAt M tail level.
Proof.
  intros M tail level.
  unfold dynamicTruthPairedGlobalOrbitFunctionalFormula.
  change
    ((forall leftSigma leftPi rightSigma rightPi : M,
      raw_formula_sat M
        (scons M rightPi (scons M rightSigma
          (scons M leftPi (scons M leftSigma
            (scons M level tail)))))
        (Formula.rename
          dynamicTruthPairedGlobalOrbitFunctionalLeftRenaming
          dynamicTruthPairedGlobalFormulaCodeOrbitGraph) ->
      raw_formula_sat M
        (scons M rightPi (scons M rightSigma
          (scons M leftPi (scons M leftSigma
            (scons M level tail)))))
        (Formula.rename
          dynamicTruthPairedGlobalOrbitFunctionalRightRenaming
          dynamicTruthPairedGlobalFormulaCodeOrbitGraph) ->
      leftSigma = rightSigma /\ leftPi = rightPi) <->
      RawDynamicTruthPairedGlobalFormulaCodeOrbitFunctionalAt M tail level).
  unfold RawDynamicTruthPairedGlobalFormulaCodeOrbitFunctionalAt.
  split.
  - intros hfunctional leftSigma leftPi rightSigma rightPi
      hleftOrbit hrightOrbit.
    apply (hfunctional leftSigma leftPi rightSigma rightPi).
    + apply (proj2
        (raw_sat_dynamicTruthPairedGlobalOrbitFunctionalLeftRenamed_iff
          M tail level leftSigma leftPi rightSigma rightPi)).
      apply (proj2
        (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
          tail level leftSigma leftPi)).
      exact hleftOrbit.
    + apply (proj2
        (raw_sat_dynamicTruthPairedGlobalOrbitFunctionalRightRenamed_iff
          M tail level leftSigma leftPi rightSigma rightPi)).
      apply (proj2
        (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
          tail level rightSigma rightPi)).
      exact hrightOrbit.
  - intros hfunctional leftSigma leftPi rightSigma rightPi
      hleftSat hrightSat.
    apply (hfunctional leftSigma leftPi rightSigma rightPi).
    + apply (proj1
        (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
          tail level leftSigma leftPi)).
      apply (proj1
        (raw_sat_dynamicTruthPairedGlobalOrbitFunctionalLeftRenamed_iff
          M tail level leftSigma leftPi rightSigma rightPi)).
      exact hleftSat.
    + apply (proj1
        (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
          tail level rightSigma rightPi)).
      apply (proj1
        (raw_sat_dynamicTruthPairedGlobalOrbitFunctionalRightRenamed_iff
          M tail level leftSigma leftPi rightSigma rightPi)).
      exact hrightSat.
Qed.

Lemma raw_dynamicTruthPairedGlobalFormulaCodeOrbitFunctionalAt_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail,
  RawDynamicTruthPairedGlobalFormulaCodeOrbitFunctionalAt M
    tail (raw_zero M).
Proof.
  intros M hPA tail leftSigma leftPi rightSigma rightPi
    hleft hright.
  apply (proj1
    (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_zero_iff M hPA
      tail leftSigma leftPi)) in hleft.
  apply (proj1
    (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_zero_iff M hPA
      tail rightSigma rightPi)) in hright.
  apply (proj1 (raw_sat_dynamicTruthPairedGlobalBaseGraph_iff M tail
    leftSigma leftPi)) in hleft.
  apply (proj1 (raw_sat_dynamicTruthPairedGlobalBaseGraph_iff M tail
    rightSigma rightPi)) in hright.
  exact (raw_dynamicTruthPairedGlobalBaseAt_functional M
    leftSigma leftPi rightSigma rightPi hleft hright).
Qed.

Lemma raw_dynamicTruthPairedGlobalFormulaCodeOrbitFunctionalAt_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail level,
  RawDynamicTruthPairedGlobalFormulaCodeOrbitFunctionalAt M tail level ->
  RawDynamicTruthPairedGlobalFormulaCodeOrbitFunctionalAt M
    tail (raw_succ M level).
Proof.
  intros M hPA tail level hlevel
    leftSigma leftPi rightSigma rightPi hleft hright.
  apply (proj1
    (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_succ_iff M hPA
      tail level leftSigma leftPi)) in hleft.
  apply (proj1
    (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_succ_iff M hPA
      tail level rightSigma rightPi)) in hright.
  destruct hleft as
    (leftPreviousSigma & leftPreviousPi & hleftPrevious & hleftSuccessor).
  destruct hright as
    (rightPreviousSigma & rightPreviousPi &
      hrightPrevious & hrightSuccessor).
  destruct (hlevel leftPreviousSigma leftPreviousPi
    rightPreviousSigma rightPreviousPi
    hleftPrevious hrightPrevious) as [hsigma hpi].
  subst rightPreviousSigma. subst rightPreviousPi.
  exact (raw_dynamicTruthPairedGlobalSuccessorAt_functional M hPA
    leftPreviousSigma leftPreviousPi level
    leftSigma leftPi rightSigma rightPi
    hleftSuccessor hrightSuccessor).
Qed.

(** PA's own induction axiom propagates pair uniqueness through arbitrary,
    including nonstandard, carrier indices. *)
Theorem raw_dynamicTruthPairedGlobalFormulaCodeOrbitFunctionalAt_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail level,
  RawDynamicTruthPairedGlobalFormulaCodeOrbitFunctionalAt M tail level.
Proof.
  intros M hPA tail.
  set (phi := dynamicTruthPairedGlobalOrbitFunctionalFormula).
  assert (hall : forall level,
      raw_formula_sat M (scons M level tail) phi).
  {
    apply (raw_definable_induction M hPA phi tail).
    - unfold phi.
      apply (proj2
        (raw_sat_dynamicTruthPairedGlobalOrbitFunctionalFormula_iff M
          tail (raw_zero M))).
      exact (raw_dynamicTruthPairedGlobalFormulaCodeOrbitFunctionalAt_zero
        M hPA tail).
    - intros level hlevelSat.
      unfold phi in hlevelSat |- *.
      pose proof (proj1
        (raw_sat_dynamicTruthPairedGlobalOrbitFunctionalFormula_iff M
          tail level) hlevelSat) as hlevel.
      apply (proj2
        (raw_sat_dynamicTruthPairedGlobalOrbitFunctionalFormula_iff M
          tail (raw_succ M level))).
      exact
        (raw_dynamicTruthPairedGlobalFormulaCodeOrbitFunctionalAt_succ
          M hPA tail level hlevel).
  }
  intro level.
  unfold phi in hall.
  exact (proj1
    (raw_sat_dynamicTruthPairedGlobalOrbitFunctionalFormula_iff M
      tail level) (hall level)).
Qed.

Theorem raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_functional : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      tail level leftSigma leftPi rightSigma rightPi,
  RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
    tail level leftSigma leftPi ->
  RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
    tail level rightSigma rightPi ->
  leftSigma = rightSigma /\ leftPi = rightPi.
Proof.
  intros M hPA tail level.
  exact (raw_dynamicTruthPairedGlobalFormulaCodeOrbitFunctionalAt_all
    M hPA tail level).
Qed.

Corollary raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_functional :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      tail level leftSigma leftPi rightSigma rightPi,
  raw_formula_sat M
    (scons M leftSigma (scons M leftPi (scons M level tail)))
    dynamicTruthPairedGlobalFormulaCodeOrbitGraph ->
  raw_formula_sat M
    (scons M rightSigma (scons M rightPi (scons M level tail)))
    dynamicTruthPairedGlobalFormulaCodeOrbitGraph ->
  leftSigma = rightSigma /\ leftPi = rightPi.
Proof.
  intros M hPA tail level leftSigma leftPi rightSigma rightPi
    hleft hright.
  apply (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_functional M hPA
    tail level leftSigma leftPi rightSigma rightPi).
  - apply (proj1
      (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
        tail level leftSigma leftPi)). exact hleft.
  - apply (proj1
      (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
        tail level rightSigma rightPi)). exact hright.
Qed.

(** Adequate totality plus functionality upgrades every law-free orbit
    witness to the adequate view.  This is useful because positive graph
    semantics intentionally expose only the law-free relation. *)
Corollary
    raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      tail level globalSigma globalPi,
  RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
    tail level globalSigma globalPi ->
  RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
    tail level globalSigma globalPi.
Proof.
  intros M hPA tail level globalSigma globalPi horbit.
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail level) as
    (adequateSigma & adequatePi & hadequateGraph &
      hadequateSigma & hadequatePi).
  pose proof (proj1
    (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
      tail level adequateSigma adequatePi) hadequateGraph) as hadequateOrbit.
  destruct
    (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_functional M hPA
      tail level globalSigma globalPi adequateSigma adequatePi
      horbit hadequateOrbit) as [hsigma hpi].
  apply (proj2
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
      tail level globalSigma globalPi)).
  split; [exact horbit |].
  split.
  - rewrite hsigma. exact hadequateSigma.
  - rewrite hpi. exact hadequatePi.
Qed.

Corollary
    raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_functional :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      tail level leftSigma leftPi rightSigma rightPi,
  RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
    tail level leftSigma leftPi ->
  RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
    tail level rightSigma rightPi ->
  leftSigma = rightSigma /\ leftPi = rightPi.
Proof.
  intros M hPA tail level leftSigma leftPi rightSigma rightPi
    hleft hright.
  apply (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_functional M hPA
    tail level leftSigma leftPi rightSigma rightPi).
  - apply (proj1
      (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
        tail level leftSigma leftPi)) in hleft.
    exact (proj1 hleft).
  - apply (proj1
      (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
        tail level rightSigma rightPi)) in hright.
    exact (proj1 hright).
Qed.

(** ------------------------------------------------------------------
    Coherence of the five native positive graph witnesses. *)

Definition RawDynamicTruthNativeFivePositiveOrbitCoherentAt
    (M : RawPAModel) (tail : nat -> M) (predecessorLevel : M)
    (localCode crossLevelCode shiftCode substitutionCode
      axiomSoundnessCode : M) : Prop :=
  exists currentGlobalSigma currentGlobalPi : M,
    RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi /\
    RawDynamicTruthNativeLocalFieldTransformAt M
      currentGlobalSigma currentGlobalPi predecessorLevel localCode /\
    RawDynamicTruthNativeCrossLevelFieldTransformAt M
      currentGlobalSigma currentGlobalPi predecessorLevel crossLevelCode /\
    RawDynamicTruthNativeShiftFieldTransformAt M
      currentGlobalSigma currentGlobalPi predecessorLevel shiftCode /\
    RawDynamicTruthNativeSubstitutionFieldTransformAt M
      currentGlobalSigma currentGlobalPi predecessorLevel substitutionCode /\
    RawDynamicTruthNativeAxiomSoundnessFieldTransformAt M
      currentGlobalSigma currentGlobalPi predecessorLevel axiomSoundnessCode.

Arguments RawDynamicTruthNativeFivePositiveOrbitCoherentAt
  M tail predecessorLevel localCode crossLevelCode shiftCode
    substitutionCode axiomSoundnessCode : clear implicits.

Theorem raw_dynamicTruthNativeFivePositiveAt_orbit_coherent : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      tail predecessorLevel
      localCode crossLevelCode shiftCode substitutionCode axiomSoundnessCode,
  RawDynamicTruthNativeLocalPositiveAt M
    tail predecessorLevel localCode ->
  RawDynamicTruthNativeCrossLevelPositiveAt M
    tail predecessorLevel crossLevelCode ->
  RawDynamicTruthNativeShiftPositiveAt M
    tail predecessorLevel shiftCode ->
  RawDynamicTruthNativeSubstitutionPositiveAt M
    tail predecessorLevel substitutionCode ->
  RawDynamicTruthNativeAxiomSoundnessPositiveAt M
    tail predecessorLevel axiomSoundnessCode ->
  RawDynamicTruthNativeFivePositiveOrbitCoherentAt M
    tail predecessorLevel localCode crossLevelCode shiftCode
    substitutionCode axiomSoundnessCode.
Proof.
  intros M hPA tail predecessorLevel
    localCode crossLevelCode shiftCode substitutionCode axiomSoundnessCode
    (localSigma & localPi & hlocalOrbit & hlocalTransform)
    (crossSigma & crossPi & hcrossOrbit & hcrossTransform)
    (shiftSigma & shiftPi & hshiftOrbit & hshiftTransform)
    (substitutionSigma & substitutionPi &
      hsubstitutionOrbit & hsubstitutionTransform)
    (axiomSigma & axiomPi & haxiomOrbit & haxiomTransform).
  destruct
    (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_functional M hPA
      tail (raw_succ M predecessorLevel)
      localSigma localPi crossSigma crossPi
      hlocalOrbit hcrossOrbit) as [hcrossSigma hcrossPi].
  subst crossSigma. subst crossPi.
  destruct
    (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_functional M hPA
      tail (raw_succ M predecessorLevel)
      localSigma localPi shiftSigma shiftPi
      hlocalOrbit hshiftOrbit) as [hshiftSigma hshiftPi].
  subst shiftSigma. subst shiftPi.
  destruct
    (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_functional M hPA
      tail (raw_succ M predecessorLevel)
      localSigma localPi substitutionSigma substitutionPi
      hlocalOrbit hsubstitutionOrbit) as [hsubstitutionSigma hsubstitutionPi].
  subst substitutionSigma. subst substitutionPi.
  destruct
    (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_functional M hPA
      tail (raw_succ M predecessorLevel)
      localSigma localPi axiomSigma axiomPi
      hlocalOrbit haxiomOrbit) as [haxiomSigma haxiomPi].
  subst axiomSigma. subst axiomPi.
  exists localSigma, localPi.
  split.
  - exact
      (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_adequate M hPA
        tail (raw_succ M predecessorLevel) localSigma localPi hlocalOrbit).
  - split; [exact hlocalTransform |].
    split; [exact hcrossTransform |].
    split; [exact hshiftTransform |].
    split; [exact hsubstitutionTransform | exact haxiomTransform].
Qed.

Corollary raw_dynamicTruthNativeFivePositiveGraphs_orbit_coherent : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      tail predecessorLevel
      localCode crossLevelCode shiftCode substitutionCode axiomSoundnessCode,
  raw_formula_sat M
    (scons M localCode (scons M predecessorLevel tail))
    dynamicTruthNativeLocalPositiveGraph ->
  raw_formula_sat M
    (scons M crossLevelCode (scons M predecessorLevel tail))
    dynamicTruthNativeCrossLevelPositiveGraph ->
  raw_formula_sat M
    (scons M shiftCode (scons M predecessorLevel tail))
    dynamicTruthNativeShiftPositiveGraph ->
  raw_formula_sat M
    (scons M substitutionCode (scons M predecessorLevel tail))
    dynamicTruthNativeSubstitutionPositiveGraph ->
  raw_formula_sat M
    (scons M axiomSoundnessCode (scons M predecessorLevel tail))
    dynamicTruthNativeAxiomSoundnessPositiveGraph ->
  RawDynamicTruthNativeFivePositiveOrbitCoherentAt M
    tail predecessorLevel localCode crossLevelCode shiftCode
    substitutionCode axiomSoundnessCode.
Proof.
  intros M hPA tail predecessorLevel
    localCode crossLevelCode shiftCode substitutionCode axiomSoundnessCode
    hlocal hcross hshift hsubstitution haxiom.
  apply (raw_dynamicTruthNativeFivePositiveAt_orbit_coherent M hPA
    tail predecessorLevel localCode crossLevelCode shiftCode
    substitutionCode axiomSoundnessCode).
  - apply (proj1 (raw_sat_dynamicTruthNativeLocalPositiveGraph_iff M
      tail predecessorLevel localCode)). exact hlocal.
  - apply (proj1 (raw_sat_dynamicTruthNativeCrossLevelPositiveGraph_iff M
      tail predecessorLevel crossLevelCode)). exact hcross.
  - apply (proj1 (raw_sat_dynamicTruthNativeShiftPositiveGraph_iff M
      tail predecessorLevel shiftCode)). exact hshift.
  - apply (proj1 (raw_sat_dynamicTruthNativeSubstitutionPositiveGraph_iff M
      tail predecessorLevel substitutionCode)). exact hsubstitution.
  - apply (proj1
      (raw_sat_dynamicTruthNativeAxiomSoundnessPositiveGraph_iff M
        tail predecessorLevel axiomSoundnessCode)). exact haxiom.
Qed.

End PABoundedRawCodedDynamicTruthPairedGlobalOrbitFunctionality.
