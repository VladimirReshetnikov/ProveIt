(**
  PA-internal carrier-indexed code orbits.

  The base and successor graphs use the parameter-friendly conventions

      base :: tail
      next :: previous :: index :: tail,

  while the resulting output-first orbit graph is read under

      output :: level :: tail.

  An orbit witness is an honest Goedel-beta assignment defined through
  [level + 1].  Row zero satisfies the base graph and every adjacent pair
  satisfies the represented successor graph.  The table bound and all row
  indices are carrier elements; totality below is therefore proved with PA's
  represented induction rather than recursion over Rocq naturals.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness PolynomialPairInjectivity
  RawCodedAssignment RawCodedAssignmentTotality
  RawCodedFormulaRankTotality RawCodedFormulaOperations
  RawCodedFixedLevelTruthTotality.

Module PABoundedRawCodedCarrierIndexedCodeOrbitGraph.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedAssignmentTotality.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruthTotality.

(** ------------------------------------------------------------------
    Explicit de Bruijn forwarding.

    Under the three trace witnesses the environment is

      base :: step :: code :: output :: level :: tail.

    Under the row quantifiers it is

      next :: previous :: index :: base :: step :: code ::
        output :: level :: tail.
*)

Definition carrierCodeOrbitBaseRenaming (index : nat) : nat :=
  match index with
  | 0 => 0
  | S tailIndex => tailIndex + 5
  end.

Definition carrierCodeOrbitSuccessorRenaming (index : nat) : nat :=
  match index with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | S (S (S tailIndex)) => tailIndex + 8
  end.

Lemma raw_sat_carrierCodeOrbitBaseRenamedGraph_iff : forall
    (M : RawPAModel) baseGraph base step code output level tail,
  raw_formula_sat M
    (scons M base (scons M step (scons M code
      (scons M output (scons M level tail)))))
    (Formula.rename carrierCodeOrbitBaseRenaming baseGraph) <->
  raw_formula_sat M (scons M base tail) baseGraph.
Proof.
  intros M baseGraph base step code output level tail.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro index.
  destruct index; cbn [carrierCodeOrbitBaseRenaming].
  - reflexivity.
  - replace (index + 5) with (S (S (S (S (S index))))) by lia.
    reflexivity.
Qed.

Lemma raw_sat_carrierCodeOrbitSuccessorRenamedGraph_iff : forall
    (M : RawPAModel) successorGraph next previous index
      base step code output level tail,
  raw_formula_sat M
    (scons M next (scons M previous (scons M index
      (scons M base (scons M step (scons M code
        (scons M output (scons M level tail))))))))
    (Formula.rename carrierCodeOrbitSuccessorRenaming successorGraph) <->
  raw_formula_sat M
    (scons M next (scons M previous (scons M index tail)))
    successorGraph.
Proof.
  intros M successorGraph next previous index
    base step code output level tail.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro variable.
  destruct variable as [|[|[|tailIndex]]];
    cbn [carrierCodeOrbitSuccessorRenaming].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - replace (tailIndex + 8) with
      (S (S (S (S (S (S (S (S tailIndex)))))))) by lia.
    reflexivity.
Qed.

(** ------------------------------------------------------------------
    Raw orbit relation and represented formula. *)

Definition RawCarrierIndexedCodeOrbitRows (M : RawPAModel)
    (successorGraph : formula) (tail : nat -> M)
    (bound code step : M) : Prop :=
  forall index previous next : M,
    rawLt M index bound ->
    RawCodedAssignmentLookup M code step index previous ->
    RawCodedAssignmentLookup M code step (raw_succ M index) next ->
    raw_formula_sat M
      (scons M next (scons M previous (scons M index tail)))
      successorGraph.

Arguments RawCarrierIndexedCodeOrbitRows
  M successorGraph tail bound code step : clear implicits.

Definition RawCarrierIndexedCodeOrbitTrace (M : RawPAModel)
    (baseGraph successorGraph : formula) (tail : nat -> M)
    (level output code step base : M) : Prop :=
  RawCodedAssignmentDefinedThrough M code step (raw_succ M level) /\
  RawCodedAssignmentLookup M code step (raw_zero M) base /\
  raw_formula_sat M (scons M base tail) baseGraph /\
  RawCarrierIndexedCodeOrbitRows M successorGraph tail level code step /\
  RawCodedAssignmentLookup M code step level output.

Arguments RawCarrierIndexedCodeOrbitTrace
  M baseGraph successorGraph tail level output code step base
  : clear implicits.

Definition RawCarrierIndexedCodeOrbitAt (M : RawPAModel)
    (baseGraph successorGraph : formula) (tail : nat -> M)
    (level output : M) : Prop :=
  exists code step base : M,
    RawCarrierIndexedCodeOrbitTrace M baseGraph successorGraph tail
      level output code step base.

Arguments RawCarrierIndexedCodeOrbitAt
  M baseGraph successorGraph tail level output : clear implicits.

(** This row formula is used beneath the three trace witnesses.  Its three
    universal binders are [index], [previous], and [next], in that order. *)
Definition carrierIndexedCodeOrbitRowsTermAt
    (successorGraph : formula) (bound code step : term) : formula :=
  pAll (pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 2) (liftTerm 3 bound))
      (pImp
        (codedAssignmentLookupTermAt
          (liftTerm 3 code) (liftTerm 3 step)
          (tVar 2) (tVar 1))
        (pImp
          (codedAssignmentLookupTermAt
            (liftTerm 3 code) (liftTerm 3 step)
            (tSucc (tVar 2)) (tVar 0))
          (Formula.rename
            carrierCodeOrbitSuccessorRenaming successorGraph)))))).

Lemma raw_sat_carrierIndexedCodeOrbitRowsTermAt_iff : forall
    (M : RawPAModel) successorGraph base step code output level tail,
  raw_formula_sat M
    (scons M base (scons M step (scons M code
      (scons M output (scons M level tail)))))
    (carrierIndexedCodeOrbitRowsTermAt
      successorGraph (tVar 4) (tVar 2) (tVar 1)) <->
  RawCarrierIndexedCodeOrbitRows M successorGraph tail level code step.
Proof.
  intros M successorGraph base step code output level tail.
  unfold carrierIndexedCodeOrbitRowsTermAt,
    RawCarrierIndexedCodeOrbitRows.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  setoid_rewrite raw_sat_carrierCodeOrbitSuccessorRenamedGraph_iff.
  repeat setoid_rewrite raw_operation_eval_liftTerm_three.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** Three existential witnesses are, from outermost to innermost, [code],
    [step], and [base]. *)
Definition carrierIndexedCodeOrbitGraph
    (baseGraph successorGraph : formula) : formula :=
  operationEx3
    (operationAnd5
      (codedAssignmentDefinedThroughTermAt
        (tVar 2) (tVar 1) (tSucc (tVar 4)))
      (codedAssignmentLookupTermAt
        (tVar 2) (tVar 1) tZero (tVar 0))
      (Formula.rename carrierCodeOrbitBaseRenaming baseGraph)
      (carrierIndexedCodeOrbitRowsTermAt
        successorGraph (tVar 4) (tVar 2) (tVar 1))
      (codedAssignmentLookupTermAt
        (tVar 2) (tVar 1) (tVar 4) (tVar 3))).

(** Exact formula semantics.  This theorem is law-free; PA enters only when
    beta functionality or nonstandard induction is used below. *)
Theorem raw_sat_carrierIndexedCodeOrbitGraph_iff : forall
    (M : RawPAModel) baseGraph successorGraph tail level output,
  raw_formula_sat M (scons M output (scons M level tail))
    (carrierIndexedCodeOrbitGraph baseGraph successorGraph) <->
  RawCarrierIndexedCodeOrbitAt M
    baseGraph successorGraph tail level output.
Proof.
  intros M baseGraph successorGraph tail level output.
  unfold carrierIndexedCodeOrbitGraph, operationEx3, operationAnd5,
    RawCarrierIndexedCodeOrbitAt, RawCarrierIndexedCodeOrbitTrace.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  setoid_rewrite raw_sat_carrierCodeOrbitBaseRenamedGraph_iff.
  setoid_rewrite raw_sat_carrierIndexedCodeOrbitRowsTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** Existential output closure used as the represented induction invariant.
    It is evaluated under [level :: tail]. *)
Definition carrierIndexedCodeOrbitExistsFormula
    (baseGraph successorGraph : formula) : formula :=
  pEx (carrierIndexedCodeOrbitGraph baseGraph successorGraph).

Lemma raw_sat_carrierIndexedCodeOrbitExistsFormula_iff : forall
    (M : RawPAModel) baseGraph successorGraph tail level,
  raw_formula_sat M (scons M level tail)
    (carrierIndexedCodeOrbitExistsFormula baseGraph successorGraph) <->
  exists output : M,
    RawCarrierIndexedCodeOrbitAt M
      baseGraph successorGraph tail level output.
Proof.
  intros M baseGraph successorGraph tail level.
  unfold carrierIndexedCodeOrbitExistsFormula.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_carrierIndexedCodeOrbitGraph_iff.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Base and successor extension. *)

Definition RawCarrierIndexedCodeOrbitBaseTotal (M : RawPAModel)
    (baseGraph : formula) : Prop :=
  forall tail : nat -> M,
    exists base : M,
      raw_formula_sat M (scons M base tail) baseGraph.

Definition RawCarrierIndexedCodeOrbitSuccessorTotal (M : RawPAModel)
    (successorGraph : formula) : Prop :=
  forall (tail : nat -> M) index previous,
    exists next : M,
      raw_formula_sat M
        (scons M next (scons M previous (scons M index tail)))
        successorGraph.

Arguments RawCarrierIndexedCodeOrbitBaseTotal M baseGraph : clear implicits.
Arguments RawCarrierIndexedCodeOrbitSuccessorTotal M successorGraph
  : clear implicits.

(** A one-entry beta table realizes the base branch. *)
Lemma raw_carrierIndexedCodeOrbitAt_zero_of_base : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph tail base,
  raw_formula_sat M (scons M base tail) baseGraph ->
  RawCarrierIndexedCodeOrbitAt M
    baseGraph successorGraph tail (raw_zero M) base.
Proof.
  intros M hPA baseGraph successorGraph tail base hbase.
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    (raw_zero M) (raw_zero M) (raw_zero M) base
    (raw_codedAssignment_empty_defined M hPA))
    as (code & step & hdefined & hprefix & hroot).
  exists code, step, base.
  split; [exact hdefined |].
  split; [exact hroot |].
  split; [exact hbase |].
  split.
  - intros index previous next hindex _ _.
    exfalso. exact (raw_not_lt_zero M hPA index hindex).
  - exact hroot.
Qed.

(** Append one successor row.  Old rows are reconstructed through the
    append prefix and beta functionality; the new final row is exactly the
    supplied successor-graph witness. *)
Lemma raw_carrierIndexedCodeOrbitAt_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph tail level previous next,
  RawCarrierIndexedCodeOrbitAt M
    baseGraph successorGraph tail level previous ->
  raw_formula_sat M
    (scons M next (scons M previous (scons M level tail)))
    successorGraph ->
  RawCarrierIndexedCodeOrbitAt M
    baseGraph successorGraph tail (raw_succ M level) next.
Proof.
  intros M hPA baseGraph successorGraph tail level previous next
    (code & step & base & hdefined & hzero & hbase & hrows & hprevious)
    hnext.
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    code step (raw_succ M level) next hdefined)
    as (newCode & newStep & hnewDefined & hpreserved & hnewLookup).
  exists newCode, newStep, base.
  split; [exact hnewDefined |].
  split.
  - apply hpreserved.
    + apply raw_lt_succ_of_le; [exact hPA |].
      apply raw_rank_zero_le. exact hPA.
    + exact hzero.
  - split; [exact hbase |]. split.
    + intros index rowPrevious rowNext hindex hrowPrevious hrowNext.
      destruct (raw_lt_succ_cases M hPA index level hindex)
        as [hindexOld | ->].
      * assert (hindexInPrefix : rawLt M index (raw_succ M level)).
        {
          exact (raw_assignment_lt_trans M hPA
            index level (raw_succ M level) hindexOld
            (raw_assignment_lt_self_succ M hPA level)).
        }
        assert (hnextInPrefix :
            rawLt M (raw_succ M index) (raw_succ M level)).
        {
          apply raw_lt_succ_of_le; [exact hPA |].
          exact (raw_succ_le_of_lt_pair M hPA index level hindexOld).
        }
        destruct (hdefined index hindexInPrefix)
          as [oldPrevious holdPrevious].
        destruct (hdefined (raw_succ M index) hnextInPrefix)
          as [oldNext holdNext].
        assert (hnewOldPrevious : RawCodedAssignmentLookup M
            newCode newStep index oldPrevious).
        { exact (hpreserved index oldPrevious
            hindexInPrefix holdPrevious). }
        assert (hnewOldNext : RawCodedAssignmentLookup M
            newCode newStep (raw_succ M index) oldNext).
        { exact (hpreserved (raw_succ M index) oldNext
            hnextInPrefix holdNext). }
        assert (hpreviousEq : rowPrevious = oldPrevious).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            newCode newStep index rowPrevious oldPrevious
            hrowPrevious hnewOldPrevious).
        }
        assert (hnextEq : rowNext = oldNext).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            newCode newStep (raw_succ M index) rowNext oldNext
            hrowNext hnewOldNext).
        }
        subst rowPrevious. subst rowNext.
        exact (hrows index oldPrevious oldNext hindexOld
          holdPrevious holdNext).
      * assert (hnewPrevious : RawCodedAssignmentLookup M
            newCode newStep level previous).
        {
          apply hpreserved.
          - exact (raw_assignment_lt_self_succ M hPA level).
          - exact hprevious.
        }
        assert (hpreviousEq : rowPrevious = previous).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            newCode newStep level rowPrevious previous
            hrowPrevious hnewPrevious).
        }
        assert (hnextEq : rowNext = next).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            newCode newStep (raw_succ M level) rowNext next
            hrowNext hnewLookup).
        }
        subst rowPrevious. subst rowNext. exact hnext.
    + exact hnewLookup.
Qed.

(** Existential base and successor forms used by represented induction. *)
Lemma raw_carrierIndexedCodeOrbitExists_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall baseGraph successorGraph tail,
  RawCarrierIndexedCodeOrbitBaseTotal M baseGraph ->
  exists output : M,
    RawCarrierIndexedCodeOrbitAt M
      baseGraph successorGraph tail (raw_zero M) output.
Proof.
  intros M hPA baseGraph successorGraph tail hbase.
  destruct (hbase tail) as [base hbaseGraph].
  exists base.
  exact (raw_carrierIndexedCodeOrbitAt_zero_of_base M hPA
    baseGraph successorGraph tail base hbaseGraph).
Qed.

Lemma raw_carrierIndexedCodeOrbitExists_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph tail,
  RawCarrierIndexedCodeOrbitSuccessorTotal M successorGraph ->
  forall level,
  (exists previous : M,
    RawCarrierIndexedCodeOrbitAt M
      baseGraph successorGraph tail level previous) ->
  exists next : M,
    RawCarrierIndexedCodeOrbitAt M
      baseGraph successorGraph tail (raw_succ M level) next.
Proof.
  intros M hPA baseGraph successorGraph tail hsuccessor level
    [previous hprevious].
  destruct (hsuccessor tail level previous) as [next hnext].
  exists next.
  exact (raw_carrierIndexedCodeOrbitAt_succ M hPA
    baseGraph successorGraph tail level previous next hprevious hnext).
Qed.

(** ------------------------------------------------------------------
    PA-definable totality.

    The induction formula is the explicit existential beta-table graph above.
    Thus this proof reaches arbitrary nonstandard carrier levels.  The only
    semantic inputs are totality of the fixed base graph and of one represented
    successor step; no orbit callback is assumed. *)

Theorem raw_carrierIndexedCodeOrbitExists_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph,
  RawCarrierIndexedCodeOrbitBaseTotal M baseGraph ->
  RawCarrierIndexedCodeOrbitSuccessorTotal M successorGraph ->
  forall (tail : nat -> M) level,
  exists output : M,
    RawCarrierIndexedCodeOrbitAt M
      baseGraph successorGraph tail level output.
Proof.
  intros M hPA baseGraph successorGraph hbase hsuccessor tail.
  set (phi := carrierIndexedCodeOrbitExistsFormula
    baseGraph successorGraph).
  assert (hall : forall level,
      raw_formula_sat M (scons M level tail) phi).
  {
    apply (raw_definable_induction M hPA phi tail).
    - unfold phi.
      apply (proj2
        (raw_sat_carrierIndexedCodeOrbitExistsFormula_iff M
          baseGraph successorGraph tail (raw_zero M))).
      exact (raw_carrierIndexedCodeOrbitExists_zero M hPA
        baseGraph successorGraph tail hbase).
    - intros level hlevelSat.
      unfold phi in hlevelSat |- *.
      pose proof (proj1
        (raw_sat_carrierIndexedCodeOrbitExistsFormula_iff M
          baseGraph successorGraph tail level) hlevelSat) as hlevel.
      apply (proj2
        (raw_sat_carrierIndexedCodeOrbitExistsFormula_iff M
          baseGraph successorGraph tail (raw_succ M level))).
      exact (raw_carrierIndexedCodeOrbitExists_succ M hPA
        baseGraph successorGraph tail hsuccessor level hlevel).
  }
  intro level. unfold phi in hall.
  exact (proj1
    (raw_sat_carrierIndexedCodeOrbitExistsFormula_iff M
      baseGraph successorGraph tail level) (hall level)).
Qed.

Definition RawCarrierIndexedCodeOrbitGraphTotal (M : RawPAModel)
    (baseGraph successorGraph : formula) : Prop :=
  forall (tail : nat -> M) level,
    exists output : M,
      raw_formula_sat M (scons M output (scons M level tail))
        (carrierIndexedCodeOrbitGraph baseGraph successorGraph).

Arguments RawCarrierIndexedCodeOrbitGraphTotal
  M baseGraph successorGraph : clear implicits.

Corollary raw_carrierIndexedCodeOrbitGraph_total : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph,
  RawCarrierIndexedCodeOrbitBaseTotal M baseGraph ->
  RawCarrierIndexedCodeOrbitSuccessorTotal M successorGraph ->
  RawCarrierIndexedCodeOrbitGraphTotal M baseGraph successorGraph.
Proof.
  intros M hPA baseGraph successorGraph hbase hsuccessor tail level.
  destruct (raw_carrierIndexedCodeOrbitExists_all M hPA
    baseGraph successorGraph hbase hsuccessor tail level)
    as [output horbit].
  exists output.
  exact (proj2 (raw_sat_carrierIndexedCodeOrbitGraph_iff M
    baseGraph successorGraph tail level output) horbit).
Qed.

(** ------------------------------------------------------------------
    Zero and successor views. *)

Lemma raw_carrierIndexedCodeOrbitAt_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph tail output,
  RawCarrierIndexedCodeOrbitAt M
    baseGraph successorGraph tail (raw_zero M) output <->
  raw_formula_sat M (scons M output tail) baseGraph.
Proof.
  intros M hPA baseGraph successorGraph tail output. split.
  - intros (code & step & base & hdefined & hzero & hbase & hrows & houtput).
    assert (houtputEq : output = base).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        code step (raw_zero M) output base houtput hzero).
    }
    subst output. exact hbase.
  - intro hbase.
    exact (raw_carrierIndexedCodeOrbitAt_zero_of_base M hPA
      baseGraph successorGraph tail output hbase).
Qed.

Lemma raw_carrierIndexedCodeOrbitAt_succ_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph tail level next,
  RawCarrierIndexedCodeOrbitAt M
    baseGraph successorGraph tail (raw_succ M level) next <->
  exists previous : M,
    RawCarrierIndexedCodeOrbitAt M
      baseGraph successorGraph tail level previous /\
    raw_formula_sat M
      (scons M next (scons M previous (scons M level tail)))
      successorGraph.
Proof.
  intros M hPA baseGraph successorGraph tail level next. split.
  - intros (code & step & base & hdefined & hzero & hbase & hrows & hnext).
    assert (hlevelInDefined :
        rawLt M level (raw_succ M (raw_succ M level))).
    {
      exact (raw_assignment_lt_trans M hPA
        level (raw_succ M level) (raw_succ M (raw_succ M level))
        (raw_assignment_lt_self_succ M hPA level)
        (raw_assignment_lt_self_succ M hPA (raw_succ M level))).
    }
    destruct (hdefined level hlevelInDefined)
      as [previous hprevious].
    exists previous. split.
    + exists code, step, base.
      split.
      * intros index hindex.
        exact (hdefined index
          (raw_assignment_lt_trans M hPA
            index (raw_succ M level)
            (raw_succ M (raw_succ M level)) hindex
            (raw_assignment_lt_self_succ M hPA
              (raw_succ M level)))).
      * split; [exact hzero |].
        split; [exact hbase |]. split.
        -- intros index rowPrevious rowNext hindex
             hrowPrevious hrowNext.
           exact (hrows index rowPrevious rowNext
             (raw_assignment_lt_trans M hPA
               index level (raw_succ M level) hindex
               (raw_assignment_lt_self_succ M hPA level))
             hrowPrevious hrowNext).
        -- exact hprevious.
    + exact (hrows level previous next
        (raw_assignment_lt_self_succ M hPA level)
        hprevious hnext).
  - intros [previous [hprevious hnext]].
    exact (raw_carrierIndexedCodeOrbitAt_succ M hPA
      baseGraph successorGraph tail level previous next
      hprevious hnext).
Qed.

Theorem raw_carrierIndexedCodeOrbitGraph_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph tail output,
  raw_formula_sat M
    (scons M output (scons M (raw_zero M) tail))
    (carrierIndexedCodeOrbitGraph baseGraph successorGraph) <->
  raw_formula_sat M (scons M output tail) baseGraph.
Proof.
  intros M hPA baseGraph successorGraph tail output.
  rewrite raw_sat_carrierIndexedCodeOrbitGraph_iff.
  exact (raw_carrierIndexedCodeOrbitAt_zero_iff M hPA
    baseGraph successorGraph tail output).
Qed.

Theorem raw_carrierIndexedCodeOrbitGraph_succ_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph tail level next,
  raw_formula_sat M
    (scons M next (scons M (raw_succ M level) tail))
    (carrierIndexedCodeOrbitGraph baseGraph successorGraph) <->
  exists previous : M,
    raw_formula_sat M
      (scons M previous (scons M level tail))
      (carrierIndexedCodeOrbitGraph baseGraph successorGraph) /\
    raw_formula_sat M
      (scons M next (scons M previous (scons M level tail)))
      successorGraph.
Proof.
  intros M hPA baseGraph successorGraph tail level next.
  rewrite raw_sat_carrierIndexedCodeOrbitGraph_iff.
  rewrite (raw_carrierIndexedCodeOrbitAt_succ_iff M hPA
    baseGraph successorGraph tail level next).
  setoid_rewrite raw_sat_carrierIndexedCodeOrbitGraph_iff.
  reflexivity.
Qed.

End PABoundedRawCodedCarrierIndexedCodeOrbitGraph.
