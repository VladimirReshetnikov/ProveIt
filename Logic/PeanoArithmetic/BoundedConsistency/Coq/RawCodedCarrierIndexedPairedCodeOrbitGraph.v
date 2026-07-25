(**
  PA-internal carrier-indexed orbits with two visible code coordinates.

  [RawCodedCarrierIndexedCodeOrbitGraph] already supplies the difficult
  part of the construction: a Goedel-beta orbit whose length may be a
  nonstandard element of an arbitrary PA model.  This file reuses that
  construction by storing each pair of coordinates as the transparent
  polynomial term [pairTerm].  Pair formation and both coordinate
  witnesses remain inside the represented formula; no meta-level unpairing
  operation is assumed.

  The public conventions are

      baseFirst :: baseSecond :: tail

  for the base graph,

      nextFirst :: nextSecond :: previousFirst :: previousSecond ::
        index :: tail

  for the successor graph, and

      outputFirst :: outputSecond :: level :: tail

  for the resulting orbit graph.

  A subtle point is that the polynomial pairing function is injective but
  not surjective.  Consequently we do *not* claim that the packed successor
  graph is total on arbitrary, possibly malformed packed values.  Instead
  PA induction is performed on the public two-coordinate orbit invariant.
  Every value reached from the paired base is visibly paired, so the
  represented successor graph can always extend it.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListFormulas Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness RawCodedFormulaOperations
  RawCodedSyntaxConstructors PolynomialPairInjectivity
  RawCodedCarrierIndexedCodeOrbitGraph.

Module PABoundedRawCodedCarrierIndexedPairedCodeOrbitGraph.

Import PA.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedCarrierIndexedCodeOrbitGraph.

(** ------------------------------------------------------------------
    Packed base and successor graphs.

    Beneath the two base witnesses the environment is

      second :: first :: packed :: tail.

    Beneath the four successor witnesses it is

      previousSecond :: previousFirst :: nextSecond :: nextFirst ::
        packedNext :: packedPrevious :: index :: tail.

    The explicit renamings below are kept separate so their de Bruijn
    bookkeeping can be audited independently of the orbit proof. *)

Definition pairedCarrierCodeOrbitBaseRenaming (index : nat) : nat :=
  match index with
  | 0 => 1
  | 1 => 0
  | S (S tailIndex) => tailIndex + 3
  end.

Definition pairedCarrierCodeOrbitSuccessorRenaming (index : nat) : nat :=
  match index with
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 6
  | S (S (S (S (S tailIndex)))) => tailIndex + 7
  end.

Lemma raw_sat_pairedCarrierCodeOrbitBaseRenamedGraph_iff : forall
    (M : RawPAModel) baseGraph second first packed tail,
  raw_formula_sat M
    (scons M second (scons M first (scons M packed tail)))
    (Formula.rename pairedCarrierCodeOrbitBaseRenaming baseGraph) <->
  raw_formula_sat M
    (scons M first (scons M second tail)) baseGraph.
Proof.
  intros M baseGraph second first packed tail.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro index.
  destruct index as [|[|tailIndex]];
    cbn [pairedCarrierCodeOrbitBaseRenaming].
  - reflexivity.
  - reflexivity.
  - replace (tailIndex + 3) with (S (S (S tailIndex))) by lia.
    reflexivity.
Qed.

Lemma raw_sat_pairedCarrierCodeOrbitSuccessorRenamedGraph_iff : forall
    (M : RawPAModel) successorGraph
      previousSecond previousFirst nextSecond nextFirst
      packedNext packedPrevious index tail,
  raw_formula_sat M
    (scons M previousSecond (scons M previousFirst
      (scons M nextSecond (scons M nextFirst
        (scons M packedNext (scons M packedPrevious
          (scons M index tail)))))))
    (Formula.rename pairedCarrierCodeOrbitSuccessorRenaming
      successorGraph) <->
  raw_formula_sat M
    (scons M nextFirst (scons M nextSecond
      (scons M previousFirst (scons M previousSecond
        (scons M index tail))))) successorGraph.
Proof.
  intros M successorGraph previousSecond previousFirst
    nextSecond nextFirst packedNext packedPrevious index tail.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro variable.
  destruct variable as [|[|[|[|[|tailIndex]]]]];
    cbn [pairedCarrierCodeOrbitSuccessorRenaming].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - replace (tailIndex + 7) with
      (S (S (S (S (S (S (S tailIndex))))))) by lia.
    reflexivity.
Qed.

(** The packed base relation has convention [packed :: tail].  Its two
    existential witnesses expose the coordinates used by [baseGraph]. *)
Definition pairedCarrierCodeOrbitPackedBaseGraph
    (baseGraph : formula) : formula :=
  operationEx2
    (pAnd
      (pEq (tVar 2) (pairTerm (tVar 1) (tVar 0)))
      (Formula.rename pairedCarrierCodeOrbitBaseRenaming baseGraph)).

Lemma raw_sat_pairedCarrierCodeOrbitPackedBaseGraph_iff : forall
    (M : RawPAModel) baseGraph tail packed,
  raw_formula_sat M (scons M packed tail)
    (pairedCarrierCodeOrbitPackedBaseGraph baseGraph) <->
  exists first second : M,
    packed = rawPolynomialPair M first second /\
    raw_formula_sat M
      (scons M first (scons M second tail)) baseGraph.
Proof.
  intros M baseGraph tail packed.
  unfold pairedCarrierCodeOrbitPackedBaseGraph, operationEx2.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_pairedCarrierCodeOrbitBaseRenamedGraph_iff.
  repeat rewrite raw_eval_pairTerm.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** The packed successor relation has convention
    [packedNext :: packedPrevious :: index :: tail].  Both decompositions
    are formula witnesses, so later successor views do not appeal to an
    external decoding function. *)
Definition pairedCarrierCodeOrbitPackedSuccessorGraph
    (successorGraph : formula) : formula :=
  operationEx4
    (operationAnd3
      (pEq (tVar 4) (pairTerm (tVar 3) (tVar 2)))
      (pEq (tVar 5) (pairTerm (tVar 1) (tVar 0)))
      (Formula.rename pairedCarrierCodeOrbitSuccessorRenaming
        successorGraph)).

Lemma raw_sat_pairedCarrierCodeOrbitPackedSuccessorGraph_iff : forall
    (M : RawPAModel) successorGraph tail index
      packedPrevious packedNext,
  raw_formula_sat M
    (scons M packedNext (scons M packedPrevious (scons M index tail)))
    (pairedCarrierCodeOrbitPackedSuccessorGraph successorGraph) <->
  exists nextFirst nextSecond previousFirst previousSecond : M,
    packedNext = rawPolynomialPair M nextFirst nextSecond /\
    packedPrevious = rawPolynomialPair M previousFirst previousSecond /\
    raw_formula_sat M
      (scons M nextFirst (scons M nextSecond
        (scons M previousFirst (scons M previousSecond
          (scons M index tail))))) successorGraph.
Proof.
  intros M successorGraph tail index packedPrevious packedNext.
  unfold pairedCarrierCodeOrbitPackedSuccessorGraph,
    operationEx4, operationAnd3.
  cbn [raw_formula_sat].
  setoid_rewrite
    raw_sat_pairedCarrierCodeOrbitSuccessorRenamedGraph_iff.
  repeat rewrite raw_eval_pairTerm.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Public two-output graph. *)

(** Beneath the public packed witness the environment is
    [packed :: first :: second :: level :: tail].  The reused one-output
    graph must see [packed :: level :: tail]. *)
Definition pairedCarrierCodeOrbitPublicRenaming (index : nat) : nat :=
  match index with
  | 0 => 0
  | 1 => 3
  | S (S tailIndex) => tailIndex + 4
  end.

Lemma raw_sat_pairedCarrierCodeOrbitPublicRenamedGraph_iff : forall
    (M : RawPAModel) packedGraph packed first second level tail,
  raw_formula_sat M
    (scons M packed (scons M first (scons M second
      (scons M level tail))))
    (Formula.rename pairedCarrierCodeOrbitPublicRenaming packedGraph) <->
  raw_formula_sat M
    (scons M packed (scons M level tail)) packedGraph.
Proof.
  intros M packedGraph packed first second level tail.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro index.
  destruct index as [|[|tailIndex]];
    cbn [pairedCarrierCodeOrbitPublicRenaming].
  - reflexivity.
  - reflexivity.
  - replace (tailIndex + 4) with (S (S (S (S tailIndex)))) by lia.
    reflexivity.
Qed.

Definition carrierIndexedPairedCodeOrbitGraph
    (baseGraph successorGraph : formula) : formula :=
  pEx
    (pAnd
      (pEq (tVar 0) (pairTerm (tVar 1) (tVar 2)))
      (Formula.rename pairedCarrierCodeOrbitPublicRenaming
        (carrierIndexedCodeOrbitGraph
          (pairedCarrierCodeOrbitPackedBaseGraph baseGraph)
          (pairedCarrierCodeOrbitPackedSuccessorGraph successorGraph)))).

Definition RawCarrierIndexedPairedCodeOrbitAt (M : RawPAModel)
    (baseGraph successorGraph : formula) (tail : nat -> M)
    (level first second : M) : Prop :=
  RawCarrierIndexedCodeOrbitAt M
    (pairedCarrierCodeOrbitPackedBaseGraph baseGraph)
    (pairedCarrierCodeOrbitPackedSuccessorGraph successorGraph)
    tail level (rawPolynomialPair M first second).

Arguments RawCarrierIndexedPairedCodeOrbitAt
  M baseGraph successorGraph tail level first second : clear implicits.

(** Exact output-first semantics.  The packed value is an existential
    witness equated to the transparent pair term; it is not decoded by the
    meta-theory. *)
Theorem raw_sat_carrierIndexedPairedCodeOrbitGraph_iff : forall
    (M : RawPAModel) baseGraph successorGraph tail level first second,
  raw_formula_sat M
    (scons M first (scons M second (scons M level tail)))
    (carrierIndexedPairedCodeOrbitGraph baseGraph successorGraph) <->
  RawCarrierIndexedPairedCodeOrbitAt M
    baseGraph successorGraph tail level first second.
Proof.
  intros M baseGraph successorGraph tail level first second.
  unfold carrierIndexedPairedCodeOrbitGraph,
    RawCarrierIndexedPairedCodeOrbitAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_pairedCarrierCodeOrbitPublicRenamedGraph_iff.
  setoid_rewrite raw_sat_carrierIndexedCodeOrbitGraph_iff.
  cbn [raw_term_eval scons]. split.
  - intros [packed [hpacked horbit]].
    rewrite hpacked in horbit. exact horbit.
  - intro horbit.
    exists (rawPolynomialPair M first second). split.
    + reflexivity.
    + exact horbit.
Qed.

(** ------------------------------------------------------------------
    Paired base and successor totality. *)

Definition RawCarrierIndexedPairedCodeOrbitBaseTotal (M : RawPAModel)
    (baseGraph : formula) : Prop :=
  forall tail : nat -> M,
    exists first second : M,
      raw_formula_sat M
        (scons M first (scons M second tail)) baseGraph.

Definition RawCarrierIndexedPairedCodeOrbitSuccessorTotal
    (M : RawPAModel) (successorGraph : formula) : Prop :=
  forall (tail : nat -> M) index previousFirst previousSecond,
    exists nextFirst nextSecond : M,
      raw_formula_sat M
        (scons M nextFirst (scons M nextSecond
          (scons M previousFirst (scons M previousSecond
            (scons M index tail))))) successorGraph.

Arguments RawCarrierIndexedPairedCodeOrbitBaseTotal M baseGraph
  : clear implicits.
Arguments RawCarrierIndexedPairedCodeOrbitSuccessorTotal M successorGraph
  : clear implicits.

Lemma raw_carrierIndexedPairedCodeOrbitAt_zero_of_base : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph tail first second,
  raw_formula_sat M
    (scons M first (scons M second tail)) baseGraph ->
  RawCarrierIndexedPairedCodeOrbitAt M
    baseGraph successorGraph tail (raw_zero M) first second.
Proof.
  intros M hPA baseGraph successorGraph tail first second hbase.
  unfold RawCarrierIndexedPairedCodeOrbitAt.
  apply (raw_carrierIndexedCodeOrbitAt_zero_of_base M hPA).
  apply (proj2
    (raw_sat_pairedCarrierCodeOrbitPackedBaseGraph_iff M
      baseGraph tail (rawPolynomialPair M first second))).
  exists first, second. split; [reflexivity | exact hbase].
Qed.

Lemma raw_carrierIndexedPairedCodeOrbitAt_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph tail level
      previousFirst previousSecond nextFirst nextSecond,
  RawCarrierIndexedPairedCodeOrbitAt M
    baseGraph successorGraph tail level previousFirst previousSecond ->
  raw_formula_sat M
    (scons M nextFirst (scons M nextSecond
      (scons M previousFirst (scons M previousSecond
        (scons M level tail))))) successorGraph ->
  RawCarrierIndexedPairedCodeOrbitAt M
    baseGraph successorGraph tail (raw_succ M level)
    nextFirst nextSecond.
Proof.
  intros M hPA baseGraph successorGraph tail level
    previousFirst previousSecond nextFirst nextSecond
    hprevious hsuccessor.
  unfold RawCarrierIndexedPairedCodeOrbitAt in hprevious |- *.
  apply (raw_carrierIndexedCodeOrbitAt_succ M hPA
    (pairedCarrierCodeOrbitPackedBaseGraph baseGraph)
    (pairedCarrierCodeOrbitPackedSuccessorGraph successorGraph)
    tail level (rawPolynomialPair M previousFirst previousSecond)
    (rawPolynomialPair M nextFirst nextSecond) hprevious).
  apply (proj2
    (raw_sat_pairedCarrierCodeOrbitPackedSuccessorGraph_iff M
      successorGraph tail level
      (rawPolynomialPair M previousFirst previousSecond)
      (rawPolynomialPair M nextFirst nextSecond))).
  exists nextFirst, nextSecond, previousFirst, previousSecond.
  repeat split; try reflexivity. exact hsuccessor.
Qed.

(** The existential closure is the represented induction invariant.  The
    order in which the two existential binders enter the environment is
    reversed below, so its semantic lemma explicitly swaps the witnesses. *)
Definition carrierIndexedPairedCodeOrbitExistsFormula
    (baseGraph successorGraph : formula) : formula :=
  pEx (pEx (carrierIndexedPairedCodeOrbitGraph baseGraph successorGraph)).

Lemma raw_sat_carrierIndexedPairedCodeOrbitExistsFormula_iff : forall
    (M : RawPAModel) baseGraph successorGraph tail level,
  raw_formula_sat M (scons M level tail)
    (carrierIndexedPairedCodeOrbitExistsFormula baseGraph successorGraph) <->
  exists first second : M,
    RawCarrierIndexedPairedCodeOrbitAt M
      baseGraph successorGraph tail level first second.
Proof.
  intros M baseGraph successorGraph tail level.
  unfold carrierIndexedPairedCodeOrbitExistsFormula.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_carrierIndexedPairedCodeOrbitGraph_iff.
  split.
  - intros [second [first horbit]].
    exists first, second. exact horbit.
  - intros [first [second horbit]].
    exists second, first. exact horbit.
Qed.

Lemma raw_carrierIndexedPairedCodeOrbitExists_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph tail,
  RawCarrierIndexedPairedCodeOrbitBaseTotal M baseGraph ->
  exists first second : M,
    RawCarrierIndexedPairedCodeOrbitAt M
      baseGraph successorGraph tail (raw_zero M) first second.
Proof.
  intros M hPA baseGraph successorGraph tail hbase.
  destruct (hbase tail) as (first & second & hbaseGraph).
  exists first, second.
  exact (raw_carrierIndexedPairedCodeOrbitAt_zero_of_base M hPA
    baseGraph successorGraph tail first second hbaseGraph).
Qed.

Lemma raw_carrierIndexedPairedCodeOrbitExists_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph tail,
  RawCarrierIndexedPairedCodeOrbitSuccessorTotal M successorGraph ->
  forall level,
  (exists previousFirst previousSecond : M,
    RawCarrierIndexedPairedCodeOrbitAt M
      baseGraph successorGraph tail level previousFirst previousSecond) ->
  exists nextFirst nextSecond : M,
    RawCarrierIndexedPairedCodeOrbitAt M
      baseGraph successorGraph tail (raw_succ M level)
      nextFirst nextSecond.
Proof.
  intros M hPA baseGraph successorGraph tail hsuccessor level
    (previousFirst & previousSecond & hprevious).
  destruct (hsuccessor tail level previousFirst previousSecond)
    as (nextFirst & nextSecond & hnext).
  exists nextFirst, nextSecond.
  exact (raw_carrierIndexedPairedCodeOrbitAt_succ M hPA
    baseGraph successorGraph tail level
    previousFirst previousSecond nextFirst nextSecond
    hprevious hnext).
Qed.

(** PA-definable induction reaches arbitrary carrier levels, not merely
    standard numerals supplied by the Rocq meta-theory. *)
Theorem raw_carrierIndexedPairedCodeOrbitExists_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph,
  RawCarrierIndexedPairedCodeOrbitBaseTotal M baseGraph ->
  RawCarrierIndexedPairedCodeOrbitSuccessorTotal M successorGraph ->
  forall (tail : nat -> M) level,
  exists first second : M,
    RawCarrierIndexedPairedCodeOrbitAt M
      baseGraph successorGraph tail level first second.
Proof.
  intros M hPA baseGraph successorGraph hbase hsuccessor tail.
  set (phi := carrierIndexedPairedCodeOrbitExistsFormula
    baseGraph successorGraph).
  assert (hall : forall level,
      raw_formula_sat M (scons M level tail) phi).
  {
    apply (raw_definable_induction M hPA phi tail).
    - unfold phi.
      apply (proj2
        (raw_sat_carrierIndexedPairedCodeOrbitExistsFormula_iff M
          baseGraph successorGraph tail (raw_zero M))).
      exact (raw_carrierIndexedPairedCodeOrbitExists_zero M hPA
        baseGraph successorGraph tail hbase).
    - intros level hlevelSat.
      unfold phi in hlevelSat |- *.
      pose proof (proj1
        (raw_sat_carrierIndexedPairedCodeOrbitExistsFormula_iff M
          baseGraph successorGraph tail level) hlevelSat) as hlevel.
      apply (proj2
        (raw_sat_carrierIndexedPairedCodeOrbitExistsFormula_iff M
          baseGraph successorGraph tail (raw_succ M level))).
      exact (raw_carrierIndexedPairedCodeOrbitExists_succ M hPA
        baseGraph successorGraph tail hsuccessor level hlevel).
  }
  intro level. unfold phi in hall.
  exact (proj1
    (raw_sat_carrierIndexedPairedCodeOrbitExistsFormula_iff M
      baseGraph successorGraph tail level) (hall level)).
Qed.

Definition RawCarrierIndexedPairedCodeOrbitGraphTotal (M : RawPAModel)
    (baseGraph successorGraph : formula) : Prop :=
  forall (tail : nat -> M) level,
    exists first second : M,
      raw_formula_sat M
        (scons M first (scons M second (scons M level tail)))
        (carrierIndexedPairedCodeOrbitGraph baseGraph successorGraph).

Arguments RawCarrierIndexedPairedCodeOrbitGraphTotal
  M baseGraph successorGraph : clear implicits.

Corollary raw_carrierIndexedPairedCodeOrbitGraph_total : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph,
  RawCarrierIndexedPairedCodeOrbitBaseTotal M baseGraph ->
  RawCarrierIndexedPairedCodeOrbitSuccessorTotal M successorGraph ->
  RawCarrierIndexedPairedCodeOrbitGraphTotal M baseGraph successorGraph.
Proof.
  intros M hPA baseGraph successorGraph hbase hsuccessor tail level.
  destruct (raw_carrierIndexedPairedCodeOrbitExists_all M hPA
    baseGraph successorGraph hbase hsuccessor tail level)
    as (first & second & horbit).
  exists first, second.
  exact (proj2
    (raw_sat_carrierIndexedPairedCodeOrbitGraph_iff M
      baseGraph successorGraph tail level first second) horbit).
Qed.

(** ------------------------------------------------------------------
    Exact zero and successor views. *)

Lemma raw_carrierIndexedPairedCodeOrbitAt_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph tail first second,
  RawCarrierIndexedPairedCodeOrbitAt M
    baseGraph successorGraph tail (raw_zero M) first second <->
  raw_formula_sat M
    (scons M first (scons M second tail)) baseGraph.
Proof.
  intros M hPA baseGraph successorGraph tail first second.
  unfold RawCarrierIndexedPairedCodeOrbitAt.
  rewrite (raw_carrierIndexedCodeOrbitAt_zero_iff M hPA).
  rewrite raw_sat_pairedCarrierCodeOrbitPackedBaseGraph_iff.
  split.
  - intros (baseFirst & baseSecond & hpacked & hbase).
    destruct (rawPolynomialPair_injective M hPA
      first second baseFirst baseSecond hpacked) as [hfirst hsecond].
    subst baseFirst. subst baseSecond. exact hbase.
  - intro hbase.
    exists first, second. split; [reflexivity | exact hbase].
Qed.

Lemma raw_carrierIndexedPairedCodeOrbitAt_succ_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph tail level nextFirst nextSecond,
  RawCarrierIndexedPairedCodeOrbitAt M
    baseGraph successorGraph tail (raw_succ M level)
    nextFirst nextSecond <->
  exists previousFirst previousSecond : M,
    RawCarrierIndexedPairedCodeOrbitAt M
      baseGraph successorGraph tail level previousFirst previousSecond /\
    raw_formula_sat M
      (scons M nextFirst (scons M nextSecond
        (scons M previousFirst (scons M previousSecond
          (scons M level tail))))) successorGraph.
Proof.
  intros M hPA baseGraph successorGraph tail level nextFirst nextSecond.
  unfold RawCarrierIndexedPairedCodeOrbitAt at 1.
  rewrite (raw_carrierIndexedCodeOrbitAt_succ_iff M hPA).
  split.
  - intros (packedPrevious & hprevious & hpackedSuccessor).
    apply (proj1
      (raw_sat_pairedCarrierCodeOrbitPackedSuccessorGraph_iff M
        successorGraph tail level packedPrevious
        (rawPolynomialPair M nextFirst nextSecond)))
      in hpackedSuccessor.
    destruct hpackedSuccessor as
      (rowNextFirst & rowNextSecond & previousFirst & previousSecond &
        hnextPacked & hpreviousPacked & hsuccessor).
    destruct (rawPolynomialPair_injective M hPA
      nextFirst nextSecond rowNextFirst rowNextSecond hnextPacked)
      as [hnextFirst hnextSecond].
    subst rowNextFirst. subst rowNextSecond.
    exists previousFirst, previousSecond. split.
    + unfold RawCarrierIndexedPairedCodeOrbitAt.
      rewrite <- hpreviousPacked. exact hprevious.
    + exact hsuccessor.
  - intros (previousFirst & previousSecond & hprevious & hsuccessor).
    exists (rawPolynomialPair M previousFirst previousSecond). split.
    + exact hprevious.
    + apply (proj2
        (raw_sat_pairedCarrierCodeOrbitPackedSuccessorGraph_iff M
          successorGraph tail level
          (rawPolynomialPair M previousFirst previousSecond)
          (rawPolynomialPair M nextFirst nextSecond))).
      exists nextFirst, nextSecond, previousFirst, previousSecond.
      repeat split; try reflexivity. exact hsuccessor.
Qed.

Theorem raw_carrierIndexedPairedCodeOrbitGraph_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph tail first second,
  raw_formula_sat M
    (scons M first (scons M second
      (scons M (raw_zero M) tail)))
    (carrierIndexedPairedCodeOrbitGraph baseGraph successorGraph) <->
  raw_formula_sat M
    (scons M first (scons M second tail)) baseGraph.
Proof.
  intros M hPA baseGraph successorGraph tail first second.
  rewrite raw_sat_carrierIndexedPairedCodeOrbitGraph_iff.
  exact (raw_carrierIndexedPairedCodeOrbitAt_zero_iff M hPA
    baseGraph successorGraph tail first second).
Qed.

Theorem raw_carrierIndexedPairedCodeOrbitGraph_succ_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph tail level nextFirst nextSecond,
  raw_formula_sat M
    (scons M nextFirst (scons M nextSecond
      (scons M (raw_succ M level) tail)))
    (carrierIndexedPairedCodeOrbitGraph baseGraph successorGraph) <->
  exists previousFirst previousSecond : M,
    raw_formula_sat M
      (scons M previousFirst (scons M previousSecond
        (scons M level tail)))
      (carrierIndexedPairedCodeOrbitGraph baseGraph successorGraph) /\
    raw_formula_sat M
      (scons M nextFirst (scons M nextSecond
        (scons M previousFirst (scons M previousSecond
          (scons M level tail))))) successorGraph.
Proof.
  intros M hPA baseGraph successorGraph tail level nextFirst nextSecond.
  rewrite raw_sat_carrierIndexedPairedCodeOrbitGraph_iff.
  rewrite (raw_carrierIndexedPairedCodeOrbitAt_succ_iff M hPA
    baseGraph successorGraph tail level nextFirst nextSecond).
  setoid_rewrite raw_sat_carrierIndexedPairedCodeOrbitGraph_iff.
  reflexivity.
Qed.

End PABoundedRawCodedCarrierIndexedPairedCodeOrbitGraph.
