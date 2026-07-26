(**
  Deep-closure-preserving carrier-indexed paired code orbits.

  The invariant in this file is represented by an actual PA formula.  It
  combines the ordinary paired orbit graph with two instances of
  [codedTernaryPredicateDeepClosedTermAt].  Thus its semantic witnesses are
  not merely closed at the public cutoff three: they are fixed by every
  represented shift and substitution whose carrier-valued cutoff is at least
  three.

  The successor interface is guarded by that same invariant.  This avoids
  asking a graph to preserve deep closure on malformed or unreachable input
  codes.  The orbit level is an arbitrary element of a PA model, and the
  existence proof uses [raw_definable_induction], not metatheoretic induction
  on Rocq's [nat].
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedFormulaOperations
  RawCodedFixedLevelTruthTotality
  RawCodedCarrierIndexedPairedCodeOrbitGraph
  RawCodedCarrierIndexedPairedAdequateCodeOrbitGraph
  RawCodedTernaryPredicateDeepClosure.

Module PABoundedRawCodedCarrierIndexedPairedDeepClosedCodeOrbitGraph.

Import PA.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedCarrierIndexedPairedCodeOrbitGraph.
Import PABoundedRawCodedCarrierIndexedPairedAdequateCodeOrbitGraph.
Import PABoundedRawCodedTernaryPredicateDeepClosure.

(** Honest base and guarded-successor interfaces for the refined orbit. *)
Definition RawCarrierIndexedPairedDeepClosedCodeOrbitBaseTotal
    (M : RawPAModel) (baseGraph : formula) : Prop :=
  forall tail : nat -> M,
    exists first second : M,
      raw_formula_sat M
        (scons M first (scons M second tail)) baseGraph /\
      RawCodedTernaryPredicateDeepClosed M first /\
      RawCodedTernaryPredicateDeepClosed M second.

Definition RawCarrierIndexedPairedDeepClosedCodeOrbitSuccessorTotal
    (M : RawPAModel) (successorGraph : formula) : Prop :=
  forall (tail : nat -> M) index previousFirst previousSecond,
    RawCodedTernaryPredicateDeepClosed M previousFirst ->
    RawCodedTernaryPredicateDeepClosed M previousSecond ->
    exists nextFirst nextSecond : M,
      raw_formula_sat M
        (scons M nextFirst (scons M nextSecond
          (scons M previousFirst (scons M previousSecond
            (scons M index tail))))) successorGraph /\
      RawCodedTernaryPredicateDeepClosed M nextFirst /\
      RawCodedTernaryPredicateDeepClosed M nextSecond.

Arguments RawCarrierIndexedPairedDeepClosedCodeOrbitBaseTotal
  M baseGraph : clear implicits.
Arguments RawCarrierIndexedPairedDeepClosedCodeOrbitSuccessorTotal
  M successorGraph : clear implicits.

(** We retain the adequate-orbit view explicitly for downstream clients.
    Adequacy is not an extra premise: it is projected from deep closure. *)
Definition RawCarrierIndexedPairedDeepClosedCodeOrbitAt
    (M : RawPAModel) (baseGraph successorGraph : formula)
    (tail : nat -> M) (level first second : M) : Prop :=
  RawCarrierIndexedPairedAdequateCodeOrbitAt M
    baseGraph successorGraph tail level first second /\
  RawCodedTernaryPredicateDeepClosed M first /\
  RawCodedTernaryPredicateDeepClosed M second.

Arguments RawCarrierIndexedPairedDeepClosedCodeOrbitAt
  M baseGraph successorGraph tail level first second : clear implicits.

(** Beneath the two existential binders the environment is

      first :: second :: level :: tail.

    The displayed variable indices therefore match the convention already
    used by the ordinary paired orbit graph. *)
Definition carrierIndexedPairedDeepClosedCodeOrbitExistsFormula
    (baseGraph successorGraph : formula) : formula :=
  pEx (pEx
    (operationAnd3
      (carrierIndexedPairedCodeOrbitGraph baseGraph successorGraph)
      (codedTernaryPredicateDeepClosedTermAt (tVar 0))
      (codedTernaryPredicateDeepClosedTermAt (tVar 1)))).

(** Exact semantics of the represented invariant. *)
Lemma raw_sat_carrierIndexedPairedDeepClosedCodeOrbitExistsFormula_iff :
  forall (M : RawPAModel) baseGraph successorGraph tail level,
  raw_formula_sat M (scons M level tail)
    (carrierIndexedPairedDeepClosedCodeOrbitExistsFormula
      baseGraph successorGraph) <->
  exists first second : M,
    RawCarrierIndexedPairedDeepClosedCodeOrbitAt M
      baseGraph successorGraph tail level first second.
Proof.
  intros M baseGraph successorGraph tail level.
  unfold carrierIndexedPairedDeepClosedCodeOrbitExistsFormula,
    RawCarrierIndexedPairedDeepClosedCodeOrbitAt,
    RawCarrierIndexedPairedAdequateCodeOrbitAt, operationAnd3.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_carrierIndexedPairedCodeOrbitGraph_iff.
  setoid_rewrite raw_sat_codedTernaryPredicateDeepClosedTermAt_iff.
  cbn [raw_term_eval scons].
  split.
  - intros [second [first [horbit [hfirst hsecond]]]].
    exists first, second. split.
    + split; [exact horbit |].
      split; [exact (proj1 hfirst) | exact (proj1 hsecond)].
    + split; assumption.
  - intros [first [second [[horbit [hfirstAdequate hsecondAdequate]]
      [hfirst hsecond]]]].
    exists second, first. exact (conj horbit (conj hfirst hsecond)).
Qed.

Lemma raw_carrierIndexedPairedDeepClosedCodeOrbitExists_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph tail,
  RawCarrierIndexedPairedDeepClosedCodeOrbitBaseTotal M baseGraph ->
  exists first second : M,
    RawCarrierIndexedPairedDeepClosedCodeOrbitAt M
      baseGraph successorGraph tail (raw_zero M) first second.
Proof.
  intros M hPA baseGraph successorGraph tail hbase.
  destruct (hbase tail) as
    (first & second & hbaseGraph & hfirst & hsecond).
  exists first, second. split.
  - split.
    + exact (raw_carrierIndexedPairedCodeOrbitAt_zero_of_base M hPA
        baseGraph successorGraph tail first second hbaseGraph).
    + split; [exact (proj1 hfirst) | exact (proj1 hsecond)].
  - split; assumption.
Qed.

Lemma raw_carrierIndexedPairedDeepClosedCodeOrbitExists_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph tail,
  RawCarrierIndexedPairedDeepClosedCodeOrbitSuccessorTotal
    M successorGraph ->
  forall level,
  (exists previousFirst previousSecond : M,
    RawCarrierIndexedPairedDeepClosedCodeOrbitAt M
      baseGraph successorGraph tail level
      previousFirst previousSecond) ->
  exists nextFirst nextSecond : M,
    RawCarrierIndexedPairedDeepClosedCodeOrbitAt M
      baseGraph successorGraph tail (raw_succ M level)
      nextFirst nextSecond.
Proof.
  intros M hPA baseGraph successorGraph tail hsuccessor level
    (previousFirst & previousSecond &
     [[hprevious [hpreviousFirstAdequate hpreviousSecondAdequate]]
      [hpreviousFirst hpreviousSecond]]).
  destruct (hsuccessor tail level previousFirst previousSecond
    hpreviousFirst hpreviousSecond) as
    (nextFirst & nextSecond & hnext & hnextFirst & hnextSecond).
  exists nextFirst, nextSecond. split.
  - split.
    + exact (raw_carrierIndexedPairedCodeOrbitAt_succ M hPA
        baseGraph successorGraph tail level previousFirst previousSecond
        nextFirst nextSecond hprevious hnext).
    + split; [exact (proj1 hnextFirst) | exact (proj1 hnextSecond)].
  - split; assumption.
Qed.

(** PA-definable induction gives witnesses at every carrier level, including
    nonstandard levels of a nonstandard model. *)
Theorem raw_carrierIndexedPairedDeepClosedCodeOrbitExists_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph,
  RawCarrierIndexedPairedDeepClosedCodeOrbitBaseTotal M baseGraph ->
  RawCarrierIndexedPairedDeepClosedCodeOrbitSuccessorTotal
    M successorGraph ->
  forall (tail : nat -> M) level,
  exists first second : M,
    RawCarrierIndexedPairedDeepClosedCodeOrbitAt M
      baseGraph successorGraph tail level first second.
Proof.
  intros M hPA baseGraph successorGraph hbase hsuccessor tail.
  set (phi := carrierIndexedPairedDeepClosedCodeOrbitExistsFormula
    baseGraph successorGraph).
  assert (hall : forall level,
      raw_formula_sat M (scons M level tail) phi).
  {
    apply (raw_definable_induction M hPA phi tail).
    - unfold phi.
      apply (proj2
        (raw_sat_carrierIndexedPairedDeepClosedCodeOrbitExistsFormula_iff M
          baseGraph successorGraph tail (raw_zero M))).
      exact (raw_carrierIndexedPairedDeepClosedCodeOrbitExists_zero M hPA
        baseGraph successorGraph tail hbase).
    - intros level hlevelSat.
      unfold phi in hlevelSat |- *.
      pose proof (proj1
        (raw_sat_carrierIndexedPairedDeepClosedCodeOrbitExistsFormula_iff M
          baseGraph successorGraph tail level) hlevelSat) as hlevel.
      apply (proj2
        (raw_sat_carrierIndexedPairedDeepClosedCodeOrbitExistsFormula_iff M
          baseGraph successorGraph tail (raw_succ M level))).
      exact (raw_carrierIndexedPairedDeepClosedCodeOrbitExists_succ M hPA
        baseGraph successorGraph tail hsuccessor level hlevel).
  }
  intro level. unfold phi in hall.
  exact (proj1
    (raw_sat_carrierIndexedPairedDeepClosedCodeOrbitExistsFormula_iff M
      baseGraph successorGraph tail level) (hall level)).
Qed.

(** Expanded graph-facing form used by dynamic-truth clients. *)
Definition RawCarrierIndexedPairedDeepClosedCodeOrbitGraphTotal
    (M : RawPAModel) (baseGraph successorGraph : formula) : Prop :=
  forall (tail : nat -> M) level,
    exists first second : M,
      raw_formula_sat M
        (scons M first (scons M second (scons M level tail)))
        (carrierIndexedPairedCodeOrbitGraph baseGraph successorGraph) /\
      RawCodedTernaryPredicateDeepClosed M first /\
      RawCodedTernaryPredicateDeepClosed M second.

Arguments RawCarrierIndexedPairedDeepClosedCodeOrbitGraphTotal
  M baseGraph successorGraph : clear implicits.

Corollary raw_carrierIndexedPairedDeepClosedCodeOrbitGraph_total : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph,
  RawCarrierIndexedPairedDeepClosedCodeOrbitBaseTotal M baseGraph ->
  RawCarrierIndexedPairedDeepClosedCodeOrbitSuccessorTotal
    M successorGraph ->
  RawCarrierIndexedPairedDeepClosedCodeOrbitGraphTotal
    M baseGraph successorGraph.
Proof.
  intros M hPA baseGraph successorGraph hbase hsuccessor tail level.
  destruct (raw_carrierIndexedPairedDeepClosedCodeOrbitExists_all M hPA
    baseGraph successorGraph hbase hsuccessor tail level) as
    (first & second & [[horbit [hfirstAdequate hsecondAdequate]]
      [hfirst hsecond]]).
  exists first, second. split.
  - exact (proj2
      (raw_sat_carrierIndexedPairedCodeOrbitGraph_iff M
        baseGraph successorGraph tail level first second) horbit).
  - exact (conj hfirst hsecond).
Qed.

End PABoundedRawCodedCarrierIndexedPairedDeepClosedCodeOrbitGraph.
