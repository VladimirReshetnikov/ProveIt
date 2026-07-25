(**
  Adequacy-preserving carrier-indexed paired code orbits.

  The underlying output-first paired orbit graph is unchanged.  This module
  strengthens its existence theorem by carrying
  [RawCodedFormulaAtomicallyAdequate] for both visible coordinates through
  the same PA-definable induction.  The successor interface is intentionally
  required only on adequate previous coordinates—the only states reachable
  from an adequate base—and must return adequate next coordinates.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedFormulaOperations RawCodedFixedLevelTruthTotality
  RawCodedCarrierIndexedPairedCodeOrbitGraph.

Module PABoundedRawCodedCarrierIndexedPairedAdequateCodeOrbitGraph.

Import PA.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedCarrierIndexedPairedCodeOrbitGraph.

(** Honest totality interfaces.  No branch is requested for malformed or
    non-adequate previous coordinates. *)
Definition RawCarrierIndexedPairedAdequateCodeOrbitBaseTotal
    (M : RawPAModel) (baseGraph : formula) : Prop :=
  forall tail : nat -> M,
    exists first second : M,
      raw_formula_sat M
        (scons M first (scons M second tail)) baseGraph /\
      RawCodedFormulaAtomicallyAdequate M first /\
      RawCodedFormulaAtomicallyAdequate M second.

Definition RawCarrierIndexedPairedAdequateCodeOrbitSuccessorTotal
    (M : RawPAModel) (successorGraph : formula) : Prop :=
  forall (tail : nat -> M) index previousFirst previousSecond,
    RawCodedFormulaAtomicallyAdequate M previousFirst ->
    RawCodedFormulaAtomicallyAdequate M previousSecond ->
    exists nextFirst nextSecond : M,
      raw_formula_sat M
        (scons M nextFirst (scons M nextSecond
          (scons M previousFirst (scons M previousSecond
            (scons M index tail))))) successorGraph /\
      RawCodedFormulaAtomicallyAdequate M nextFirst /\
      RawCodedFormulaAtomicallyAdequate M nextSecond.

Arguments RawCarrierIndexedPairedAdequateCodeOrbitBaseTotal
  M baseGraph : clear implicits.
Arguments RawCarrierIndexedPairedAdequateCodeOrbitSuccessorTotal
  M successorGraph : clear implicits.

Definition RawCarrierIndexedPairedAdequateCodeOrbitAt
    (M : RawPAModel) (baseGraph successorGraph : formula)
    (tail : nat -> M) (level first second : M) : Prop :=
  RawCarrierIndexedPairedCodeOrbitAt M
    baseGraph successorGraph tail level first second /\
  RawCodedFormulaAtomicallyAdequate M first /\
  RawCodedFormulaAtomicallyAdequate M second.

Arguments RawCarrierIndexedPairedAdequateCodeOrbitAt
  M baseGraph successorGraph tail level first second : clear implicits.

(** Beneath the two existential binders the body sees
    [first :: second :: level :: tail]. *)
Definition carrierIndexedPairedAdequateCodeOrbitExistsFormula
    (baseGraph successorGraph : formula) : formula :=
  pEx (pEx
    (operationAnd3
      (carrierIndexedPairedCodeOrbitGraph baseGraph successorGraph)
      (codedFormulaAtomicallyAdequateTermAt (tVar 0))
      (codedFormulaAtomicallyAdequateTermAt (tVar 1)))).

Lemma raw_sat_carrierIndexedPairedAdequateCodeOrbitExistsFormula_iff :
  forall (M : RawPAModel) baseGraph successorGraph tail level,
  raw_formula_sat M (scons M level tail)
    (carrierIndexedPairedAdequateCodeOrbitExistsFormula
      baseGraph successorGraph) <->
  exists first second : M,
    RawCarrierIndexedPairedAdequateCodeOrbitAt M
      baseGraph successorGraph tail level first second.
Proof.
  intros M baseGraph successorGraph tail level.
  unfold carrierIndexedPairedAdequateCodeOrbitExistsFormula,
    RawCarrierIndexedPairedAdequateCodeOrbitAt, operationAnd3.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_carrierIndexedPairedCodeOrbitGraph_iff.
  setoid_rewrite raw_sat_codedFormulaAtomicallyAdequateTermAt_iff.
  cbn [raw_term_eval scons].
  split.
  - intros [second [first [horbit [hfirst hsecond]]]].
    exists first, second. repeat split; assumption.
  - intros [first [second [horbit [hfirst hsecond]]]].
    exists second, first. repeat split; assumption.
Qed.

Lemma raw_carrierIndexedPairedAdequateCodeOrbitExists_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph tail,
  RawCarrierIndexedPairedAdequateCodeOrbitBaseTotal M baseGraph ->
  exists first second : M,
    RawCarrierIndexedPairedAdequateCodeOrbitAt M
      baseGraph successorGraph tail (raw_zero M) first second.
Proof.
  intros M hPA baseGraph successorGraph tail hbase.
  destruct (hbase tail) as
    (first & second & hbaseGraph & hfirst & hsecond).
  exists first, second. repeat split; try assumption.
  exact (raw_carrierIndexedPairedCodeOrbitAt_zero_of_base M hPA
    baseGraph successorGraph tail first second hbaseGraph).
Qed.

Lemma raw_carrierIndexedPairedAdequateCodeOrbitExists_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph tail,
  RawCarrierIndexedPairedAdequateCodeOrbitSuccessorTotal
    M successorGraph ->
  forall level,
  (exists previousFirst previousSecond : M,
    RawCarrierIndexedPairedAdequateCodeOrbitAt M
      baseGraph successorGraph tail level
      previousFirst previousSecond) ->
  exists nextFirst nextSecond : M,
    RawCarrierIndexedPairedAdequateCodeOrbitAt M
      baseGraph successorGraph tail (raw_succ M level)
      nextFirst nextSecond.
Proof.
  intros M hPA baseGraph successorGraph tail hsuccessor level
    (previousFirst & previousSecond & hprevious &
     hpreviousFirst & hpreviousSecond).
  destruct (hsuccessor tail level previousFirst previousSecond
    hpreviousFirst hpreviousSecond) as
    (nextFirst & nextSecond & hnext & hnextFirst & hnextSecond).
  exists nextFirst, nextSecond. repeat split; try assumption.
  exact (raw_carrierIndexedPairedCodeOrbitAt_succ M hPA
    baseGraph successorGraph tail level
    previousFirst previousSecond nextFirst nextSecond
    hprevious hnext).
Qed.

(** PA induction applies to the represented existential invariant, so the
    result covers arbitrary nonstandard carrier levels. *)
Theorem raw_carrierIndexedPairedAdequateCodeOrbitExists_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph,
  RawCarrierIndexedPairedAdequateCodeOrbitBaseTotal M baseGraph ->
  RawCarrierIndexedPairedAdequateCodeOrbitSuccessorTotal M successorGraph ->
  forall (tail : nat -> M) level,
  exists first second : M,
    RawCarrierIndexedPairedAdequateCodeOrbitAt M
      baseGraph successorGraph tail level first second.
Proof.
  intros M hPA baseGraph successorGraph hbase hsuccessor tail.
  set (phi := carrierIndexedPairedAdequateCodeOrbitExistsFormula
    baseGraph successorGraph).
  assert (hall : forall level,
      raw_formula_sat M (scons M level tail) phi).
  {
    apply (raw_definable_induction M hPA phi tail).
    - unfold phi.
      apply (proj2
        (raw_sat_carrierIndexedPairedAdequateCodeOrbitExistsFormula_iff M
          baseGraph successorGraph tail (raw_zero M))).
      exact (raw_carrierIndexedPairedAdequateCodeOrbitExists_zero M hPA
        baseGraph successorGraph tail hbase).
    - intros level hlevelSat.
      unfold phi in hlevelSat |- *.
      pose proof (proj1
        (raw_sat_carrierIndexedPairedAdequateCodeOrbitExistsFormula_iff M
          baseGraph successorGraph tail level) hlevelSat) as hlevel.
      apply (proj2
        (raw_sat_carrierIndexedPairedAdequateCodeOrbitExistsFormula_iff M
          baseGraph successorGraph tail (raw_succ M level))).
      exact (raw_carrierIndexedPairedAdequateCodeOrbitExists_succ M hPA
        baseGraph successorGraph tail hsuccessor level hlevel).
  }
  intro level. unfold phi in hall.
  exact (proj1
    (raw_sat_carrierIndexedPairedAdequateCodeOrbitExistsFormula_iff M
      baseGraph successorGraph tail level) (hall level)).
Qed.

Definition RawCarrierIndexedPairedAdequateCodeOrbitGraphTotal
    (M : RawPAModel) (baseGraph successorGraph : formula) : Prop :=
  forall (tail : nat -> M) level,
    exists first second : M,
      raw_formula_sat M
        (scons M first (scons M second (scons M level tail)))
        (carrierIndexedPairedCodeOrbitGraph baseGraph successorGraph) /\
      RawCodedFormulaAtomicallyAdequate M first /\
      RawCodedFormulaAtomicallyAdequate M second.

Arguments RawCarrierIndexedPairedAdequateCodeOrbitGraphTotal
  M baseGraph successorGraph : clear implicits.

Corollary raw_carrierIndexedPairedAdequateCodeOrbitGraph_total : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph,
  RawCarrierIndexedPairedAdequateCodeOrbitBaseTotal M baseGraph ->
  RawCarrierIndexedPairedAdequateCodeOrbitSuccessorTotal M successorGraph ->
  RawCarrierIndexedPairedAdequateCodeOrbitGraphTotal
    M baseGraph successorGraph.
Proof.
  intros M hPA baseGraph successorGraph hbase hsuccessor tail level.
  destruct (raw_carrierIndexedPairedAdequateCodeOrbitExists_all M hPA
    baseGraph successorGraph hbase hsuccessor tail level) as
    (first & second & horbit & hfirst & hsecond).
  exists first, second. repeat split; try assumption.
  exact (proj2
    (raw_sat_carrierIndexedPairedCodeOrbitGraph_iff M
      baseGraph successorGraph tail level first second) horbit).
Qed.

End PABoundedRawCodedCarrierIndexedPairedAdequateCodeOrbitGraph.
