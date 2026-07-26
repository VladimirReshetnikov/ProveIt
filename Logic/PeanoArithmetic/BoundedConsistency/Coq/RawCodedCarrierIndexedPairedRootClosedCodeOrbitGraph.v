(**
  Root-closure-preserving carrier-indexed paired code orbits.

  This is the root-closed refinement of
  [RawCodedCarrierIndexedPairedAdequateCodeOrbitGraph].  Its invariant is an
  actual PA formula: it existentially selects both visible orbit coordinates
  and asserts the represented root-closure formula for each.  The base and
  successor interfaces ask for closure only along closure-certified states,
  exactly the states reachable from the base.

  The induction below is [raw_definable_induction] in the arbitrary PA
  model.  It therefore covers every carrier element, including nonstandard
  ones; no metatheoretic induction over [nat] is used for the orbit level.
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
  RawCodedTemplateTernaryApplication
  RawCodedTernaryPredicateRootClosureFormula.

Module PABoundedRawCodedCarrierIndexedPairedRootClosedCodeOrbitGraph.

Import PA.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedCarrierIndexedPairedCodeOrbitGraph.
Import PABoundedRawCodedCarrierIndexedPairedAdequateCodeOrbitGraph.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTernaryPredicateRootClosureFormula.

(** Honest totality interfaces.  The successor relation is deliberately not
    required to preserve closure from malformed or merely adequate inputs. *)
Definition RawCarrierIndexedPairedRootClosedCodeOrbitBaseTotal
    (M : RawPAModel) (baseGraph : formula) : Prop :=
  forall tail : nat -> M,
    exists first second : M,
      raw_formula_sat M
        (scons M first (scons M second tail)) baseGraph /\
      RawCodedTernaryPredicateRootClosed M first /\
      RawCodedTernaryPredicateRootClosed M second.

Definition RawCarrierIndexedPairedRootClosedCodeOrbitSuccessorTotal
    (M : RawPAModel) (successorGraph : formula) : Prop :=
  forall (tail : nat -> M) index previousFirst previousSecond,
    RawCodedTernaryPredicateRootClosed M previousFirst ->
    RawCodedTernaryPredicateRootClosed M previousSecond ->
    exists nextFirst nextSecond : M,
      raw_formula_sat M
        (scons M nextFirst (scons M nextSecond
          (scons M previousFirst (scons M previousSecond
            (scons M index tail))))) successorGraph /\
      RawCodedTernaryPredicateRootClosed M nextFirst /\
      RawCodedTernaryPredicateRootClosed M nextSecond.

Arguments RawCarrierIndexedPairedRootClosedCodeOrbitBaseTotal
  M baseGraph : clear implicits.
Arguments RawCarrierIndexedPairedRootClosedCodeOrbitSuccessorTotal
  M successorGraph : clear implicits.

(** The adequate orbit is retained explicitly.  Although root closure already
    contains adequacy, retaining this layer makes the refinement relationship
    and downstream reuse transparent. *)
Definition RawCarrierIndexedPairedRootClosedCodeOrbitAt
    (M : RawPAModel) (baseGraph successorGraph : formula)
    (tail : nat -> M) (level first second : M) : Prop :=
  RawCarrierIndexedPairedAdequateCodeOrbitAt M
    baseGraph successorGraph tail level first second /\
  RawCodedTernaryPredicateRootClosed M first /\
  RawCodedTernaryPredicateRootClosed M second.

Arguments RawCarrierIndexedPairedRootClosedCodeOrbitAt
  M baseGraph successorGraph tail level first second : clear implicits.

(** Beneath the two existential binders the body sees
    [first :: second :: level :: tail]. *)
Definition carrierIndexedPairedRootClosedCodeOrbitExistsFormula
    (baseGraph successorGraph : formula) : formula :=
  pEx (pEx
    (operationAnd3
      (carrierIndexedPairedCodeOrbitGraph baseGraph successorGraph)
      (codedTernaryPredicateRootClosedTermAt (tVar 0))
      (codedTernaryPredicateRootClosedTermAt (tVar 1)))).

(** Exact semantics of the represented invariant.  The two adequacy facts in
    the refined orbit are projections of the two root-closure certificates,
    not extra semantic assumptions hidden in the formula. *)
Lemma raw_sat_carrierIndexedPairedRootClosedCodeOrbitExistsFormula_iff :
  forall (M : RawPAModel) baseGraph successorGraph tail level,
  raw_formula_sat M (scons M level tail)
    (carrierIndexedPairedRootClosedCodeOrbitExistsFormula
      baseGraph successorGraph) <->
  exists first second : M,
    RawCarrierIndexedPairedRootClosedCodeOrbitAt M
      baseGraph successorGraph tail level first second.
Proof.
  intros M baseGraph successorGraph tail level.
  unfold carrierIndexedPairedRootClosedCodeOrbitExistsFormula,
    RawCarrierIndexedPairedRootClosedCodeOrbitAt,
    RawCarrierIndexedPairedAdequateCodeOrbitAt, operationAnd3.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_carrierIndexedPairedCodeOrbitGraph_iff.
  setoid_rewrite raw_sat_codedTernaryPredicateRootClosedTermAt_iff.
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

Lemma raw_carrierIndexedPairedRootClosedCodeOrbitExists_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph tail,
  RawCarrierIndexedPairedRootClosedCodeOrbitBaseTotal M baseGraph ->
  exists first second : M,
    RawCarrierIndexedPairedRootClosedCodeOrbitAt M
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

Lemma raw_carrierIndexedPairedRootClosedCodeOrbitExists_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph tail,
  RawCarrierIndexedPairedRootClosedCodeOrbitSuccessorTotal
    M successorGraph ->
  forall level,
  (exists previousFirst previousSecond : M,
    RawCarrierIndexedPairedRootClosedCodeOrbitAt M
      baseGraph successorGraph tail level
      previousFirst previousSecond) ->
  exists nextFirst nextSecond : M,
    RawCarrierIndexedPairedRootClosedCodeOrbitAt M
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

(** The quantified conclusion ranges over the carrier [M], not over Rocq's
    [nat].  The only induction principle invoked is PA-definable induction on
    the arithmetized existential invariant above. *)
Theorem raw_carrierIndexedPairedRootClosedCodeOrbitExists_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph,
  RawCarrierIndexedPairedRootClosedCodeOrbitBaseTotal M baseGraph ->
  RawCarrierIndexedPairedRootClosedCodeOrbitSuccessorTotal M successorGraph ->
  forall (tail : nat -> M) level,
  exists first second : M,
    RawCarrierIndexedPairedRootClosedCodeOrbitAt M
      baseGraph successorGraph tail level first second.
Proof.
  intros M hPA baseGraph successorGraph hbase hsuccessor tail.
  set (phi := carrierIndexedPairedRootClosedCodeOrbitExistsFormula
    baseGraph successorGraph).
  assert (hall : forall level,
      raw_formula_sat M (scons M level tail) phi).
  {
    apply (raw_definable_induction M hPA phi tail).
    - unfold phi.
      apply (proj2
        (raw_sat_carrierIndexedPairedRootClosedCodeOrbitExistsFormula_iff M
          baseGraph successorGraph tail (raw_zero M))).
      exact (raw_carrierIndexedPairedRootClosedCodeOrbitExists_zero M hPA
        baseGraph successorGraph tail hbase).
    - intros level hlevelSat.
      unfold phi in hlevelSat |- *.
      pose proof (proj1
        (raw_sat_carrierIndexedPairedRootClosedCodeOrbitExistsFormula_iff M
          baseGraph successorGraph tail level) hlevelSat) as hlevel.
      apply (proj2
        (raw_sat_carrierIndexedPairedRootClosedCodeOrbitExistsFormula_iff M
          baseGraph successorGraph tail (raw_succ M level))).
      exact (raw_carrierIndexedPairedRootClosedCodeOrbitExists_succ M hPA
        baseGraph successorGraph tail hsuccessor level hlevel).
  }
  intro level. unfold phi in hall.
  exact (proj1
    (raw_sat_carrierIndexedPairedRootClosedCodeOrbitExistsFormula_iff M
      baseGraph successorGraph tail level) (hall level)).
Qed.

(** Convenient graph-facing totality: ordinary orbit satisfaction is kept
    alongside both closure certificates. *)
Definition RawCarrierIndexedPairedRootClosedCodeOrbitGraphTotal
    (M : RawPAModel) (baseGraph successorGraph : formula) : Prop :=
  forall (tail : nat -> M) level,
    exists first second : M,
      raw_formula_sat M
        (scons M first (scons M second (scons M level tail)))
        (carrierIndexedPairedCodeOrbitGraph baseGraph successorGraph) /\
      RawCodedTernaryPredicateRootClosed M first /\
      RawCodedTernaryPredicateRootClosed M second.

Arguments RawCarrierIndexedPairedRootClosedCodeOrbitGraphTotal
  M baseGraph successorGraph : clear implicits.

Corollary raw_carrierIndexedPairedRootClosedCodeOrbitGraph_total : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph successorGraph,
  RawCarrierIndexedPairedRootClosedCodeOrbitBaseTotal M baseGraph ->
  RawCarrierIndexedPairedRootClosedCodeOrbitSuccessorTotal M successorGraph ->
  RawCarrierIndexedPairedRootClosedCodeOrbitGraphTotal
    M baseGraph successorGraph.
Proof.
  intros M hPA baseGraph successorGraph hbase hsuccessor tail level.
  destruct (raw_carrierIndexedPairedRootClosedCodeOrbitExists_all M hPA
    baseGraph successorGraph hbase hsuccessor tail level) as
    (first & second & [[horbit [hfirstAdequate hsecondAdequate]]
      [hfirst hsecond]]).
  exists first, second. split.
  - exact (proj2
      (raw_sat_carrierIndexedPairedCodeOrbitGraph_iff M
        baseGraph successorGraph tail level first second) horbit).
  - exact (conj hfirst hsecond).
Qed.

End PABoundedRawCodedCarrierIndexedPairedRootClosedCodeOrbitGraph.
