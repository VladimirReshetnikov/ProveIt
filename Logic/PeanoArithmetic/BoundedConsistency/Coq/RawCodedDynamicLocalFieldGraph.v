(**
  The represented zero/successor splice for a dynamic local field.

  The Lean local coordinate selects a fixed base bundle at zero and the
  positive local-bundle orbit at the model predecessor of every nonzero
  index.  Coq does not yet expose the lower model-coded truth-formula orbit,
  nor output-first graphs for the four local component formula codes.  It
  would therefore be unsound to name a concrete augmented-local-bundle graph
  here.

  This module closes the largest independent graph layer: given an
  output-first base graph and an output-first positive/predecessor graph, it
  constructs their model-indexed splice.  The graph is read under

      output :: level :: tail.

  Its positive branch existentially exposes [predecessor], checks
  [level = S predecessor], and renames the supplied graph so that it is read
  under [output :: predecessor :: tail].  All binder bookkeeping has exact
  semantics in every raw arithmetic structure.  PA is used only for the
  zero/successor views and for totality at an arbitrary (possibly
  nonstandard) carrier level.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedSyntaxConstructorSeparation.

Module PABoundedRawCodedDynamicLocalFieldGraph.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructorSeparation.

(** Under the positive branch's existential binder the environment is

      predecessor :: output :: level :: tail.

    A supplied positive graph expects [output :: predecessor :: tail]. *)
Definition dynamicLocalPositiveRenaming (index : nat) : nat :=
  match index with
  | 0 => 1
  | 1 => 0
  | S (S tailIndex) => S (S (S tailIndex))
  end.

Lemma raw_sat_dynamicLocalPositiveRenamedGraph_iff : forall
    (M : RawPAModel) positiveGraph predecessor output level tail,
  raw_formula_sat M
    (scons M predecessor (scons M output (scons M level tail)))
    (Formula.rename dynamicLocalPositiveRenaming positiveGraph) <->
  raw_formula_sat M
    (scons M output (scons M predecessor tail)) positiveGraph.
Proof.
  intros M positiveGraph predecessor output level tail.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro index.
  destruct index as [|[|tailIndex]]; reflexivity.
Qed.

(** Output-first zero/positive splice.  The base graph is evaluated at the
    actual zero level.  The positive graph is evaluated at the predecessor
    selected by the existential branch. *)
Definition dynamicLocalFieldGraph
    (baseGraph positiveGraph : formula) : formula :=
  pOr
    (pAnd (pEq (tVar 1) tZero) baseGraph)
    (pEx
      (pAnd
        (pEq (tVar 2) (tSucc (tVar 0)))
        (Formula.rename dynamicLocalPositiveRenaming positiveGraph))).

Definition RawDynamicLocalFieldGraphAt (M : RawPAModel)
    (baseGraph positiveGraph : formula)
    (tail : nat -> M) (level output : M) : Prop :=
  (level = raw_zero M /\
    raw_formula_sat M (scons M output (scons M level tail)) baseGraph) \/
  exists predecessor : M,
    level = raw_succ M predecessor /\
    raw_formula_sat M
      (scons M output (scons M predecessor tail)) positiveGraph.

Arguments RawDynamicLocalFieldGraphAt
  M baseGraph positiveGraph tail level output : clear implicits.

(** Exact arbitrary-structure semantics of the represented graph. *)
Theorem raw_sat_dynamicLocalFieldGraph_iff : forall
    (M : RawPAModel) baseGraph positiveGraph tail level output,
  raw_formula_sat M (scons M output (scons M level tail))
    (dynamicLocalFieldGraph baseGraph positiveGraph) <->
  RawDynamicLocalFieldGraphAt M
    baseGraph positiveGraph tail level output.
Proof.
  intros M baseGraph positiveGraph tail level output.
  unfold dynamicLocalFieldGraph, RawDynamicLocalFieldGraphAt.
  cbn [raw_formula_sat raw_term_eval scons].
  setoid_rewrite raw_sat_dynamicLocalPositiveRenamedGraph_iff.
  reflexivity.
Qed.

(** The two component-totality interfaces are deliberately explicit.  They
    are exactly the concrete lower-level facts still required from future
    augmented-local-bundle code graphs. *)
Definition RawDynamicLocalBaseGraphTotal (M : RawPAModel)
    (baseGraph : formula) : Prop :=
  forall tail : nat -> M,
    exists output : M,
      raw_formula_sat M
        (scons M output (scons M (raw_zero M) tail)) baseGraph.

Definition RawDynamicLocalPositiveGraphTotal (M : RawPAModel)
    (positiveGraph : formula) : Prop :=
  forall (tail : nat -> M) predecessor,
    exists output : M,
      raw_formula_sat M
        (scons M output (scons M predecessor tail)) positiveGraph.

Arguments RawDynamicLocalBaseGraphTotal M baseGraph : clear implicits.
Arguments RawDynamicLocalPositiveGraphTotal M positiveGraph
  : clear implicits.

Definition RawDynamicLocalFieldGraphTotal (M : RawPAModel)
    (baseGraph positiveGraph : formula) : Prop :=
  forall (tail : nat -> M) level,
    exists output : M,
      raw_formula_sat M (scons M output (scons M level tail))
        (dynamicLocalFieldGraph baseGraph positiveGraph).

Arguments RawDynamicLocalFieldGraphTotal
  M baseGraph positiveGraph : clear implicits.

(** Totality reaches nonstandard carrier levels because PA itself supplies
    the zero-or-successor decomposition. *)
Theorem raw_dynamicLocalFieldGraph_total : forall
    (M : RawPAModel), RawPASatisfies M -> forall baseGraph positiveGraph,
  RawDynamicLocalBaseGraphTotal M baseGraph ->
  RawDynamicLocalPositiveGraphTotal M positiveGraph ->
  RawDynamicLocalFieldGraphTotal M baseGraph positiveGraph.
Proof.
  intros M hPA baseGraph positiveGraph hbase hpositive tail level.
  destruct (raw_assignment_zero_or_successor M hPA level)
    as [hzero | [predecessor hsuccessor]].
  - subst level.
    destruct (hbase tail) as [output houtput].
    exists output.
    apply (proj2 (raw_sat_dynamicLocalFieldGraph_iff M
      baseGraph positiveGraph tail (raw_zero M) output)).
    left. split; [reflexivity | exact houtput].
  - destruct (hpositive tail predecessor) as [output houtput].
    exists output.
    apply (proj2 (raw_sat_dynamicLocalFieldGraph_iff M
      baseGraph positiveGraph tail level output)).
    right. exists predecessor. split; assumption.
Qed.

(** At zero the positive branch is impossible in every PA model. *)
Theorem raw_dynamicLocalFieldGraph_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph positiveGraph tail output,
  raw_formula_sat M
    (scons M output (scons M (raw_zero M) tail))
    (dynamicLocalFieldGraph baseGraph positiveGraph) <->
  raw_formula_sat M
    (scons M output (scons M (raw_zero M) tail)) baseGraph.
Proof.
  intros M hPA baseGraph positiveGraph tail output.
  rewrite raw_sat_dynamicLocalFieldGraph_iff.
  unfold RawDynamicLocalFieldGraphAt. split.
  - intros [[_ hbase] | [predecessor [hzero _]]].
    + exact hbase.
    + exfalso.
      exact (raw_zero_not_succ_syntax M hPA predecessor hzero).
  - intro hbase. left. split; [reflexivity | exact hbase].
Qed.

(** At a successor the base branch is impossible and successor injectivity
    identifies the existential predecessor with the supplied level. *)
Theorem raw_dynamicLocalFieldGraph_succ_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph positiveGraph tail level output,
  raw_formula_sat M
    (scons M output (scons M (raw_succ M level) tail))
    (dynamicLocalFieldGraph baseGraph positiveGraph) <->
  raw_formula_sat M
    (scons M output (scons M level tail)) positiveGraph.
Proof.
  intros M hPA baseGraph positiveGraph tail level output.
  rewrite raw_sat_dynamicLocalFieldGraph_iff.
  unfold RawDynamicLocalFieldGraphAt. split.
  - intros [[hsuccessorZero _] |
      [predecessor [hsuccessors hpositive]]].
    + exfalso.
      exact (raw_zero_not_succ_syntax M hPA level
        (eq_sym hsuccessorZero)).
    + assert (hpredecessor : level = predecessor).
      {
        exact (raw_succ_injective_syntax M hPA
          level predecessor hsuccessors).
      }
      subst predecessor. exact hpositive.
  - intro hpositive. right.
    exists level. split; [reflexivity | exact hpositive].
Qed.

End PABoundedRawCodedDynamicLocalFieldGraph.
