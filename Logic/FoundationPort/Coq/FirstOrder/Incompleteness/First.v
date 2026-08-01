(** Semantic consequences of first incompleteness.

    Foundation specializes these results to arithmetic truth in the natural
    numbers.  The selection argument itself needs only that truth is
    bivalent and that a false formula has a true negation. *)

From FoundationModal Require Import Syntax LogicInfrastructure.
From Foundation.FirstOrder.Incompleteness Require Import
  ProvabilityAbstraction.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Every independent formula has a true, still-unprovable orientation.
    Making the truth split explicit keeps this theorem constructive. *)
Theorem pa_exists_true_unprovable_of_incomplete : forall (A : Type)
    (L truth : modal_logic_set A),
  (forall p, truth p \/ ~ truth p) ->
  (forall p, ~ truth p -> truth (Neg p)) ->
  pa_incomplete L ->
  exists sigma, truth sigma /\ ~ L sigma.
Proof.
  intros A L truth Htruth_cases Hneg_complete
    [sigma [Hunprovable Hunrefutable]].
  destruct (Htruth_cases sigma) as [Htrue | Hfalse].
  - exists sigma. now split.
  - exists (Neg sigma). split.
    + now apply Hneg_complete.
    + exact Hunrefutable.
Qed.

(** If all theorems of an incomplete predicate are true, the complete truth
    predicate is strictly stronger.  This factors the source instance
    [T strictly weaker than true arithmetic] from its arithmetic adapters. *)
Theorem pa_incomplete_strictly_weaker_than_truth : forall (A : Type)
    (L truth : modal_logic_set A),
  logic_subset L truth ->
  (forall p, truth p \/ ~ truth p) ->
  (forall p, ~ truth p -> truth (Neg p)) ->
  pa_incomplete L ->
  logic_strictly_weaker L truth.
Proof.
  intros A L truth Hsound Htruth_cases Hneg_complete Hincomplete.
  destruct (pa_exists_true_unprovable_of_incomplete
    Htruth_cases Hneg_complete Hincomplete)
    as [sigma [Htrue Hunprovable]].
  split; [exact Hsound |].
  exists sigma. now split.
Qed.
