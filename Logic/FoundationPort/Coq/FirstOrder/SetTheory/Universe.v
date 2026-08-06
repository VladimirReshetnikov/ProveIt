(** A representation-independent fragment of Foundation's standard Universe.

    The source constructs its Universe as a QPF fixpoint and then defines a
    choice set by applying a selected element function to every member of a
    family.  The uniqueness theorem for that choice set does not inspect the
    fixpoint: it uses only the selected-element specification, the image
    membership equation, nonemptiness of each family member, and pairwise
    disjointness.  Those four ingredients are packaged here without
    postulating a concrete Universe implementation. *)

From Foundation.FirstOrder.SetTheory Require Import Basic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** A choice operation consists of one selected element for every nonempty
    object and an image-like set operation recording those selections. *)
Record universe_choice_data (m : membership_structure) : Type := {
  universe_choice_one : membership_carrier m -> membership_carrier m;
  universe_choice_one_mem : forall x,
    set_model_is_nonempty x ->
    membership_rel (universe_choice_one x) x;
  universe_choice : membership_carrier m -> membership_carrier m;
  universe_choice_mem_iff : forall collection z,
    membership_rel z (universe_choice collection) <->
    exists x, membership_rel x collection /\
      z = universe_choice_one x
}.

Arguments universe_choice_one {m} _ _.
Arguments universe_choice_one_mem {m} _ _ _.
Arguments universe_choice {m} _ _.
Arguments universe_choice_mem_iff {m} _ _ _.

(** Source-shaped [Universe.choice_existsUnique], generalized by replacing
    the source's empty-object test with the exact nonemptiness premise that
    the proof consumes. *)
Theorem universe_choice_existsUnique : forall m
    (C : universe_choice_data m)
    (collection X : membership_carrier m),
  (forall Y, membership_rel Y collection ->
    set_model_is_nonempty Y) ->
  (forall Y Z,
    membership_rel Y collection ->
    membership_rel Z collection ->
    (exists w, membership_rel w Y /\ membership_rel w Z) ->
    Y = Z) ->
  membership_rel X collection ->
  exists! x, membership_rel x (universe_choice C collection) /\
    membership_rel x X.
Proof.
  intros m C collection X Hnonempty Hdisjoint hX.
  exists (universe_choice_one C X). split.
  - split.
    + apply (proj2 (universe_choice_mem_iff C collection
        (universe_choice_one C X))).
      exists X. split; [exact hX | reflexivity].
    + apply universe_choice_one_mem. exact (Hnonempty X hX).
  - intros y [hy_choice hyX].
    destruct (proj1 (universe_choice_mem_iff C collection y)
      hy_choice) as [Y [hY Hy]].
    assert (Hinter : exists w,
        membership_rel w Y /\ membership_rel w X).
    { exists (universe_choice_one C Y). split.
      - apply universe_choice_one_mem. exact (Hnonempty Y hY).
      - rewrite <- Hy. exact hyX. }
    assert (HXY : Y = X).
    { apply Hdisjoint; [exact hY | exact hX | exact Hinter]. }
    now rewrite HXY in Hy.
Qed.

Print Assumptions universe_choice_existsUnique.
