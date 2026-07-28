(**
  Generic weak converse well-foundedness.

  This module independently ports the complete eight-declaration surface of
  the pinned Foundation module [Vorspiel/Rel/WCWF.lean].  As in Foundation,
  a relation is weakly converse well-founded when deleting its reflexive
  edges makes it converse well founded.  The public statements remain about
  arbitrary relations; the existing frame-specialized presentation is a
  downstream adapter of the same notion.

  Foundation proves the finite theorem through an infinite-chain argument.
  Here the main theorem instead reuses the finite transitive irreflexive
  result from [ConverseWellFounded]: the irreflexive generator of a
  transitive antisymmetric relation is transitive and irreflexive.  The two
  chain-building helpers are nevertheless retained at their exact source
  boundaries.  Relational choice is needed only by [wcwf_dependent_choice];
  the remaining classical boundary is propositional excluded middle, also
  present in the upstream development.
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.Classical_Prop Logic.ClassicalChoice.
From Stdlib Require Import Relations.Relation_Definitions.
From FoundationModal Require Import
  ConverseWellFounded FrameProperties RelationProperties.

Import ListNotations.
Import FrameProperties RelationProperties.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Source declaration 1/8: [WeaklyConverseWellFounded]. *)
Definition weakly_converse_well_founded {A : Type}
    (R : A -> A -> Prop) : Prop :=
  converse_well_founded (relation_irreflexive_generator R).

(** Source declaration 2/8: [IsWeaklyConverseWellFounded]. *)
Record is_weakly_converse_well_founded (A : Type)
    (R : A -> A -> Prop) : Prop := {
  relation_wcwf : weakly_converse_well_founded R
}.

Arguments relation_wcwf {A R} _.

(** Source declaration 3/8: [dependent_choice].  The prefix avoids a
    collision with Stdlib's stronger, data-valued theorem of that name. *)
Lemma wcwf_dependent_choice :
  forall (A : Type) (R : A -> A -> Prop),
    (exists X : A -> Prop,
      (exists x, X x) /\
      forall a, X a -> exists b, X b /\ R a b) ->
    exists f : nat -> A, forall n, R (f n) (f (S n)).
Proof.
  intros A R [X [[x Hx] Hstep]].
  assert (Hnext : forall a : {z : A | X z},
      exists b : {z : A | X z}, R (proj1_sig a) (proj1_sig b)).
  {
    intros [a Ha]; simpl.
    destruct (Hstep a Ha) as [b [Hb Rab]].
    now exists (exist _ b Hb).
  }
  destruct (@choice {z : A | X z} {z : A | X z}
      (fun a b => R (proj1_sig a) (proj1_sig b)) Hnext)
    as [next Hnext_ok].
  exists (fun n =>
    proj1_sig (Nat.iter n next (exist (fun z => X z) x Hx))).
  intro n. rewrite Nat.iter_succ.
  apply Hnext_ok.
Qed.

(** Proposition-valued counterparts of Foundation's [Infinite] and strict
    [LinearOrder] interfaces.  A finite cover may contain duplicates. *)
Definition relation_infinite (A : Type) : Prop :=
  forall cover : list A, exists x : A, ~ In x cover.

Record relation_linear_order (A : Type)
    (lt : A -> A -> Prop) : Prop := {
  relation_lt_irreflexive : forall x, ~ lt x x;
  relation_lt_transitive : transitive A lt;
  relation_lt_trichotomy : forall x y, lt x y \/ x = y \/ lt y x
}.

Arguments relation_lt_irreflexive {A lt} _ _.
Arguments relation_lt_transitive {A lt} _ _ _ _ _ _.
Arguments relation_lt_trichotomy {A lt} _ _ _.

Lemma relation_infinite_nodup_list :
  forall A : Type, relation_infinite A ->
    forall n, exists xs : list A, length xs = n /\ NoDup xs.
Proof.
  intros A Hinf n; induction n as [|n IH].
  - exists []; split; [reflexivity | constructor].
  - destruct IH as [xs [Hlength Hnodup]].
    destruct (Hinf xs) as [x Hfresh].
    exists (x :: xs); split.
    + simpl. now rewrite Hlength.
    + now constructor.
Qed.

Lemma wcwf_nodup_map_of_injective_on :
  forall (A B : Type) (f : A -> B) (xs : list A),
    NoDup xs ->
    (forall x y, In x xs -> In y xs -> f x = f y -> x = y) ->
    NoDup (map f xs).
Proof.
  intros A B f xs Hnodup.
  induction Hnodup as [|a xs Hnotin Hnodup IH]; intro Hinjective.
  - constructor.
  - simpl. constructor.
    + intro Hmapped.
      apply in_map_iff in Hmapped.
      destruct Hmapped as [b [Hfb Hbin]].
      apply Hnotin. assert (Hab : a = b).
      { apply Hinjective; [now left | now right |]. now symmetry. }
      now subst b.
    + apply IH. intros x y Hxin Hyin Heq.
      apply Hinjective; [now right | now right | exact Heq].
Qed.

(** Source declaration 4/8:
    [Finite.exists_ne_map_eq_of_infinite_lt]. *)
Lemma finite_exists_ne_map_eq_of_infinite_lt :
  forall (A B : Type) (lt : A -> A -> Prop) (f : A -> B),
    relation_linear_order lt -> relation_infinite A -> relation_finite B ->
    exists x y : A, lt x y /\ f x = f y.
Proof.
  intros A B lt f Horder Hinf [cover Hcover].
  destruct (relation_infinite_nodup_list Hinf (S (length cover)))
    as [xs [Hlength Hnodup]].
  assert (Hmap_not_nodup : ~ NoDup (map f xs)).
  {
    intro Hmap_nodup.
    pose proof (NoDup_incl_length Hmap_nodup
      (fun b Hb => Hcover b)) as Hle.
    rewrite length_map, Hlength in Hle. lia.
  }
  assert (Hcollision : exists x y : A,
      In x xs /\ In y xs /\ x <> y /\ f x = f y).
  {
    apply NNPP. intro Hnone.
    apply Hmap_not_nodup.
    apply wcwf_nodup_map_of_injective_on; [exact Hnodup |].
    intros x y Hxin Hyin Heq.
    apply NNPP. intro Hneq.
    apply Hnone. now exists x, y.
  }
  destruct Hcollision as [x [y [_ [_ [Hneq Heq]]]]].
  destruct (relation_lt_trichotomy Horder x y)
    as [Hxy | [Hxy | Hyx]].
  - now exists x, y.
  - contradiction.
  - exists y, x; split; [exact Hyx | now symmetry].
Qed.

(** Source declaration 5/8:
    [antisymm_of_weaklyConverseWellFounded]. *)
Lemma antisymmetric_of_weakly_converse_well_founded :
  forall (A : Type) (R : A -> A -> Prop),
    weakly_converse_well_founded R -> antisymmetric A R.
Proof.
  intros A R Hweak x y Rxy Ryx.
  unfold weakly_converse_well_founded in Hweak.
  pose proof (@converse_well_founded_has_max A
    (relation_irreflexive_generator R) Hweak) as Hmax.
  destruct (Hmax (fun z => z = x \/ z = y))
    as [m [Hm Hmaximal]].
  - exists x. now left.
  - destruct Hm as [-> | ->].
    + apply NNPP. intro Hneq.
      exact (Hmaximal y (or_intror eq_refl) (conj Rxy Hneq)).
    + apply NNPP. intro Hneq.
      apply (Hmaximal x (or_introl eq_refl)).
      split; [exact Ryx |]. intro Hyx. apply Hneq. now symmetry.
Qed.

(** Source declaration 6/8: the [Std.Antisymm] instance induced by
    [IsWeaklyConverseWellFounded]. *)
Definition weakly_converse_well_founded_is_antisymmetric
    (A : Type) (R : A -> A -> Prop)
    (Hweak : @is_weakly_converse_well_founded A R)
    : antisymmetric A R :=
  antisymmetric_of_weakly_converse_well_founded (relation_wcwf Hweak).

(** Source declaration 7/8:
    [weaklyConverseWellFounded_of_finite_trans_antisymm]. *)
Theorem weakly_converse_well_founded_of_finite_transitive_antisymmetric :
  forall (A : Type) (R : A -> A -> Prop),
    relation_finite A -> transitive A R -> antisymmetric A R ->
    weakly_converse_well_founded R.
Proof.
  intros A R Hfinite Htrans Hanti.
  unfold weakly_converse_well_founded.
  apply finite_converse_well_founded_of_transitive_irreflexive.
  - exact Hfinite.
  - now apply relation_irreflexive_generator_transitive.
  - apply relation_irreflexive_generator_irreflexive.
Qed.

(** Source declaration 8/8: the finite/transitive/antisymmetric
    [IsWeaklyConverseWellFounded] instance. *)
Definition finite_transitive_antisymmetric_is_weakly_converse_well_founded
    (A : Type) (R : A -> A -> Prop)
    (Hfinite : relation_finite A) (Htrans : transitive A R)
    (Hanti : antisymmetric A R)
    : @is_weakly_converse_well_founded A R :=
  {| relation_wcwf :=
       weakly_converse_well_founded_of_finite_transitive_antisymmetric
         Hfinite Htrans Hanti |}.
