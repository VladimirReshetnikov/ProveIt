(** Generic axiom schemes underlying arithmetic induction theories. *)

From FoundationModal Require Import GenericEntailment.
From Foundation.Syntax.Predicate Require Import Language.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition first_order_axiom_scheme {L : language} {I : Type}
    (C : I -> Prop) (axiom : I -> sentence L) : theory L :=
  fun sigma => exists i, C i /\ sigma = axiom i.

Definition first_order_theory_union {L : language}
    (T U : theory L) : theory L :=
  fun sigma => T sigma \/ U sigma.

Lemma first_order_axiom_scheme_intro : forall L I
    (C : I -> Prop) (axiom : I -> sentence L) i,
  C i -> first_order_axiom_scheme C axiom (axiom i).
Proof.
  intros L I C axiom i Hi. exists i. now split.
Qed.

Lemma first_order_axiom_scheme_subset : forall L I
    (C D : I -> Prop) (axiom : I -> sentence L),
  (forall i, C i -> D i) ->
  forall sigma, first_order_axiom_scheme C axiom sigma ->
    first_order_axiom_scheme D axiom sigma.
Proof.
  intros L I C D axiom HCD sigma [i [Hi ->]].
  exists i. split; [now apply HCD | reflexivity].
Qed.

Lemma first_order_theory_union_mono_right : forall L
    (T U V : theory L),
  (forall sigma, U sigma -> V sigma) ->
  forall sigma, first_order_theory_union T U sigma ->
    first_order_theory_union T V sigma.
Proof.
  intros L T U V HUV sigma [HT | HU].
  - now left.
  - right. now apply HUV.
Qed.

Lemma first_order_scheme_union_subset : forall L I
    (T : theory L) (C D : I -> Prop) (axiom : I -> sentence L),
  (forall i, C i -> D i) ->
  forall sigma,
    first_order_theory_union T (first_order_axiom_scheme C axiom) sigma ->
    first_order_theory_union T (first_order_axiom_scheme D axiom) sigma.
Proof.
  intros L I T C D axiom HCD.
  apply first_order_theory_union_mono_right.
  now apply first_order_axiom_scheme_subset.
Qed.

Theorem first_order_scheme_union_weaker : forall L I
    (T : theory L) (C D : I -> Prop) (axiom : I -> sentence L),
  (forall i, C i -> D i) ->
  generic_weaker_than
    (first_order_theory_entailment L) (first_order_theory_entailment L)
    (first_order_theory_union T (first_order_axiom_scheme C axiom))
    (first_order_theory_union T (first_order_axiom_scheme D axiom)).
Proof.
  intros L I T C D axiom HCD.
  apply first_order_theory_weaker_of_subset.
  now apply first_order_scheme_union_subset.
Qed.

Definition arithmetic_induction_scheme
    (C : semiproposition oring_language 1 -> Prop)
    (induction_axiom : semiproposition oring_language 1 ->
      sentence oring_language) : theory oring_language :=
  first_order_axiom_scheme C induction_axiom.

Lemma arithmetic_induction_scheme_intro : forall C induction_axiom phi,
  C phi -> arithmetic_induction_scheme C induction_axiom
    (induction_axiom phi).
Proof.
  intros. apply first_order_axiom_scheme_intro. assumption.
Qed.

Lemma arithmetic_induction_scheme_subset : forall C D induction_axiom,
  (forall phi, C phi -> D phi) ->
  forall sigma,
    arithmetic_induction_scheme C induction_axiom sigma ->
    arithmetic_induction_scheme D induction_axiom sigma.
Proof.
  intros. eapply first_order_axiom_scheme_subset; eauto.
Qed.
