(** Complete lattices of fixed points of an arbitrary closure operator. *)

From Foundation.Vorspiel.Order Require Import Dense.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record closure_order_data (A : Type) := {
  closure_order : preorder_data A;
  closure_apply : A -> A;
  closure_extensive : forall x,
    preorder_le closure_order x (closure_apply x);
  closure_monotone : forall x y,
    preorder_le closure_order x y ->
    preorder_le closure_order (closure_apply x) (closure_apply y);
  closure_idempotent : forall x,
    preorder_le closure_order
      (closure_apply (closure_apply x)) (closure_apply x)
}.

Arguments closure_apply {A} _ _.

Definition closure_le {A} (C : closure_order_data A) : A -> A -> Prop :=
  preorder_le (closure_order C).

Definition closure_equiv {A} (C : closure_order_data A) (x y : A) : Prop :=
  closure_le C x y /\ closure_le C y x.

Definition closure_fixed {A} (C : closure_order_data A) (x : A) : Prop :=
  closure_le C (closure_apply C x) x.

Record regular_element {A} (C : closure_order_data A) := {
  regular_value : A;
  regular_value_fixed : closure_fixed C regular_value
}.

Arguments regular_value {A C} _.

Definition regular_le {A} {C : closure_order_data A}
    (x y : regular_element C) : Prop :=
  closure_le C (regular_value x) (regular_value y).

Definition regular_order_equiv {A} {C : closure_order_data A}
    (x y : regular_element C) : Prop :=
  regular_le x y /\ regular_le y x.

Definition closure_regularize {A} (C : closure_order_data A) (x : A) :
    regular_element C :=
  {| regular_value := closure_apply C x;
     regular_value_fixed := closure_idempotent C x |}.

Lemma regular_value_equiv_closure : forall A (C : closure_order_data A)
    (x : regular_element C),
  closure_equiv C (closure_apply C (regular_value x))
    (regular_value x).
Proof.
  intros A C x. split.
  - apply regular_value_fixed.
  - apply closure_extensive.
Qed.

Lemma regular_le_refl : forall A (C : closure_order_data A)
    (x : regular_element C),
  regular_le x x.
Proof. intros A C x. apply preorder_refl. Qed.

Lemma regular_le_trans : forall A (C : closure_order_data A)
    (x y z : regular_element C),
  regular_le x y -> regular_le y z -> regular_le x z.
Proof. intros A C x y z Hxy Hyz. eapply preorder_trans; eauto. Qed.

Definition regular_family_sup {A} (C : closure_order_data A) I
    (a : I -> regular_element C) (sup : A) : regular_element C :=
  closure_regularize C sup.

Lemma regular_family_sup_value : forall A (C : closure_order_data A)
    I (a : I -> regular_element C) sup,
  regular_value (@regular_family_sup A C I a sup) = closure_apply C sup.
Proof. reflexivity. Qed.

Lemma regular_family_sup_contains : forall A (C : closure_order_data A)
    I (a : I -> regular_element C) sup,
  (forall i, closure_le C (regular_value (a i)) sup) ->
  forall i, regular_le (a i) (@regular_family_sup A C I a sup).
Proof.
  intros A C I a sup Hupper i. eapply preorder_trans.
  - apply Hupper.
  - apply closure_extensive.
Qed.

Theorem regular_family_sup_least : forall A (C : closure_order_data A)
    I (a : I -> regular_element C) sup,
  (forall i, closure_le C (regular_value (a i)) sup) ->
  (forall x,
    (forall i, closure_le C (regular_value (a i)) x) ->
    closure_le C sup x) ->
  forall z : regular_element C,
    (forall i, regular_le (a i) z) ->
    regular_le (@regular_family_sup A C I a sup) z.
Proof.
  intros A C I a sup Hupper Hleast z Hz.
  eapply (@preorder_trans A (closure_order C)
    (closure_apply C sup) (closure_apply C (regular_value z))
    (regular_value z)).
  - apply closure_monotone. now apply Hleast.
  - exact (regular_value_fixed z).
Qed.

Definition regular_family_inf {A} (C : closure_order_data A) I
    (a : I -> regular_element C) (inf : A)
    (Hlower : forall i, closure_le C inf (regular_value (a i)))
    (Hgreatest : forall x,
      (forall i, closure_le C x (regular_value (a i))) ->
      closure_le C x inf) :
    regular_element C.
Proof.
  refine {| regular_value := inf |}.
  apply Hgreatest. intro i. eapply preorder_trans.
  - apply closure_monotone. apply Hlower.
  - exact (regular_value_fixed (a i)).
Defined.

Lemma regular_family_inf_value : forall A (C : closure_order_data A)
    I (a : I -> regular_element C) inf Hlower Hgreatest,
  regular_value (@regular_family_inf A C I a inf Hlower Hgreatest) = inf.
Proof. reflexivity. Qed.

Lemma regular_family_inf_below : forall A (C : closure_order_data A)
    I (a : I -> regular_element C) inf Hlower Hgreatest i,
  regular_le (@regular_family_inf A C I a inf Hlower Hgreatest) (a i).
Proof. intros A C I a inf Hlower Hgreatest i. apply Hlower. Qed.

Theorem regular_family_inf_greatest : forall A
    (C : closure_order_data A) I (a : I -> regular_element C) inf Hlower
    (Hgreatest : forall x,
    (forall i, closure_le C x (regular_value (a i))) ->
    closure_le C x inf),
  forall z : regular_element C,
    (forall i, regular_le z (a i)) ->
    regular_le z (@regular_family_inf A C I a inf Hlower Hgreatest).
Proof. intros A C I a inf Hlower Hgreatest z Hz. now apply Hgreatest. Qed.

Theorem regular_family_sup_universal : forall A
    (C : closure_order_data A) I (a : I -> regular_element C) sup,
  (forall i, closure_le C (regular_value (a i)) sup) ->
  (forall x,
    (forall i, closure_le C (regular_value (a i)) x) ->
    closure_le C sup x) ->
  forall z : regular_element C,
  regular_le (@regular_family_sup A C I a sup) z <->
  forall i, regular_le (a i) z.
Proof.
  intros A C I a sup Hupper Hleast z. split.
  - intros H i. eapply regular_le_trans.
    + now apply regular_family_sup_contains.
    + exact H.
  - now apply regular_family_sup_least.
Qed.

Theorem regular_family_inf_universal : forall A
    (C : closure_order_data A) I (a : I -> regular_element C) inf Hlower
    (Hgreatest : forall x,
    (forall i, closure_le C x (regular_value (a i))) ->
    closure_le C x inf),
  forall z : regular_element C,
  regular_le z (@regular_family_inf A C I a inf Hlower Hgreatest) <->
  forall i, regular_le z (a i).
Proof.
  intros A C I a inf Hlower Hgreatest z. split.
  - intros H i. eapply regular_le_trans.
    + exact H.
    + apply regular_family_inf_below.
  - now apply regular_family_inf_greatest.
Qed.
