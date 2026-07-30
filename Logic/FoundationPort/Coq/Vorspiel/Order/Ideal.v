(** Ideals over a minimal bounded join-semilattice interface. *)

From Stdlib Require Import Lists.List.
From Foundation.Vorspiel.List Require Import Basic.
From Foundation.Vorspiel.Order Require Import Dense.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record join_order_data (A : Type) := {
  jo_order : preorder_data A;
  jo_join : A -> A -> A;
  jo_le_join_left : forall x y, preorder_le jo_order x (jo_join x y);
  jo_le_join_right : forall x y, preorder_le jo_order y (jo_join x y);
  jo_join_le : forall x y z,
    preorder_le jo_order x z -> preorder_le jo_order y z ->
    preorder_le jo_order (jo_join x y) z;
  jo_bottom : A;
  jo_bottom_le : forall x, preorder_le jo_order jo_bottom x
}.

Arguments jo_join {A} _ _ _.
Arguments jo_bottom {A} _.

Definition jo_le {A} (J : join_order_data A) : A -> A -> Prop :=
  preorder_le (jo_order J).

Record order_ideal {A} (J : join_order_data A) := {
  ideal_member : A -> Prop;
  ideal_bottom_member : ideal_member (jo_bottom J);
  ideal_lower : forall x y,
    jo_le J y x -> ideal_member x -> ideal_member y;
  ideal_join_member : forall x y,
    ideal_member x -> ideal_member y ->
    ideal_member (jo_join J x y)
}.

Arguments ideal_member {A J} _ _.

Definition ideal_subset {A} {J : join_order_data A}
    (I K : order_ideal J) : Prop :=
  forall x, ideal_member I x -> ideal_member K x.

Definition principal_ideal {A} (J : join_order_data A) (a : A) :
    order_ideal J.
Proof.
  refine {| ideal_member := fun x => jo_le J x a |}.
  - apply jo_bottom_le.
  - intros x y Hyx Hxa.
    exact (@preorder_trans A (jo_order J) y x a Hyx Hxa).
  - intros x y Hx Hy. now apply jo_join_le.
Defined.

Lemma principal_ideal_member_iff : forall A (J : join_order_data A) a x,
  ideal_member (principal_ideal J a) x <-> jo_le J x a.
Proof. reflexivity. Qed.

Definition bottom_ideal {A} (J : join_order_data A) : order_ideal J :=
  principal_ideal J (jo_bottom J).

Lemma bottom_ideal_member_iff : forall A (J : join_order_data A) x,
  ideal_member (bottom_ideal J) x <-> jo_le J x (jo_bottom J).
Proof. reflexivity. Qed.

Corollary bottom_ideal_member_eq_iff : forall A
    (J : join_order_data A),
  (forall x y, jo_le J x y -> jo_le J y x -> x = y) ->
  forall x, ideal_member (bottom_ideal J) x <-> x = jo_bottom J.
Proof.
  intros A J Hantisym x. rewrite bottom_ideal_member_iff. split.
  - intro Hx. apply Hantisym; [exact Hx | apply jo_bottom_le].
  - intros ->. apply preorder_refl.
Qed.

Lemma principal_ideal_least : forall A (J : join_order_data A)
    (I : order_ideal J) a,
  ideal_subset (principal_ideal J a) I <-> ideal_member I a.
Proof.
  intros A J I a. split.
  - intro H. apply H. apply preorder_refl.
  - intros Ha x Hx. exact (@ideal_lower A J I a x Hx Ha).
Qed.

Definition ideal_join_list {A} (J : join_order_data A) (xs : list A) : A :=
  list_join (jo_join J) (jo_bottom J) xs.

Lemma ideal_join_list_member_bound : forall A (J : join_order_data A)
    xs x,
  List.In x xs -> jo_le J x (ideal_join_list J xs).
Proof.
  intros A J xs x Hx. unfold ideal_join_list.
  apply (@list_member_le_join A (jo_le J) (jo_join J) (jo_bottom J)).
  - apply preorder_trans.
  - apply jo_le_join_left.
  - apply jo_le_join_right.
  - exact Hx.
Qed.

Lemma ideal_join_list_least_upper : forall A (J : join_order_data A)
    xs z,
  (forall x, List.In x xs -> jo_le J x z) ->
  jo_le J (ideal_join_list J xs) z.
Proof.
  intros A J xs. induction xs as [|x xs IH]; intros z Hall.
  - simpl. apply jo_bottom_le.
  - simpl. apply jo_join_le.
    + apply Hall. now left.
    + apply IH. intros y Hy. apply Hall. now right.
Qed.

Lemma ideal_join_list_member : forall A (J : join_order_data A)
    (I : order_ideal J) xs,
  (forall x, List.In x xs -> ideal_member I x) ->
  ideal_member I (ideal_join_list J xs).
Proof.
  intros A J I xs Hall. induction xs as [|x xs IH].
  - apply ideal_bottom_member.
  - simpl. apply ideal_join_member.
    + apply Hall. now left.
    + apply IH. intros y Hy. apply Hall. now right.
Qed.

Theorem principal_ideal_join_list_least : forall A
    (J : join_order_data A) (I : order_ideal J) xs,
  ideal_subset (principal_ideal J (ideal_join_list J xs)) I <->
  forall x, List.In x xs -> ideal_member I x.
Proof.
  intros A J I xs. split.
  - intros H x Hx. apply H. apply ideal_join_list_member_bound. exact Hx.
  - intro Hall. apply (proj2 (principal_ideal_least I _)).
    now apply ideal_join_list_member.
Qed.

Theorem ideal_supremum_member_downward : forall A
    (J : join_order_data A) (I : order_ideal J)
    (S : A -> Prop) sup,
  (forall x, S x -> jo_le J x sup) ->
  ideal_member I sup ->
  forall x, S x -> ideal_member I x.
Proof.
  intros A J I S sup Hupper Hsup x Hx.
  exact (@ideal_lower A J I sup x (Hupper x Hx) Hsup).
Qed.

Definition ideal_proper {A} {J : join_order_data A}
    (I : order_ideal J) : Prop :=
  ~ forall x, ideal_member I x.

Theorem ideal_proper_iff_top_not_member : forall A
    (J : join_order_data A) (I : order_ideal J) top,
  (forall x, jo_le J x top) ->
  (ideal_proper I <-> ~ ideal_member I top).
Proof.
  intros A J I top Htop. split.
  - intros Hproper Hmember. apply Hproper. intro x.
    exact (@ideal_lower A J I top x (Htop x) Hmember).
  - intros Hnot Hall. apply Hnot. apply Hall.
Qed.

Record ideal_prime_pair {A} (J : join_order_data A) := {
  prime_pair_ideal : order_ideal J;
  prime_pair_filter : A -> Prop;
  prime_pair_cover : forall x,
    ideal_member prime_pair_ideal x \/ prime_pair_filter x;
  prime_pair_disjoint : forall x,
    ideal_member prime_pair_ideal x -> ~ prime_pair_filter x
}.

Arguments prime_pair_filter {A J} _ _.

Lemma prime_pair_not_filter_iff_ideal : forall A
    (J : join_order_data A) (P : ideal_prime_pair J) x,
  ~ prime_pair_filter P x <-> ideal_member (prime_pair_ideal P) x.
Proof.
  intros A J P x. split.
  - intro Hnot. destruct (prime_pair_cover P x); [assumption | contradiction].
  - apply prime_pair_disjoint.
Qed.

Lemma prime_pair_not_ideal_iff_filter : forall A
    (J : join_order_data A) (P : ideal_prime_pair J) x,
  ~ ideal_member (prime_pair_ideal P) x <-> prime_pair_filter P x.
Proof.
  intros A J P x. split.
  - intro Hnot. destruct (prime_pair_cover P x); [contradiction | assumption].
  - intros Hfilter Hideal.
    exact (@prime_pair_disjoint A J P x Hideal Hfilter).
Qed.
