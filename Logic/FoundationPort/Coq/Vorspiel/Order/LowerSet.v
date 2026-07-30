(** Lower sets, incompatibility pseudocomplements, and Heyting implication. *)

From Foundation.Vorspiel.Order Require Import Dense.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record lower_set {A} (O : preorder_data A) := {
  lower_member : A -> Prop;
  lower_closed : forall x y,
    preorder_le O y x -> lower_member x -> lower_member y
}.

Arguments lower_member {A O} _ _.

Definition lower_subset {A} {O : preorder_data A}
    (U V : lower_set O) : Prop :=
  forall x, lower_member U x -> lower_member V x.

Definition lower_disjoint {A} {O : preorder_data A}
    (U V : lower_set O) : Prop :=
  forall x, ~ (lower_member U x /\ lower_member V x).

Definition lower_intersection {A} {O : preorder_data A}
    (U V : lower_set O) : lower_set O.
Proof.
  refine {| lower_member := fun x =>
    lower_member U x /\ lower_member V x |}.
  intros x y Hyx [HU HV]. split.
  - exact (@lower_closed A O U x y Hyx HU).
  - exact (@lower_closed A O V x y Hyx HV).
Defined.

Lemma lower_intersection_member_iff : forall A (O : preorder_data A)
    (U V : lower_set O) x,
  lower_member (lower_intersection U V) x <->
  lower_member U x /\ lower_member V x.
Proof. reflexivity. Qed.

Theorem lower_disjoint_iff_incompatible : forall A
    (O : preorder_data A) (U V : lower_set O),
  lower_disjoint U V <->
  forall x, lower_member U x ->
    forall y, lower_member V y -> order_incompatible O x y.
Proof.
  intros A O U V. split.
  - intros Hdisjoint x Hx y Hy [z [Hzx Hzy]].
    apply (Hdisjoint z). split.
    + exact (@lower_closed A O U x z Hzx Hx).
    + exact (@lower_closed A O V y z Hzy Hy).
  - intros Hcross x [Hx Hy].
    apply (Hcross x Hx x Hy). apply order_compatible_refl.
Qed.

Definition lower_dual {A} {O : preorder_data A}
    (U : lower_set O) : lower_set O.
Proof.
  refine {| lower_member := fun x =>
    forall y, lower_member U y -> order_incompatible O x y |}.
  intros x x' Hx'x Hx y Hy.
  exact (order_incompatible_lower
    (Hx y Hy) Hx'x (preorder_refl O y)).
Defined.

Lemma lower_dual_member_iff : forall A (O : preorder_data A)
    (U : lower_set O) x,
  lower_member (lower_dual U) x <->
  forall y, lower_member U y -> order_incompatible O x y.
Proof. reflexivity. Qed.

Theorem lower_dual_greatest_disjoint : forall A
    (O : preorder_data A) (S U : lower_set O),
  lower_disjoint S U <-> lower_subset S (lower_dual U).
Proof.
  intros A O S U. rewrite lower_disjoint_iff_incompatible.
  unfold lower_subset. reflexivity.
Qed.

Definition lower_himp {A} {O : preorder_data A}
    (U V : lower_set O) : lower_set O.
Proof.
  refine {| lower_member := fun x =>
    forall y, preorder_le O y x ->
      lower_member U y -> lower_member V y |}.
  intros x x' Hx'x Hx y Hyx' HyU. apply Hx; [| exact HyU].
  exact (@preorder_trans A O y x' x Hyx' Hx'x).
Defined.

Lemma lower_himp_member_iff : forall A (O : preorder_data A)
    (U V : lower_set O) x,
  lower_member (lower_himp U V) x <->
  forall y, preorder_le O y x ->
    lower_member U y -> lower_member V y.
Proof. reflexivity. Qed.

Theorem lower_himp_greatest : forall A (O : preorder_data A)
    (S U V : lower_set O),
  lower_subset (lower_intersection S U) V <->
  lower_subset S (lower_himp U V).
Proof.
  intros A O S U V. split.
  - intros H x Hx y Hyx Hy.
    apply H. split; [exact (@lower_closed A O S x y Hyx Hx) | exact Hy].
  - intros H x [HS HU].
    exact (H x HS x (preorder_refl O x) HU).
Qed.

Definition lower_regular {A} {O : preorder_data A}
    (U : lower_set O) : Prop :=
  forall x, lower_member (lower_dual (lower_dual U)) x <->
    lower_member U x.
