(** Lower sets, incompatibility pseudocomplements, and Heyting implication. *)

From Foundation.Vorspiel.Order Require Import Dense Heyting.

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

Definition lower_empty {A} {O : preorder_data A} : lower_set O.
Proof.
  refine {| lower_member := fun _ => False |}.
  intros x y _ H. contradiction.
Defined.

Definition lower_full {A} {O : preorder_data A} : lower_set O.
Proof.
  refine {| lower_member := fun _ => True |}.
  intros x y _ _. exact I.
Defined.

Definition lower_union {A} {O : preorder_data A}
    (U V : lower_set O) : lower_set O.
Proof.
  refine {| lower_member := fun x =>
    lower_member U x \/ lower_member V x |}.
  intros x y Hyx [HU | HV].
  - left. exact (@lower_closed A O U x y Hyx HU).
  - right. exact (@lower_closed A O V x y Hyx HV).
Defined.

Definition lower_family_union {A} {O : preorder_data A} I
    (F : I -> lower_set O) : lower_set O.
Proof.
  refine {| lower_member := fun x => exists i, lower_member (F i) x |}.
  intros x y Hyx [i Hi]. exists i.
  exact (@lower_closed A O (F i) x y Hyx Hi).
Defined.

Definition lower_family_intersection {A} {O : preorder_data A} I
    (F : I -> lower_set O) : lower_set O.
Proof.
  refine {| lower_member := fun x => forall i, lower_member (F i) x |}.
  intros x y Hyx Hx i.
  exact (@lower_closed A O (F i) x y Hyx (Hx i)).
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

Definition lower_set_heyting_algebra {A} (O : preorder_data A) :
    heyting_algebra_data (lower_set O).
Proof.
  refine {|
    ha_le := lower_subset;
    ha_inf := lower_intersection;
    ha_sup := lower_union;
    ha_himp := lower_himp
  |}.
  - intros U x Hx. exact Hx.
  - intros U V W HUV HVW x Hx. now apply HVW, HUV.
  - intros U V x [Hx _]. exact Hx.
  - intros U V x [_ Hx]. exact Hx.
  - intros U V W HWU HWV x Hx. split; [now apply HWU | now apply HWV].
  - intros U V x Hx. now left.
  - intros U V x Hx. now right.
  - intros U V W HUW HVW x [Hx | Hx]; [now apply HUW | now apply HVW].
  - intros S U V. exact (lower_himp_greatest S U V).
Defined.

Definition lower_regular {A} {O : preorder_data A}
    (U : lower_set O) : Prop :=
  forall x, lower_member (lower_dual (lower_dual U)) x <->
    lower_member U x.

Definition lower_equiv {A} {O : preorder_data A}
    (U V : lower_set O) : Prop :=
  lower_subset U V /\ lower_subset V U.

Lemma lower_dual_antitone : forall A (O : preorder_data A)
    (U V : lower_set O),
  lower_subset U V -> lower_subset (lower_dual V) (lower_dual U).
Proof.
  intros A O U V HUV x Hx y Hy. apply Hx. now apply HUV.
Qed.

Lemma lower_double_dual_extensive : forall A (O : preorder_data A)
    (U : lower_set O),
  lower_subset U (lower_dual (lower_dual U)).
Proof.
  intros A O U x Hx y Hy.
  apply (proj2 (order_incompatible_sym_iff O x y)). now apply Hy.
Qed.

Lemma lower_double_dual_monotone : forall A (O : preorder_data A)
    (U V : lower_set O),
  lower_subset U V ->
  lower_subset (lower_dual (lower_dual U))
    (lower_dual (lower_dual V)).
Proof.
  intros A O U V HUV. apply lower_dual_antitone.
  now apply lower_dual_antitone.
Qed.

Theorem lower_triple_dual_equiv : forall A (O : preorder_data A)
    (U : lower_set O),
  lower_equiv (lower_dual (lower_dual (lower_dual U)))
    (lower_dual U).
Proof.
  intros A O U. split.
  - apply lower_dual_antitone. apply lower_double_dual_extensive.
  - apply lower_double_dual_extensive.
Qed.

Definition lower_regularize {A} {O : preorder_data A}
    (U : lower_set O) : lower_set O :=
  lower_dual (lower_dual U).

Theorem lower_regularize_regular : forall A (O : preorder_data A)
    (U : lower_set O),
  lower_regular (lower_regularize U).
Proof.
  intros A O U x. split.
  - apply lower_dual_antitone.
    apply lower_double_dual_extensive.
  - apply lower_double_dual_extensive.
Qed.

Theorem lower_dual_regular : forall A (O : preorder_data A)
    (U : lower_set O),
  lower_regular (lower_dual U).
Proof.
  intros A O U x.
  destruct (@lower_triple_dual_equiv A O U) as [Hforward Hbackward].
  split; [apply Hforward | apply Hbackward].
Qed.

Theorem lower_intersection_regular : forall A (O : preorder_data A)
    (U V : lower_set O),
  lower_regular U -> lower_regular V ->
  lower_regular (lower_intersection U V).
Proof.
  intros A O U V HU HV x. split.
  - intro Hx. split.
    + apply (proj1 (HU x)).
      eapply lower_double_dual_monotone; [|exact Hx].
      intros y [Hy _]. exact Hy.
    + apply (proj1 (HV x)).
      eapply lower_double_dual_monotone; [|exact Hx].
      intros y [_ Hy]. exact Hy.
  - apply lower_double_dual_extensive.
Qed.

Theorem lower_family_intersection_regular : forall A
    (O : preorder_data A) I (F : I -> lower_set O),
  (forall i, lower_regular (F i)) ->
  lower_regular (lower_family_intersection F).
Proof.
  intros A O I F HF x. split.
  - intros Hx i. apply (proj1 (HF i x)).
    eapply lower_double_dual_monotone; [|exact Hx].
    intros y Hy. exact (Hy i).
  - apply lower_double_dual_extensive.
Qed.

Lemma lower_empty_regular : forall A (O : preorder_data A),
  lower_regular (@lower_empty A O).
Proof.
  intros A O x. split.
  - intro Hx. exfalso. apply (@order_incompatible_irrefl A O x).
    apply Hx. intros y Hy. contradiction.
  - intro H. contradiction.
Qed.

Lemma lower_full_regular : forall A (O : preorder_data A),
  lower_regular (@lower_full A O).
Proof.
  intros A O x. split; [intros; exact I |].
  intro H. apply lower_double_dual_extensive. exact I.
Qed.

Record regular_lower_set {A} (O : preorder_data A) := {
  regular_carrier : lower_set O;
  regular_carrier_regular : lower_regular regular_carrier
}.

Arguments regular_carrier {A O} _.

Definition regular_subset {A} {O : preorder_data A}
    (U V : regular_lower_set O) : Prop :=
  lower_subset (regular_carrier U) (regular_carrier V).

Definition regular_equiv {A} {O : preorder_data A}
    (U V : regular_lower_set O) : Prop :=
  regular_subset U V /\ regular_subset V U.

Definition regular_bottom {A} {O : preorder_data A} :
    regular_lower_set O :=
  {| regular_carrier := lower_empty;
     regular_carrier_regular := lower_empty_regular O |}.

Definition regular_top {A} {O : preorder_data A} :
    regular_lower_set O :=
  {| regular_carrier := lower_full;
     regular_carrier_regular := lower_full_regular O |}.

Definition regular_meet {A} {O : preorder_data A}
    (U V : regular_lower_set O) : regular_lower_set O :=
  {| regular_carrier := lower_intersection
       (regular_carrier U) (regular_carrier V);
     regular_carrier_regular := lower_intersection_regular
       (regular_carrier_regular U) (regular_carrier_regular V) |}.

Definition regular_join {A} {O : preorder_data A}
    (U V : regular_lower_set O) : regular_lower_set O :=
  {| regular_carrier := lower_regularize
       (lower_union (regular_carrier U) (regular_carrier V));
     regular_carrier_regular := @lower_regularize_regular A O
       (lower_union (regular_carrier U) (regular_carrier V)) |}.

Definition regular_compl {A} {O : preorder_data A}
    (U : regular_lower_set O) : regular_lower_set O :=
  {| regular_carrier := lower_dual (regular_carrier U);
     regular_carrier_regular := @lower_dual_regular A O
       (regular_carrier U) |}.

Definition regular_family_sup {A} {O : preorder_data A} I
    (F : I -> regular_lower_set O) : regular_lower_set O :=
  {| regular_carrier := lower_regularize
       (lower_family_union (fun i => regular_carrier (F i)));
     regular_carrier_regular := @lower_regularize_regular A O
       (lower_family_union (fun i => regular_carrier (F i))) |}.

Definition regular_family_inf {A} {O : preorder_data A} I
    (F : I -> regular_lower_set O) : regular_lower_set O :=
  {| regular_carrier := lower_family_intersection
       (fun i => regular_carrier (F i));
     regular_carrier_regular := @lower_family_intersection_regular
       A O I (fun i => regular_carrier (F i))
       (fun i => regular_carrier_regular (F i)) |}.

Lemma regular_subset_refl : forall A (O : preorder_data A)
    (U : regular_lower_set O),
  regular_subset U U.
Proof. intros A O U x Hx. exact Hx. Qed.

Lemma regular_subset_trans : forall A (O : preorder_data A)
    (U V W : regular_lower_set O),
  regular_subset U V -> regular_subset V W -> regular_subset U W.
Proof. intros A O U V W HUV HVW x Hx. now apply HVW, HUV. Qed.

Lemma regular_bottom_least : forall A (O : preorder_data A)
    (U : regular_lower_set O),
  regular_subset regular_bottom U.
Proof. intros A O U x H. contradiction. Qed.

Lemma regular_top_greatest : forall A (O : preorder_data A)
    (U : regular_lower_set O),
  regular_subset U regular_top.
Proof. intros A O U x H. exact I. Qed.

Lemma regular_meet_left : forall A (O : preorder_data A)
    (U V : regular_lower_set O),
  regular_subset (regular_meet U V) U.
Proof. intros A O U V x [Hx _]. exact Hx. Qed.

Lemma regular_meet_right : forall A (O : preorder_data A)
    (U V : regular_lower_set O),
  regular_subset (regular_meet U V) V.
Proof. intros A O U V x [_ Hx]. exact Hx. Qed.

Lemma regular_meet_greatest : forall A (O : preorder_data A)
    (S U V : regular_lower_set O),
  regular_subset S U -> regular_subset S V ->
  regular_subset S (regular_meet U V).
Proof.
  intros A O S U V HSU HSV x Hx. split; [now apply HSU | now apply HSV].
Qed.

Lemma regular_join_left : forall A (O : preorder_data A)
    (U V : regular_lower_set O),
  regular_subset U (regular_join U V).
Proof.
  intros A O U V x Hx. apply lower_double_dual_extensive. now left.
Qed.

Lemma regular_join_right : forall A (O : preorder_data A)
    (U V : regular_lower_set O),
  regular_subset V (regular_join U V).
Proof.
  intros A O U V x Hx. apply lower_double_dual_extensive. now right.
Qed.

Lemma regular_join_least : forall A (O : preorder_data A)
    (U V S : regular_lower_set O),
  regular_subset U S -> regular_subset V S ->
  regular_subset (regular_join U V) S.
Proof.
  intros A O U V S HUS HVS x Hx.
  apply (proj1 (regular_carrier_regular S x)).
  eapply lower_double_dual_monotone; [|exact Hx].
  intros y [Hy | Hy]; [now apply HUS | now apply HVS].
Qed.

Lemma regular_family_sup_contains : forall A (O : preorder_data A)
    I (F : I -> regular_lower_set O) i,
  regular_subset (F i) (regular_family_sup F).
Proof.
  intros A O I F i x Hx. apply lower_double_dual_extensive.
  now exists i.
Qed.

Theorem regular_family_sup_least : forall A (O : preorder_data A)
    I (F : I -> regular_lower_set O) (S : regular_lower_set O),
  regular_subset (regular_family_sup F) S <->
  forall i, regular_subset (F i) S.
Proof.
  intros A O I F S. split.
  - intros H i x Hx. apply H. exact (@regular_family_sup_contains A O I F i x Hx).
  - intros Hall x Hx. apply (proj1 (regular_carrier_regular S x)).
    eapply lower_double_dual_monotone; [|exact Hx].
    intros y [i Hi]. now apply (Hall i).
Qed.

Lemma regular_family_inf_below : forall A (O : preorder_data A)
    I (F : I -> regular_lower_set O) i,
  regular_subset (regular_family_inf F) (F i).
Proof. intros A O I F i x Hx. exact (Hx i). Qed.

Theorem regular_family_inf_greatest : forall A (O : preorder_data A)
    I (F : I -> regular_lower_set O) (S : regular_lower_set O),
  regular_subset S (regular_family_inf F) <->
  forall i, regular_subset S (F i).
Proof.
  intros A O I F S. split.
  - intros H i x Hx. exact (H x Hx i).
  - intros Hall x Hx i. now apply (Hall i).
Qed.

Theorem regular_meet_compl_bottom : forall A (O : preorder_data A)
    (U : regular_lower_set O),
  regular_equiv (regular_meet U (regular_compl U)) regular_bottom.
Proof.
  intros A O U. split.
  - intros x [Hx Hdual]. exfalso.
    apply (@order_incompatible_irrefl A O x). now apply Hdual.
  - apply regular_bottom_least.
Qed.

Theorem regular_join_compl_top : forall A (O : preorder_data A)
    (U : regular_lower_set O),
  regular_equiv (regular_join U (regular_compl U)) regular_top.
Proof.
  intros A O U. split; [apply regular_top_greatest |].
  intros x _ y Hy. exfalso.
  apply (@order_incompatible_irrefl A O y).
  apply Hy. right. intros z Hz. apply Hy. now left.
Qed.

Theorem regular_compl_involutive : forall A (O : preorder_data A)
    (U : regular_lower_set O),
  regular_equiv (regular_compl (regular_compl U)) U.
Proof.
  intros A O U. split.
  - intros x Hx. now apply (proj1 (regular_carrier_regular U x)).
  - intros x Hx. now apply (proj2 (regular_carrier_regular U x)).
Qed.
