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

Lemma ideal_join_list_app_left : forall A (J : join_order_data A) xs ys,
  jo_le J (ideal_join_list J xs) (ideal_join_list J (xs ++ ys)).
Proof.
  intros A J xs ys. apply ideal_join_list_least_upper.
  intros x Hx. apply ideal_join_list_member_bound.
  apply in_app_iff. now left.
Qed.

Lemma ideal_join_list_app_right : forall A (J : join_order_data A) xs ys,
  jo_le J (ideal_join_list J ys) (ideal_join_list J (xs ++ ys)).
Proof.
  intros A J xs ys. apply ideal_join_list_least_upper.
  intros x Hx. apply ideal_join_list_member_bound.
  apply in_app_iff. now right.
Qed.

Definition generated_ideal {A} (J : join_order_data A)
    (G : A -> Prop) : order_ideal J.
Proof.
  refine {| ideal_member := fun x => exists xs,
    Forall G xs /\ jo_le J x (ideal_join_list J xs) |}.
  - exists nil. split; [constructor |]. simpl. apply preorder_refl.
  - intros x y Hyx [xs [Hxs Hx]]. exists xs. split; [exact Hxs |].
    exact (@preorder_trans A (jo_order J) y x
      (ideal_join_list J xs) Hyx Hx).
  - intros x y [xs [Hxs Hx]] [ys [Hys Hy]].
    exists (xs ++ ys). split.
    + apply Forall_app. now split.
    + apply jo_join_le.
      * exact (@preorder_trans A (jo_order J) x
          (ideal_join_list J xs) (ideal_join_list J (xs ++ ys))
          Hx (ideal_join_list_app_left J xs ys)).
      * exact (@preorder_trans A (jo_order J) y
          (ideal_join_list J ys) (ideal_join_list J (xs ++ ys))
          Hy (ideal_join_list_app_right J xs ys)).
Defined.

Lemma generated_ideal_member_iff : forall A (J : join_order_data A)
    G x,
  ideal_member (generated_ideal J G) x <->
  exists xs, Forall G xs /\ jo_le J x (ideal_join_list J xs).
Proof. reflexivity. Qed.

Definition principal_list_generators {A} (J : join_order_data A)
    (generators : list A) : A -> Prop :=
  fun x => exists a, In a generators /\ jo_le J x a.

Theorem generated_principal_list_member_iff : forall A
    (J : join_order_data A) generators x,
  ideal_member
    (generated_ideal J (principal_list_generators J generators)) x <->
  jo_le J x (ideal_join_list J generators).
Proof.
  intros A J generators x. rewrite generated_ideal_member_iff. split.
  - intros [xs [Hxs Hx]]. eapply preorder_trans; [exact Hx |].
    apply ideal_join_list_least_upper. intros y Hy.
    apply Forall_forall with (x := y) in Hxs; [|exact Hy].
    destruct Hxs as [a [Ha Hya]]. eapply preorder_trans; [exact Hya |].
    now apply ideal_join_list_member_bound.
  - intro Hx. exists generators. split; [|exact Hx].
    apply Forall_forall. intros a Ha. exists a. split.
    + exact Ha.
    + apply preorder_refl.
Qed.

Definition ideal_family_sup {A} (J : join_order_data A)
    I (F : I -> order_ideal J) : order_ideal J :=
  generated_ideal J (fun x => exists i, ideal_member (F i) x).

Theorem ideal_family_sup_member_iff : forall A
    (J : join_order_data A) I (F : I -> order_ideal J) x,
  ideal_member (@ideal_family_sup A J I F) x <->
  exists xs,
    Forall (fun y => exists i, ideal_member (F i) y) xs /\
    jo_le J x (ideal_join_list J xs).
Proof. reflexivity. Qed.

Lemma ideal_family_sup_contains : forall A (J : join_order_data A)
    I (F : I -> order_ideal J) i,
  ideal_subset (F i) (@ideal_family_sup A J I F).
Proof.
  intros A J I F i x Hx. rewrite ideal_family_sup_member_iff.
  exists (x :: nil). split.
  - constructor; [now exists i | constructor].
  - simpl. apply jo_le_join_left.
Qed.

Theorem ideal_family_sup_least : forall A (J : join_order_data A)
    I (F : I -> order_ideal J) (K : order_ideal J),
  ideal_subset (@ideal_family_sup A J I F) K <->
  forall i, ideal_subset (F i) K.
Proof.
  intros A J I F K. split.
  - intros H i x Hx. apply H.
    exact (@ideal_family_sup_contains A J I F i x Hx).
  - intros Hall x Hx. rewrite ideal_family_sup_member_iff in Hx.
    destruct Hx as [xs [Hxs Hbound]].
    apply (@ideal_lower A J K (ideal_join_list J xs) x Hbound).
    apply ideal_join_list_member. intros y Hy.
    apply Forall_forall with (x := y) in Hxs; [|exact Hy].
    destruct Hxs as [i Hi]. now apply (Hall i).
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

Record boolean_order_data (A : Type) := {
  bo_join_order : join_order_data A;
  bo_meet : A -> A -> A;
  bo_top : A;
  bo_compl : A -> A;
  bo_himp : A -> A -> A;
  bo_meet_le_left : forall x y,
    jo_le bo_join_order (bo_meet x y) x;
  bo_meet_le_right : forall x y,
    jo_le bo_join_order (bo_meet x y) y;
  bo_meet_compl_bottom : forall x,
    bo_meet x (bo_compl x) = jo_bottom bo_join_order;
  bo_join_compl_top : forall x,
    jo_join bo_join_order x (bo_compl x) = bo_top;
  bo_compl_involutive : forall x, bo_compl (bo_compl x) = x;
  bo_compl_join : forall x y,
    bo_compl (jo_join bo_join_order x y) =
    bo_meet (bo_compl x) (bo_compl y);
  bo_himp_eq : forall x y,
    bo_himp x y = jo_join bo_join_order (bo_compl x) y
}.

Arguments bo_meet {A} _ _ _.
Arguments bo_top {A} _.
Arguments bo_compl {A} _ _.
Arguments bo_himp {A} _ _ _.

Definition boolean_prime_ideal {A} (B : boolean_order_data A)
    (I : order_ideal (bo_join_order B)) : Prop :=
  forall x y,
    ideal_member I (bo_meet B x y) ->
    ideal_member I x \/ ideal_member I y.

Arguments boolean_prime_ideal {A} B I.

Theorem boolean_prime_pair_ideal_or_compl : forall A
    (B : boolean_order_data A)
    (P : ideal_prime_pair (bo_join_order B)),
  boolean_prime_ideal B (prime_pair_ideal P) ->
  forall x,
    ideal_member (prime_pair_ideal P) x \/
    ideal_member (prime_pair_ideal P) (bo_compl B x).
Proof.
  intros A B P Hprime x. apply Hprime.
  rewrite bo_meet_compl_bottom. apply ideal_bottom_member.
Qed.

Arguments boolean_prime_pair_ideal_or_compl {A} B P _ x.

Theorem boolean_prime_pair_filter_or_compl : forall A
    (B : boolean_order_data A)
    (P : ideal_prime_pair (bo_join_order B)),
  ~ ideal_member (prime_pair_ideal P) (bo_top B) ->
  forall x,
    prime_pair_filter P x \/ prime_pair_filter P (bo_compl B x).
Proof.
  intros A B P Hproper x.
  destruct (prime_pair_cover P x) as [HxI | HxF]; [|now left].
  destruct (prime_pair_cover P (bo_compl B x)) as [HcI | HcF]; [|now right].
  exfalso. apply Hproper.
  pose proof (@ideal_join_member A (bo_join_order B) (prime_pair_ideal P)
    x (bo_compl B x) HxI HcI) as Htop.
  now rewrite bo_join_compl_top in Htop.
Qed.

Arguments boolean_prime_pair_filter_or_compl {A} B P _ x.

Theorem boolean_prime_pair_compl_ideal_iff_filter : forall A
    (B : boolean_order_data A)
    (P : ideal_prime_pair (bo_join_order B)),
  boolean_prime_ideal B (prime_pair_ideal P) ->
  ~ ideal_member (prime_pair_ideal P) (bo_top B) ->
  forall x,
    ideal_member (prime_pair_ideal P) (bo_compl B x) <->
    prime_pair_filter P x.
Proof.
  intros A B P Hprime Hproper x. split.
  - intro HcI. destruct (prime_pair_cover P x) as [HxI | HxF]; [|exact HxF].
    exfalso. apply Hproper.
    pose proof (@ideal_join_member A (bo_join_order B) (prime_pair_ideal P)
      x (bo_compl B x) HxI HcI) as Htop.
    now rewrite bo_join_compl_top in Htop.
  - intro HxF.
    destruct (boolean_prime_pair_ideal_or_compl B P Hprime x)
      as [HxI | HcI]; [|exact HcI].
    exfalso. exact (@prime_pair_disjoint A (bo_join_order B) P x HxI HxF).
Qed.

Arguments boolean_prime_pair_compl_ideal_iff_filter {A} B P _ _ x.

Theorem boolean_prime_pair_compl_filter_iff_ideal : forall A
    (B : boolean_order_data A)
    (P : ideal_prime_pair (bo_join_order B)),
  boolean_prime_ideal B (prime_pair_ideal P) ->
  ~ ideal_member (prime_pair_ideal P) (bo_top B) ->
  forall x,
    prime_pair_filter P (bo_compl B x) <->
    ideal_member (prime_pair_ideal P) x.
Proof.
  intros A B P Hprime Hproper x. split.
  - intro Hfilter.
    pose proof (proj2 (boolean_prime_pair_compl_ideal_iff_filter
      B P Hprime Hproper (bo_compl B x)) Hfilter) as Hideal.
    now rewrite bo_compl_involutive in Hideal.
  - intro Hideal.
    apply (proj1 (boolean_prime_pair_compl_ideal_iff_filter
      B P Hprime Hproper (bo_compl B x))).
    now rewrite bo_compl_involutive.
Qed.

Arguments boolean_prime_pair_compl_filter_iff_ideal {A} B P _ _ x.

Theorem boolean_prime_pair_meet_ideal_iff : forall A
    (B : boolean_order_data A)
    (P : ideal_prime_pair (bo_join_order B)),
  boolean_prime_ideal B (prime_pair_ideal P) ->
  forall x y,
    ideal_member (prime_pair_ideal P) (bo_meet B x y) <->
    ideal_member (prime_pair_ideal P) x \/
    ideal_member (prime_pair_ideal P) y.
Proof.
  intros A B P Hprime x y. split; [apply Hprime |].
  intros [Hx | Hy].
  - exact (@ideal_lower A (bo_join_order B) (prime_pair_ideal P)
      x (bo_meet B x y) (bo_meet_le_left B x y) Hx).
  - exact (@ideal_lower A (bo_join_order B) (prime_pair_ideal P)
      y (bo_meet B x y) (bo_meet_le_right B x y) Hy).
Qed.

Arguments boolean_prime_pair_meet_ideal_iff {A} B P _ x y.

Theorem boolean_prime_pair_join_filter_iff : forall A
    (B : boolean_order_data A)
    (P : ideal_prime_pair (bo_join_order B)),
  boolean_prime_ideal B (prime_pair_ideal P) ->
  ~ ideal_member (prime_pair_ideal P) (bo_top B) ->
  forall x y,
    prime_pair_filter P (jo_join (bo_join_order B) x y) <->
    prime_pair_filter P x \/ prime_pair_filter P y.
Proof.
  intros A B P Hprime Hproper x y. split.
  - intro Hjoin.
    apply (proj2 (boolean_prime_pair_compl_ideal_iff_filter
      B P Hprime Hproper _)) in Hjoin.
    rewrite bo_compl_join in Hjoin.
    apply (proj1 (boolean_prime_pair_meet_ideal_iff B P Hprime _ _)) in Hjoin.
    destruct Hjoin as [Hx | Hy].
    + left. now apply (proj1 (boolean_prime_pair_compl_ideal_iff_filter
        B P Hprime Hproper x)).
    + right. now apply (proj1 (boolean_prime_pair_compl_ideal_iff_filter
        B P Hprime Hproper y)).
  - intros [Hx | Hy].
    + apply (proj1 (boolean_prime_pair_compl_ideal_iff_filter
        B P Hprime Hproper _)). rewrite bo_compl_join.
      apply (proj2 (boolean_prime_pair_meet_ideal_iff B P Hprime _ _)). left.
      now apply (proj2 (boolean_prime_pair_compl_ideal_iff_filter
        B P Hprime Hproper x)).
    + apply (proj1 (boolean_prime_pair_compl_ideal_iff_filter
        B P Hprime Hproper _)). rewrite bo_compl_join.
      apply (proj2 (boolean_prime_pair_meet_ideal_iff B P Hprime _ _)). right.
      now apply (proj2 (boolean_prime_pair_compl_ideal_iff_filter
        B P Hprime Hproper y)).
Qed.

Arguments boolean_prime_pair_join_filter_iff {A} B P _ _ x y.

Theorem boolean_prime_pair_himp_filter_iff : forall A
    (B : boolean_order_data A)
    (P : ideal_prime_pair (bo_join_order B)),
  boolean_prime_ideal B (prime_pair_ideal P) ->
  ~ ideal_member (prime_pair_ideal P) (bo_top B) ->
  forall x y,
    prime_pair_filter P (bo_himp B x y) <->
    (prime_pair_filter P x -> prime_pair_filter P y).
Proof.
  intros A B P Hprime Hproper x y. rewrite bo_himp_eq. split.
  - intro Hjoin. apply (proj1 (boolean_prime_pair_join_filter_iff
      B P Hprime Hproper _ _)) in Hjoin.
    intros Hx. destruct Hjoin as [Hcx | Hy]; [|exact Hy].
    pose proof (proj1 (boolean_prime_pair_compl_filter_iff_ideal
      B P Hprime Hproper x) Hcx) as HxI.
    exfalso. exact (@prime_pair_disjoint A (bo_join_order B) P x HxI Hx).
  - intro Himp. apply (proj2 (boolean_prime_pair_join_filter_iff
      B P Hprime Hproper _ _)).
    destruct (prime_pair_cover P x) as [HxI | HxF].
    + left. now apply (proj2 (boolean_prime_pair_compl_filter_iff_ideal
        B P Hprime Hproper x)).
    + right. now apply Himp.
Qed.
