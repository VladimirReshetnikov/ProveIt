(** Unique choice and total extension outside a predicate domain. *)

From Stdlib Require Import Logic.ClassicalEpsilon Logic.Classical_Prop.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition choose_unique {A : Type} (P : A -> Prop)
    (h : exists! x, P x) : A :=
  proj1_sig (constructive_definite_description P h).

Arguments choose_unique {A} P h.

Lemma choose_unique_spec : forall A (P : A -> Prop) (h : exists! x, P x),
  P (choose_unique P h).
Proof.
  intros A P h. unfold choose_unique.
  destruct (constructive_definite_description P h) as [x Hx]. exact Hx.
Qed.

Lemma choose_unique_uniq : forall A (P : A -> Prop)
    (h : exists! x, P x) x,
  P x -> x = choose_unique P h.
Proof.
  intros A P [w [Hw Huniq]] x Hx.
  transitivity w.
  - symmetry. now apply Huniq.
  - apply Huniq. apply choose_unique_spec.
Qed.

Lemma choose_unique_eq_iff_right : forall A (P : A -> Prop)
    (h : exists! x, P x) x,
  x = choose_unique P h <-> P x.
Proof.
  intros A P h x. split.
  - intros ->. apply choose_unique_spec.
  - apply (choose_unique_uniq h).
Qed.

Lemma choose_unique_eq_iff_left : forall A (P : A -> Prop)
    (h : exists! x, P x) x,
  choose_unique P h = x <-> P x.
Proof.
  intros A P h x. rewrite <- (choose_unique_eq_iff_right h x).
  split; now intros ->.
Qed.

Lemma exists_unique_extend : forall A (P : A -> Prop) (R : A -> A -> Prop),
  (forall x, P x -> exists! y, R x y) ->
  forall default x, exists! y,
    (P x -> R x y) /\ (~ P x -> y = default).
Proof.
  intros A P R H default x.
  destruct (classic (P x)) as [Hpx | Hpx].
  - destruct (H x Hpx) as [y [Hy Huniq]].
    exists y. split.
    + split; [intros _; exact Hy | intros Hn; contradiction].
    + intros z [Hz _]. apply Huniq. now apply Hz.
  - exists default. split.
    + split; [intros Hp; contradiction | intros _; reflexivity].
    + intros z [_ Hz]. symmetry. now apply Hz.
Qed.

Arguments exists_unique_extend {A P R} h default x.

Definition extended_choose_unique {A : Type} (P : A -> Prop)
    (R : A -> A -> Prop)
    (h : forall x, P x -> exists! y, R x y)
    (default x : A) : A :=
  choose_unique
    (fun y => (P x -> R x y) /\ (~ P x -> y = default))
    (exists_unique_extend h default x).

Arguments extended_choose_unique {A} P R h default x.

Lemma extended_choose_unique_spec : forall A (P : A -> Prop)
    (R : A -> A -> Prop)
    (h : forall x, P x -> exists! y, R x y) default x,
  P x -> R x (extended_choose_unique P R h default x).
Proof.
  intros A P R h default x Hpx.
  exact (proj1 (choose_unique_spec (exists_unique_extend h default x)) Hpx).
Qed.

Lemma extended_choose_unique_spec_not : forall A (P : A -> Prop)
    (R : A -> A -> Prop)
    (h : forall x, P x -> exists! y, R x y) default x,
  ~ P x -> extended_choose_unique P R h default x = default.
Proof.
  intros A P R h default x Hpx.
  exact (proj2 (choose_unique_spec (exists_unique_extend h default x)) Hpx).
Qed.

Lemma extended_choose_unique_uniq : forall A (P : A -> Prop)
    (R : A -> A -> Prop)
    (h : forall x, P x -> exists! y, R x y) default x y,
  P x -> R x y -> y = extended_choose_unique P R h default x.
Proof.
  intros A P R h default x y Hpx Hry.
  apply (choose_unique_uniq (exists_unique_extend h default x)).
  split.
  - intros _. exact Hry.
  - intros Hn. contradiction.
Qed.

Lemma extended_choose_unique_eq_iff : forall A (P : A -> Prop)
    (R : A -> A -> Prop)
    (h : forall x, P x -> exists! y, R x y) default x y,
  P x ->
  y = extended_choose_unique P R h default x <-> R x y.
Proof.
  intros A P R h default x y Hpx. split.
  - intros ->. now apply extended_choose_unique_spec.
  - now apply (extended_choose_unique_uniq h default Hpx).
Qed.
