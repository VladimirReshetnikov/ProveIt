(** Generic Heyting-algebra inequalities and infinitary complementation. *)

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record heyting_algebra_data (A : Type) := {
  ha_le : A -> A -> Prop;
  ha_le_refl : forall x, ha_le x x;
  ha_le_trans : forall x y z, ha_le x y -> ha_le y z -> ha_le x z;
  ha_inf : A -> A -> A;
  ha_sup : A -> A -> A;
  ha_himp : A -> A -> A;
  ha_inf_le_left : forall x y, ha_le (ha_inf x y) x;
  ha_inf_le_right : forall x y, ha_le (ha_inf x y) y;
  ha_le_inf : forall x y z, ha_le x y -> ha_le x z -> ha_le x (ha_inf y z);
  ha_le_sup_left : forall x y, ha_le x (ha_sup x y);
  ha_le_sup_right : forall x y, ha_le y (ha_sup x y);
  ha_sup_le : forall x y z, ha_le x z -> ha_le y z -> ha_le (ha_sup x y) z;
  ha_residuation : forall x y z,
    ha_le (ha_inf x y) z <-> ha_le x (ha_himp y z)
}.

Arguments ha_le {A} _ _ _.
Arguments ha_inf {A} _ _ _.
Arguments ha_sup {A} _ _ _.
Arguments ha_himp {A} _ _ _.

Definition ha_order_equiv {A} (H : heyting_algebra_data A)
    (x y : A) : Prop :=
  ha_le H x y /\ ha_le H y x.

Lemma ha_inf_mono : forall A (H : heyting_algebra_data A)
    a a' b b',
  ha_le H a a' -> ha_le H b b' ->
  ha_le H (ha_inf H a b) (ha_inf H a' b').
Proof.
  intros A H a a' b b' Ha Hb. apply ha_le_inf.
  - exact (@ha_le_trans A H _ _ _ (ha_inf_le_left H a b) Ha).
  - exact (@ha_le_trans A H _ _ _ (ha_inf_le_right H a b) Hb).
Qed.

Lemma ha_inf_swap_le : forall A (H : heyting_algebra_data A) a b,
  ha_le H (ha_inf H a b) (ha_inf H b a).
Proof.
  intros A H a b. apply ha_le_inf.
  - apply ha_inf_le_right.
  - apply ha_inf_le_left.
Qed.

Lemma ha_himp_elim : forall A (H : heyting_algebra_data A) a b,
  ha_le H (ha_inf H (ha_himp H a b) a) b.
Proof.
  intros A H a b. apply (proj2 (ha_residuation H _ _ _)).
  apply ha_le_refl.
Qed.

Theorem ha_himp_himp_inf_himp_inf_le :
  forall A (H : heyting_algebra_data A) a b c,
  ha_le H
    (ha_inf H
      (ha_inf H (ha_himp H a (ha_himp H b c)) (ha_himp H a b))
      a)
    c.
Proof.
  intros A H a b c.
  eapply ha_le_trans.
  2: apply (ha_himp_elim H b c).
  apply ha_le_inf.
  - eapply ha_le_trans.
    2: apply (ha_himp_elim H a (ha_himp H b c)).
    apply ha_inf_mono; [apply ha_inf_le_left | apply ha_le_refl].
  - eapply ha_le_trans.
    2: apply (ha_himp_elim H a b).
    apply ha_inf_mono; [apply ha_inf_le_right | apply ha_le_refl].
Qed.

Theorem ha_himp_inf_himp_inf_sup_le :
  forall A (H : heyting_algebra_data A) a b c,
  ha_le H
    (ha_inf H
      (ha_inf H (ha_himp H a c) (ha_himp H b c))
      (ha_sup H a b))
    c.
Proof.
  intros A H a b c.
  eapply ha_le_trans; [apply ha_inf_swap_le |].
  apply (proj2 (ha_residuation H _ _ _)).
  apply ha_sup_le.
  - apply (proj1 (ha_residuation H _ _ _)).
    eapply ha_le_trans; [apply ha_inf_swap_le |].
    eapply ha_le_trans.
    + apply ha_inf_mono; [apply ha_inf_le_left | apply ha_le_refl].
    + apply ha_himp_elim.
  - apply (proj1 (ha_residuation H _ _ _)).
    eapply ha_le_trans; [apply ha_inf_swap_le |].
    eapply ha_le_trans.
    + apply ha_inf_mono; [apply ha_inf_le_right | apply ha_le_refl].
    + apply ha_himp_elim.
Qed.

Theorem ha_complement_of_sup_equiv_inf_complements :
  forall A (H : heyting_algebra_data A) (bottom : A)
    I (a : I -> A) sup inf,
  (forall i, ha_le H (a i) sup) ->
  (forall x, (forall i, ha_le H (a i) x) -> ha_le H sup x) ->
  (forall i, ha_le H inf (ha_himp H (a i) bottom)) ->
  (forall x,
    (forall i, ha_le H x (ha_himp H (a i) bottom)) ->
    ha_le H x inf) ->
  ha_order_equiv H (ha_himp H sup bottom) inf.
Proof.
  intros A H bottom I a sup inf Hupper Hsup Hlower Hinf. split.
  - apply Hinf. intro i.
    apply (proj1 (ha_residuation H _ _ _)).
    eapply ha_le_trans.
    + apply ha_inf_mono; [apply ha_le_refl | apply Hupper].
    + apply ha_himp_elim.
  - apply (proj1 (ha_residuation H _ _ _)).
    eapply ha_le_trans; [apply ha_inf_swap_le |].
    apply (proj2 (ha_residuation H _ _ _)).
    apply Hsup. intro i.
    apply (proj1 (ha_residuation H _ _ _)).
    eapply ha_le_trans; [apply ha_inf_swap_le |].
    eapply ha_le_trans.
    + apply ha_inf_mono; [apply Hlower | apply ha_le_refl].
    + apply ha_himp_elim.
Qed.
