(** Finite-vector elimination and lifting through explicit quotients.

    Rocq has no primitive quotient type.  We therefore expose exactly the
    representation data needed by the source theorems: every quotient value
    has a representative, representatives round-trip to the same quotient
    value, and choosing a representative of a constructed class is related
    to the original value. *)

From Stdlib Require Import Logic.FunctionalExtensionality Vectors.Fin.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record explicit_quotient (A : Type) (R : A -> A -> Prop) := {
  quotient_carrier : Type;
  quotient_mk : A -> quotient_carrier;
  quotient_repr : quotient_carrier -> A;
  quotient_repr_mk_related : forall a,
    R (quotient_repr (quotient_mk a)) a;
  quotient_mk_repr : forall q,
    quotient_mk (quotient_repr q) = q
}.

Arguments quotient_carrier {A R} _.
Arguments quotient_mk {A R} _ _.
Arguments quotient_repr {A R} _ _.
Arguments quotient_repr_mk_related {A R} _ _.
Arguments quotient_mk_repr {A R} _ _.

Definition quotient_vec_mk {A R} (Q : @explicit_quotient A R) {n}
    (v : Fin.t n -> A) : Fin.t n -> quotient_carrier Q :=
  fun i => quotient_mk Q (v i).

Theorem quotient_vec_induction : forall A (R : A -> A -> Prop)
    (Q : @explicit_quotient A R) n
    (P : (Fin.t n -> quotient_carrier Q) -> Prop)
    (v : Fin.t n -> quotient_carrier Q),
  (forall representatives : Fin.t n -> A,
    P (quotient_vec_mk Q representatives)) ->
  P v.
Proof.
  intros A R Q n P v H.
  pose (representatives := fun i => quotient_repr Q (v i)).
  assert (Heq : quotient_vec_mk Q representatives = v).
  { apply functional_extensionality. intro i. apply quotient_mk_repr. }
  now rewrite <- Heq.
Qed.

Definition quotient_vec_lift {A R} (Q : @explicit_quotient A R)
    {n B} (f : (Fin.t n -> A) -> B)
    (_ : forall v w : Fin.t n -> A,
      (forall i, R (v i) (w i)) -> f v = f w)
    (v : Fin.t n -> quotient_carrier Q) : B :=
  f (fun i => quotient_repr Q (v i)).

Lemma quotient_vec_lift_zero : forall A (R : A -> A -> Prop)
    (Q : @explicit_quotient A R) B
    (f : (Fin.t 0 -> A) -> B)
    (respectful : forall v w : Fin.t 0 -> A,
      (forall i, R (v i) (w i)) -> f v = f w)
    (v : Fin.t 0 -> quotient_carrier Q),
  @quotient_vec_lift A R Q 0 B f respectful v =
  f (fun i => match i with end).
Proof.
  intros A R Q B f respectful v. unfold quotient_vec_lift.
  f_equal. apply functional_extensionality. intro i. inversion i.
Qed.

Theorem quotient_vec_lift_mk : forall A (R : A -> A -> Prop)
    (Q : @explicit_quotient A R) n B
    (f : (Fin.t n -> A) -> B)
    (respectful : forall v w : Fin.t n -> A,
      (forall i, R (v i) (w i)) -> f v = f w)
    (v : Fin.t n -> A),
  @quotient_vec_lift A R Q n B f respectful
    (quotient_vec_mk Q v) = f v.
Proof.
  intros A R Q n B f respectful v. unfold quotient_vec_lift.
  apply respectful. intro i. apply quotient_repr_mk_related.
Qed.

Corollary quotient_vec_lift_mk_one : forall A (R : A -> A -> Prop)
    (Q : @explicit_quotient A R) B
    (f : (Fin.t 1 -> A) -> B)
    (respectful : forall v w : Fin.t 1 -> A,
      (forall i, R (v i) (w i)) -> f v = f w)
    (v : Fin.t 1 -> A),
  @quotient_vec_lift A R Q 1 B f respectful
    (quotient_vec_mk Q v) = f v.
Proof. intros. exact (@quotient_vec_lift_mk A R Q 1 B f respectful v). Qed.

Corollary quotient_vec_lift_mk_two : forall A (R : A -> A -> Prop)
    (Q : @explicit_quotient A R) B
    (f : (Fin.t 2 -> A) -> B)
    (respectful : forall v w : Fin.t 2 -> A,
      (forall i, R (v i) (w i)) -> f v = f w)
    (v : Fin.t 2 -> A),
  @quotient_vec_lift A R Q 2 B f respectful
    (quotient_vec_mk Q v) = f v.
Proof. intros. exact (@quotient_vec_lift_mk A R Q 2 B f respectful v). Qed.
