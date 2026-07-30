(** Quantifier decomposition for bounded finite vectors. *)

From Foundation.Vorspiel Require Import Matrix.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition fin_vec_pointwise {A n} (R : A -> A -> Prop)
    (v w : Fin.t n -> A) : Prop :=
  forall i, R (v i) (w i).

Theorem fin_vec_forall_bounded_iff : forall A n (R : A -> A -> Prop)
    (P : (Fin.t (S n) -> A) -> Prop) (bound : Fin.t (S n) -> A),
  (forall v, fin_vec_pointwise R v bound -> P v) <->
  forall head, R head (matrix_vec_head bound) ->
  forall tail : Fin.t n -> A,
    fin_vec_pointwise R tail (matrix_vec_tail bound) ->
    P (matrix_vec_cons head tail).
Proof.
  intros A n R P bound. split.
  - intros H head Hhead tail Htail. apply H.
    intro i. refine (@Fin.caseS' n i (fun j =>
      R (matrix_vec_cons head tail j) (bound j)) _ _).
    + exact Hhead.
    + exact Htail.
  - intros H v Hv. rewrite <- (matrix_vec_eta v).
    apply H.
    + exact (Hv Fin.F1).
    + intro i. exact (Hv (Fin.FS i)).
Qed.

Theorem fin_vec_exists_bounded_iff : forall A n (R : A -> A -> Prop)
    (P : (Fin.t (S n) -> A) -> Prop) (bound : Fin.t (S n) -> A),
  (exists v, fin_vec_pointwise R v bound /\ P v) <->
  exists head, R head (matrix_vec_head bound) /\
  exists tail : Fin.t n -> A,
    fin_vec_pointwise R tail (matrix_vec_tail bound) /\
    P (matrix_vec_cons head tail).
Proof.
  intros A n R P bound. split.
  - intros [v [Hv HP]].
    exists (matrix_vec_head v). split; [exact (Hv Fin.F1) |].
    exists (matrix_vec_tail v). split.
    + intro i. exact (Hv (Fin.FS i)).
    + now rewrite matrix_vec_eta.
  - intros [head [Hhead [tail [Htail HP]]]].
    exists (matrix_vec_cons head tail). split; [| exact HP].
    intro i. refine (@Fin.caseS' n i (fun j =>
      R (matrix_vec_cons head tail j) (bound j)) _ _).
    + exact Hhead.
    + exact Htail.
Qed.

Theorem fin_vec_forall_iff : forall A n
    (P : (Fin.t (S n) -> A) -> Prop),
  (forall v, P v) <->
  forall head, forall tail : Fin.t n -> A,
    P (matrix_vec_cons head tail).
Proof. apply matrix_vec_forall_iff. Qed.

Theorem fin_vec_exists_iff : forall A n
    (P : (Fin.t (S n) -> A) -> Prop),
  (exists v, P v) <->
  exists head, exists tail : Fin.t n -> A,
    P (matrix_vec_cons head tail).
Proof. apply matrix_vec_exists_iff. Qed.
