(** Finite-vector elimination and lifting through explicit quotients.

    Rocq has no primitive quotient type.  We therefore expose exactly the
    representation data needed by the source theorems: every quotient value
    has a representative, representatives round-trip to the same quotient
    value, and choosing a representative of a constructed class is related
    to the original value. *)

From Stdlib Require Import Classes.RelationClasses Logic.ClassicalEpsilon Logic.FunctionalExtensionality
  Logic.ProofIrrelevance Logic.PropExtensionality Vectors.Fin.

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

(** A concrete quotient representation for every equivalence relation.
    Quotient values are predicates extensionally equal to one equivalence
    class.  Classical description chooses representatives; propositional and
    functional extensionality identify equal classes.  This supplies the
    quotient construction that Rocq intentionally leaves out of its kernel. *)
Definition equivalence_class_carrier {A}
    (R : A -> A -> Prop) : Type :=
  { P : A -> Prop |
    exists a : A, forall x, P x <-> R x a }.

Definition equivalence_class_mk {A} (R : A -> A -> Prop)
    (Hrefl : Reflexive R) (a : A) :
    equivalence_class_carrier R.
Proof.
  exists (fun x => R x a). exists a. intro x. reflexivity.
Defined.

Definition equivalence_class_repr {A} {R : A -> A -> Prop}
    (q : equivalence_class_carrier R) : A :=
  proj1_sig (constructive_indefinite_description _ (proj2_sig q)).

Lemma equivalence_class_repr_spec : forall A (R : A -> A -> Prop)
    (q : equivalence_class_carrier R) x,
  proj1_sig q x <-> R x (equivalence_class_repr q).
Proof.
  intros A R [P HP] x. unfold equivalence_class_repr. simpl.
  exact (proj2_sig (constructive_indefinite_description
    (fun a => forall y, P y <-> R y a) HP) x).
Qed.

Lemma equivalence_class_repr_mk_related : forall A
    (R : A -> A -> Prop) (Hequiv : Equivalence R) a,
  R (equivalence_class_repr
      (@equivalence_class_mk A R (@Equivalence_Reflexive A R Hequiv) a)) a.
Proof.
  intros A R Hequiv a.
  pose (b := equivalence_class_repr
    (@equivalence_class_mk A R (@Equivalence_Reflexive A R Hequiv) a)).
  apply (proj2 (@equivalence_class_repr_spec A R
    (@equivalence_class_mk A R (@Equivalence_Reflexive A R Hequiv) a) b)).
  apply (@Equivalence_Reflexive A R Hequiv).
Qed.

Lemma equivalence_class_mk_repr : forall A
    (R : A -> A -> Prop) (Hequiv : Equivalence R)
    (q : equivalence_class_carrier R),
  @equivalence_class_mk A R (@Equivalence_Reflexive A R Hequiv)
      (equivalence_class_repr q) = q.
Proof.
  intros A R Hequiv [P HP].
  apply eq_sig_hprop; [intros; apply proof_irrelevance |].
  apply functional_extensionality. intro x.
  apply propositional_extensionality.
  symmetry. apply equivalence_class_repr_spec.
Qed.

Lemma equivalence_class_mk_eq_iff : forall A
    (R : A -> A -> Prop) (Hequiv : Equivalence R) a b,
  @equivalence_class_mk A R (@Equivalence_Reflexive A R Hequiv) a =
  @equivalence_class_mk A R (@Equivalence_Reflexive A R Hequiv) b <->
  R a b.
Proof.
  intros A R Hequiv a b. split.
  - intro H.
    assert (Hpred : (fun x => R x a) = (fun x => R x b)).
    { now inversion H. }
    assert (Haa : R a a) by apply (@Equivalence_Reflexive A R Hequiv).
    change (R a b). change ((fun x => R x b) a).
    rewrite <- Hpred. exact Haa.
  - intro Hab. apply eq_sig_hprop; [intros; apply proof_irrelevance |].
    apply functional_extensionality. intro x.
    apply propositional_extensionality. split; intro Hx.
    + exact (@Equivalence_Transitive A R Hequiv x a b Hx Hab).
    + exact (@Equivalence_Transitive A R Hequiv x b a Hx
        (@Equivalence_Symmetric A R Hequiv a b Hab)).
Qed.

Definition equivalence_class_quotient {A} (R : A -> A -> Prop)
    (Hequiv : Equivalence R) : @explicit_quotient A R :=
  {| quotient_carrier := equivalence_class_carrier R;
     quotient_mk :=
       @equivalence_class_mk A R (@Equivalence_Reflexive A R Hequiv);
     quotient_repr := equivalence_class_repr;
     quotient_repr_mk_related :=
       equivalence_class_repr_mk_related Hequiv;
     quotient_mk_repr := equivalence_class_mk_repr Hequiv |}.

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
