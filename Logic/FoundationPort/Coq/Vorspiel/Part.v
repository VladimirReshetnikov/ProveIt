(** Partial values and pointwise finite products. *)

From Stdlib Require Import Logic.FunctionalExtensionality Vectors.Fin.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record partial_value (A : Type) := {
  partial_member : A -> Prop;
  partial_member_unique : forall x y,
    partial_member x -> partial_member y -> x = y
}.

Arguments partial_member {A} _ _.

Definition partial_dom {A} (x : partial_value A) : Prop :=
  exists a, partial_member x a.

Definition partial_some {A} (a : A) : partial_value A :=
  {| partial_member := fun x => x = a;
     partial_member_unique := fun x y Hx Hy => eq_trans Hx (eq_sym Hy) |}.

Definition fin_partial_product {A} {n}
    (v : Fin.t n -> partial_value A) : partial_value (Fin.t n -> A).
Proof.
  refine {| partial_member := fun w => forall i, partial_member (v i) (w i) |}.
  intros w u Hw Hu. apply functional_extensionality. intro i.
  exact (@partial_member_unique A (v i) (w i) (u i) (Hw i) (Hu i)).
Defined.

Lemma fin_partial_product_member_iff : forall A n
    (w : Fin.t n -> A) (v : Fin.t n -> partial_value A),
  partial_member (fin_partial_product v) w <->
  forall i, partial_member (v i) (w i).
Proof. reflexivity. Qed.

Lemma partial_unit_dom_iff : forall x : partial_value unit,
  partial_dom x <-> partial_member x tt.
Proof.
  intro x. split.
  - intros [u Hu]. destruct u. exact Hu.
  - intro H. now exists tt.
Qed.
