(** Partial values and pointwise finite products. *)

From Stdlib Require Import Arith.PeanoNat Logic.FunctionalExtensionality Vectors.Fin.

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

Definition partial_none {A} : partial_value A :=
  {| partial_member := fun _ => False;
     partial_member_unique := fun x y Hx _ => False_rect (x = y) Hx |}.

Definition partial_bind {A B} (x : partial_value A)
    (f : A -> partial_value B) : partial_value B.
Proof.
  refine {| partial_member := fun b =>
    exists a, partial_member x a /\ partial_member (f a) b |}.
  intros b c [a [Ha Hb]] [d [Hd Hc]].
  pose proof (@partial_member_unique A x a d Ha Hd) as ->.
  exact (@partial_member_unique B (f d) b c Hb Hc).
Defined.

Definition partial_map {A B} (f : A -> B) (x : partial_value A) :
    partial_value B :=
  partial_bind x (fun a => partial_some (f a)).

Lemma partial_bind_some : forall A B (a : A) (f : A -> partial_value B) b,
  partial_member (partial_bind (partial_some a) f) b <->
  partial_member (f a) b.
Proof.
  intros A B a f b. split.
  - intros [x [-> H]]. exact H.
  - intro H. exists a. now split.
Qed.

Lemma partial_map_member_iff : forall A B (f : A -> B)
    (x : partial_value A) b,
  partial_member (partial_map f x) b <->
  exists a, partial_member x a /\ f a = b.
Proof.
  intros A B f x b. unfold partial_map, partial_bind. simpl.
  split.
  - intros [a [Ha Hb]]. exists a. split; [exact Ha | now symmetry].
  - intros [a [Ha Hfa]]. exists a. split; [exact Ha | now symmetry].
Qed.

Definition partial_find_zero (f : nat -> nat) : partial_value nat.
Proof.
  refine {| partial_member := fun n =>
    f n = 0 /\ forall m, m < n -> f m <> 0 |}.
  intros n k [Hn Hleastn] [Hk Hleastk].
  destruct (Nat.lt_trichotomy n k) as [Hlt | [-> | Hgt]].
  - exfalso. exact (Hleastk n Hlt Hn).
  - reflexivity.
  - exfalso. exact (Hleastn k Hgt Hk).
Defined.

Lemma partial_find_zero_member_iff : forall f n,
  partial_member (partial_find_zero f) n <->
  f n = 0 /\ forall m, m < n -> f m <> 0.
Proof. reflexivity. Qed.

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
