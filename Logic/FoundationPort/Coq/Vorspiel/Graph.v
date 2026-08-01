(** Graph predicates for finite-vector and curried functions. *)

From Stdlib Require Import Vectors.Fin.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition function_graph_vector {A} {k}
    (f : (Fin.t k -> A) -> A) : (Fin.t (S k) -> A) -> Prop :=
  fun v => v Fin.F1 = f (fun i => v (Fin.FS i)).

Definition function_graph {A R} (f : A -> R) : R -> A -> Prop :=
  fun y x => y = f x.

Definition function_graph2 {A B R} (f : A -> B -> R) :
    R -> A -> B -> Prop :=
  fun y x1 x2 => y = f x1 x2.

Definition function_graph3 {A B C R} (f : A -> B -> C -> R) :
    R -> A -> B -> C -> Prop :=
  fun y x1 x2 x3 => y = f x1 x2 x3.

Definition function_graph4 {A B C D R} (f : A -> B -> C -> D -> R) :
    R -> A -> B -> C -> D -> Prop :=
  fun y x1 x2 x3 x4 => y = f x1 x2 x3 x4.

Definition function_graph5 {A B C D E R}
    (f : A -> B -> C -> D -> E -> R) :
    R -> A -> B -> C -> D -> E -> Prop :=
  fun y x1 x2 x3 x4 x5 => y = f x1 x2 x3 x4 x5.

Lemma function_graph_eq : forall A R (f : A -> R) y x,
  function_graph f y x -> f x = y.
Proof. intros A R f y x H. symmetry. exact H. Qed.

Lemma function_graph_iff_left : forall A R (f : A -> R) y x,
  f x = y <-> function_graph f y x.
Proof. intros A R f y x. unfold function_graph. split; intro H; now symmetry. Qed.

Lemma function_graph_iff_right : forall A R (f : A -> R) y x,
  y = f x <-> function_graph f y x.
Proof. reflexivity. Qed.

Lemma function_graph2_eq : forall A B R (f : A -> B -> R) y x1 x2,
  function_graph2 f y x1 x2 -> f x1 x2 = y.
Proof. intros A B R f y x1 x2 H. symmetry. exact H. Qed.

Lemma function_graph2_iff_left : forall A B R (f : A -> B -> R) y x1 x2,
  f x1 x2 = y <-> function_graph2 f y x1 x2.
Proof. intros A B R f y x1 x2. unfold function_graph2. split; intro H; now symmetry. Qed.

Lemma function_graph2_iff_right : forall A B R (f : A -> B -> R) y x1 x2,
  y = f x1 x2 <-> function_graph2 f y x1 x2.
Proof. reflexivity. Qed.

Lemma function_graph3_eq : forall A B C R
    (f : A -> B -> C -> R) y x1 x2 x3,
  function_graph3 f y x1 x2 x3 -> f x1 x2 x3 = y.
Proof. intros A B C R f y x1 x2 x3 H. symmetry. exact H. Qed.

Lemma function_graph3_iff_left : forall A B C R
    (f : A -> B -> C -> R) y x1 x2 x3,
  f x1 x2 x3 = y <-> function_graph3 f y x1 x2 x3.
Proof.
  intros A B C R f y x1 x2 x3. unfold function_graph3.
  split; intro H; now symmetry.
Qed.

Lemma function_graph3_iff_right : forall A B C R
    (f : A -> B -> C -> R) y x1 x2 x3,
  y = f x1 x2 x3 <-> function_graph3 f y x1 x2 x3.
Proof. reflexivity. Qed.
