(** Predicate-restricted finite folds. *)

From Stdlib Require Import Lists.List.

Set Implicit Arguments.
Unset Strict Implicit.

Fixpoint finite_fold {A B} (op : B -> B -> B) (unit : B)
    (f : A -> B) (xs : list A) : B :=
  match xs with
  | nil => unit
  | x :: rest => op (f x) (finite_fold op unit f rest)
  end.

Lemma finite_fold_filter_all : forall A B
    (op : B -> B -> B) unit (f : A -> B) keep xs,
  (forall x, List.In x xs -> keep x = true) ->
  finite_fold op unit f (List.filter keep xs) =
  finite_fold op unit f xs.
Proof.
  intros A B op unit f keep xs Hall.
  induction xs as [|x xs IH]; simpl; [reflexivity |].
  rewrite (Hall x (or_introl eq_refl)). simpl.
  f_equal. apply IH. intros y Hy. apply Hall. now right.
Qed.

Corollary finite_sup_filter_all : forall A
    (sup : A -> A -> A) bottom keep xs,
  (forall x, List.In x xs -> keep x = true) ->
  finite_fold sup bottom (fun x => x) (List.filter keep xs) =
  finite_fold sup bottom (fun x => x) xs.
Proof. intros. now apply finite_fold_filter_all. Qed.

Corollary finite_inf_filter_all : forall A
    (inf : A -> A -> A) top keep xs,
  (forall x, List.In x xs -> keep x = true) ->
  finite_fold inf top (fun x => x) (List.filter keep xs) =
  finite_fold inf top (fun x => x) xs.
Proof. intros. now apply finite_fold_filter_all. Qed.
