(** Duplicate-tolerant finite-family arithmetization into HFS bit codes. *)

From Stdlib Require Import Lists.List NArith.NArith.
From Foundation.FirstOrder.Arithmetic.HFS Require Import Basic.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Fixpoint hfs_arithmetize_list (xs : list hfs_code) : hfs_code :=
  match xs with
  | [] => hfs_empty
  | x :: tail => hfs_insert x (hfs_arithmetize_list tail)
  end.

Lemma hfs_arithmetize_list_nil :
  hfs_arithmetize_list [] = hfs_empty.
Proof. reflexivity. Qed.

Lemma hfs_arithmetize_list_cons : forall x xs,
  hfs_arithmetize_list (x :: xs) =
  hfs_insert x (hfs_arithmetize_list xs).
Proof. reflexivity. Qed.

Theorem hfs_mem_arithmetize_list_iff : forall x xs,
  hfs_mem x (hfs_arithmetize_list xs) <-> In x xs.
Proof.
  intros x xs. induction xs as [|y ys IH]; simpl.
  - apply hfs_mem_empty_iff.
  - rewrite hfs_mem_insert_iff, IH. split.
    + intros [H | H]; [left; now symmetry|now right].
    + intros [H | H]; [left; now symmetry|now right].
Qed.

Lemma hfs_arithmetize_list_app : forall xs ys,
  hfs_arithmetize_list (xs ++ ys) =
  hfs_union (hfs_arithmetize_list xs) (hfs_arithmetize_list ys).
Proof.
  intros xs ys. apply hfs_extensionality. intro x.
  rewrite hfs_mem_arithmetize_list_iff, hfs_mem_union_iff,
    !hfs_mem_arithmetize_list_iff, in_app_iff. reflexivity.
Qed.

Lemma hfs_arithmetize_list_nodup : forall xs,
  hfs_arithmetize_list (nodup N.eq_dec xs) = hfs_arithmetize_list xs.
Proof.
  intro xs. apply hfs_extensionality. intro x.
  rewrite !hfs_mem_arithmetize_list_iff, nodup_In. reflexivity.
Qed.

Lemma hfs_arithmetize_list_insert : forall x xs,
  hfs_arithmetize_list (x :: nodup N.eq_dec xs) =
  hfs_insert x (hfs_arithmetize_list xs).
Proof.
  intros. simpl. now rewrite hfs_arithmetize_list_nodup.
Qed.
