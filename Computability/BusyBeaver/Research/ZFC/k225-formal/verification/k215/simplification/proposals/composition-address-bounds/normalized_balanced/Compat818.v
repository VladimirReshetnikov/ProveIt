(** Proof-library aliases for reproducing the extracted Rocq 9.1 dependency
    with Coq 8.18.  No executable definition is changed. *)
From Coq Require Import List Arith.
Definition length_firstn := @firstn_length.
Definition length_app := @app_length.
Definition length_map := @map_length.
Definition length_seq := seq_length.

Lemma nth_firstn {A : Type} (l : list A) (n k : nat) (d : A) :
  nth n (firstn k l) d = if n <? k then nth n l d else d.
Proof.
  revert l n. induction k as [|k IH]; intros [|a l] [|n]; simpl; auto.
  - change (d = if n <? k then d else d). destruct (n <? k); reflexivity.
Qed.
