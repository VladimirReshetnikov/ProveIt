(**
  Faithful standard HFS vectors and structural recursion.

  Foundation represents a vector by nested successor-pair codes:
  zero is nil and [x :: xs] is [pair x xs + 1].  The proof-facing wrapper
  below stores the corresponding list, while [hfs_vector_code_injective]
  proves that the raw nested HFS code loses no information.

  This first layer factors the common infrastructure used by the source's
  later maximum, suffix, concatenation, membership, repetition, and set
  conversion operations.  Indexing is total with zero beyond the end, exactly
  matching Foundation's recursively defined [nth].
*)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List NArith.NArith.
From Foundation.FirstOrder.Arithmetic.HFS Require Import Basic Seq.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Raw nested-pair codes *)

Definition hfs_vector_adjoin_code (x tail : hfs_code) : hfs_code :=
  N.succ (hfs_index_pair x tail).

Fixpoint hfs_vector_code_list (xs : list hfs_code) : hfs_code :=
  match xs with
  | [] => 0%N
  | x :: tail => hfs_vector_adjoin_code x (hfs_vector_code_list tail)
  end.

Lemma hfs_vector_code_list_nil :
  hfs_vector_code_list [] = 0%N.
Proof. reflexivity. Qed.

Lemma hfs_vector_code_list_cons : forall x xs,
  hfs_vector_code_list (x :: xs) =
  hfs_vector_adjoin_code x (hfs_vector_code_list xs).
Proof. reflexivity. Qed.

Lemma hfs_vector_adjoin_code_nonzero : forall x tail,
  hfs_vector_adjoin_code x tail <> 0%N.
Proof. intros x tail. unfold hfs_vector_adjoin_code. apply N.neq_succ_0. Qed.

Lemma hfs_vector_adjoin_code_injective : forall x tail y rest,
  hfs_vector_adjoin_code x tail = hfs_vector_adjoin_code y rest ->
  x = y /\ tail = rest.
Proof.
  intros x tail y rest H. unfold hfs_vector_adjoin_code in H.
  apply N.succ_inj in H. now apply hfs_index_pair_injective in H.
Qed.

Theorem hfs_vector_code_list_injective : forall xs ys,
  hfs_vector_code_list xs = hfs_vector_code_list ys -> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] H; simpl in H.
  - reflexivity.
  - exfalso. apply (@hfs_vector_adjoin_code_nonzero y
      (hfs_vector_code_list ys)). now symmetry.
  - exfalso. exact (@hfs_vector_adjoin_code_nonzero x
      (hfs_vector_code_list xs) H).
  - apply hfs_vector_adjoin_code_injective in H.
    destruct H as [-> Htail]. f_equal. now apply IH.
Qed.

(** * Typed vector interface *)

Record hfs_vector : Type := hfs_vector_of_list {
  hfs_vector_values : list hfs_code
}.

Definition hfs_vector_code (v : hfs_vector) : hfs_code :=
  hfs_vector_code_list (hfs_vector_values v).

Definition hfs_vector_empty : hfs_vector := hfs_vector_of_list [].

Definition hfs_vector_adjoin (x : hfs_code) (v : hfs_vector) : hfs_vector :=
  hfs_vector_of_list (x :: hfs_vector_values v).

Definition hfs_vector_head (v : hfs_vector) : hfs_code :=
  match hfs_vector_values v with
  | [] => hfs_empty
  | x :: _ => x
  end.

Definition hfs_vector_tail (v : hfs_vector) : hfs_vector :=
  match hfs_vector_values v with
  | [] => hfs_vector_empty
  | _ :: tail => hfs_vector_of_list tail
  end.

Definition hfs_vector_nth (v : hfs_vector) (i : nat) : hfs_code :=
  nth i (hfs_vector_values v) hfs_empty.

Definition hfs_vector_length (v : hfs_vector) : nat :=
  length (hfs_vector_values v).

Lemma hfs_vector_eq : forall v w,
  hfs_vector_values v = hfs_vector_values w -> v = w.
Proof. intros [xs] [ys]. simpl. now intros ->. Qed.

Theorem hfs_vector_code_injective : forall v w,
  hfs_vector_code v = hfs_vector_code w -> v = w.
Proof.
  intros [xs] [ys] H. apply hfs_vector_eq. simpl in *.
  now apply hfs_vector_code_list_injective.
Qed.

Lemma hfs_vector_empty_code :
  hfs_vector_code hfs_vector_empty = hfs_empty.
Proof. reflexivity. Qed.

Lemma hfs_vector_code_adjoin : forall x v,
  hfs_vector_code (hfs_vector_adjoin x v) =
  hfs_vector_adjoin_code x (hfs_vector_code v).
Proof. reflexivity. Qed.

Lemma hfs_vector_head_adjoin : forall x v,
  hfs_vector_head (hfs_vector_adjoin x v) = x.
Proof. reflexivity. Qed.

Lemma hfs_vector_tail_adjoin : forall x v,
  hfs_vector_tail (hfs_vector_adjoin x v) = v.
Proof. intros x [xs]. reflexivity. Qed.

Lemma hfs_vector_adjoin_injective : forall x v y w,
  hfs_vector_adjoin x v = hfs_vector_adjoin y w <->
  x = y /\ v = w.
Proof.
  intros x [xs] y [ys]. split.
  - intro H. inversion H. now split.
  - now intros [-> ->].
Qed.

Lemma hfs_vector_cases : forall v,
  v = hfs_vector_empty \/
  exists x tail, v = hfs_vector_adjoin x tail.
Proof.
  intros [[|x xs]].
  - now left.
  - right. exists x, (hfs_vector_of_list xs). reflexivity.
Qed.

Theorem hfs_vector_induction : forall (P : hfs_vector -> Prop),
  P hfs_vector_empty ->
  (forall x v, P v -> P (hfs_vector_adjoin x v)) ->
  forall v, P v.
Proof.
  intros P Hnil Hcons [xs]. induction xs as [|x xs IH].
  - exact Hnil.
  - change (P (hfs_vector_adjoin x (hfs_vector_of_list xs))).
    now apply Hcons.
Qed.

(** * Total indexing and length *)

Lemma hfs_vector_nth_empty : forall i,
  hfs_vector_nth hfs_vector_empty i = hfs_empty.
Proof. now intros [|i]. Qed.

Lemma hfs_vector_nth_adjoin_zero : forall x v,
  hfs_vector_nth (hfs_vector_adjoin x v) 0 = x.
Proof. reflexivity. Qed.

Lemma hfs_vector_nth_adjoin_succ : forall x v i,
  hfs_vector_nth (hfs_vector_adjoin x v) (S i) =
  hfs_vector_nth v i.
Proof. reflexivity. Qed.

Lemma hfs_vector_length_empty :
  hfs_vector_length hfs_vector_empty = 0.
Proof. reflexivity. Qed.

Lemma hfs_vector_length_adjoin : forall x v,
  hfs_vector_length (hfs_vector_adjoin x v) =
  S (hfs_vector_length v).
Proof. reflexivity. Qed.

Lemma hfs_vector_length_zero_iff : forall v,
  hfs_vector_length v = 0 <-> v = hfs_vector_empty.
Proof.
  intros [xs]. unfold hfs_vector_length. simpl. split.
  - intro H. apply length_zero_iff_nil in H. subst. reflexivity.
  - intro H. inversion H. reflexivity.
Qed.

Theorem hfs_vector_nth_out_of_range : forall v i,
  hfs_vector_length v <= i -> hfs_vector_nth v i = hfs_empty.
Proof.
  intros [xs] i H. unfold hfs_vector_length, hfs_vector_nth in *.
  now apply nth_overflow.
Qed.

Theorem hfs_vector_bounded_extensionality : forall v w,
  hfs_vector_length v = hfs_vector_length w ->
  (forall i, i < hfs_vector_length v ->
    hfs_vector_nth v i = hfs_vector_nth w i) ->
  v = w.
Proof.
  intros [xs] [ys] Hlength Hnth. apply hfs_vector_eq. simpl in *.
  apply nth_ext with (d := hfs_empty) (d' := hfs_empty).
  - exact Hlength.
  - exact Hnth.
Qed.

Definition hfs_vector_singleton (x : hfs_code) : hfs_vector :=
  hfs_vector_adjoin x hfs_vector_empty.

Definition hfs_vector_doubleton (x y : hfs_code) : hfs_vector :=
  hfs_vector_adjoin x (hfs_vector_singleton y).

Lemma hfs_vector_length_one_iff : forall v,
  hfs_vector_length v = 1 <->
  exists x, v = hfs_vector_singleton x.
Proof.
  intros [xs]. destruct xs as [|x xs].
  - simpl. split; [discriminate|]. intros [y H]. inversion H.
  - destruct xs as [|y ys].
    + simpl. split.
      * intro H. exists x. reflexivity.
      * intros [z H]. inversion H. reflexivity.
    + simpl. split; [discriminate|]. intros [z H]. inversion H.
Qed.

Lemma hfs_vector_length_two_iff : forall v,
  hfs_vector_length v = 2 <->
  exists x y, v = hfs_vector_doubleton x y.
Proof.
  intros [xs]. destruct xs as [|x xs].
  - simpl. split; [discriminate|]. intros [a [b H]]. inversion H.
  - destruct xs as [|y ys].
    + simpl. split; [discriminate|]. intros [a [b H]]. inversion H.
    + destruct ys as [|z zs].
      * simpl. split.
        -- intro H. exists x, y. reflexivity.
        -- intros [a [b H]]. inversion H. reflexivity.
      * simpl. split; [discriminate|]. intros [a [b H]]. inversion H.
Qed.

(** * Generic structural vector recursion *)

Record hfs_vector_recursion (P : Type) : Type := {
  hfs_vector_rec_nil : P -> hfs_code;
  hfs_vector_rec_adjoin : P -> hfs_code -> hfs_code -> hfs_code
}.

Arguments hfs_vector_rec_nil {P} _ _.
Arguments hfs_vector_rec_adjoin {P} _ _ _ _.

Fixpoint hfs_vector_rec_list {P} (r : hfs_vector_recursion P)
    (parameters : P) (xs : list hfs_code) : hfs_code :=
  match xs with
  | [] => hfs_vector_rec_nil r parameters
  | x :: tail =>
      hfs_vector_rec_adjoin r parameters x
        (hfs_vector_rec_list r parameters tail)
  end.

Definition hfs_vector_rec {P} (r : hfs_vector_recursion P)
    (parameters : P) (v : hfs_vector) : hfs_code :=
  hfs_vector_rec_list r parameters (hfs_vector_values v).

Lemma hfs_vector_rec_empty : forall P (r : hfs_vector_recursion P) p,
  hfs_vector_rec r p hfs_vector_empty = hfs_vector_rec_nil r p.
Proof. reflexivity. Qed.

Lemma hfs_vector_rec_adjoin_law : forall P
    (r : hfs_vector_recursion P) p x v,
  hfs_vector_rec r p (hfs_vector_adjoin x v) =
  hfs_vector_rec_adjoin r p x (hfs_vector_rec r p v).
Proof. reflexivity. Qed.

Theorem hfs_vector_rec_unique : forall P
    (r : hfs_vector_recursion P) p (f : hfs_vector -> hfs_code),
  f hfs_vector_empty = hfs_vector_rec_nil r p ->
  (forall x v,
    f (hfs_vector_adjoin x v) =
    hfs_vector_rec_adjoin r p x (f v)) ->
  forall v, f v = hfs_vector_rec r p v.
Proof.
  intros P r p f Hnil Hcons v.
  induction v using hfs_vector_induction.
  - exact Hnil.
  - rewrite Hcons, hfs_vector_rec_adjoin_law. now rewrite IHv.
Qed.

Definition hfs_vector_as_sequence (v : hfs_vector) : hfs_sequence :=
  hfs_sequence_of_list (hfs_vector_values v).

Lemma hfs_vector_as_sequence_length : forall v,
  hfs_sequence_length (hfs_vector_as_sequence v) = hfs_vector_length v.
Proof. reflexivity. Qed.

Lemma hfs_vector_as_sequence_nth : forall v i,
  hfs_sequence_znth (hfs_vector_as_sequence v) i = hfs_vector_nth v i.
Proof. reflexivity. Qed.
