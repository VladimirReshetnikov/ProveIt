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
From Foundation.FirstOrder.Arithmetic.HFS Require Import Basic Coding Seq.

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
  - left. now symmetry.
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
  (** The step sees the head, the raw code of the tail, and the recursive
      result.  Exposing the tail code is essential for source constructions
      such as [takeLast], whose branch condition inspects the tail length. *)
  hfs_vector_rec_adjoin :
    P -> hfs_code -> hfs_code -> hfs_code -> hfs_code
}.

Arguments hfs_vector_rec_nil {P} _ _.
Arguments hfs_vector_rec_adjoin {P} _ _ _ _ _.

Fixpoint hfs_vector_rec_list {P} (r : hfs_vector_recursion P)
    (parameters : P) (xs : list hfs_code) : hfs_code :=
  match xs with
  | [] => hfs_vector_rec_nil r parameters
  | x :: tail =>
      hfs_vector_rec_adjoin r parameters x
        (hfs_vector_code_list tail)
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
  hfs_vector_rec_adjoin r p x (hfs_vector_code v)
    (hfs_vector_rec r p v).
Proof. intros P r p x [xs]. reflexivity. Qed.

Theorem hfs_vector_rec_unique : forall P
    (r : hfs_vector_recursion P) p (f : hfs_vector -> hfs_code),
  f hfs_vector_empty = hfs_vector_rec_nil r p ->
  (forall x v,
    f (hfs_vector_adjoin x v) =
    hfs_vector_rec_adjoin r p x (hfs_vector_code v) (f v)) ->
  forall v, f v = hfs_vector_rec r p v.
Proof.
  intros P r p f Hnil Hcons v.
  induction v using hfs_vector_induction.
  - exact Hnil.
  - rewrite Hcons, hfs_vector_rec_adjoin_law. now rewrite IHv.
Qed.

(** * Maximum entry *)

Definition hfs_vector_max_recursion : hfs_vector_recursion unit :=
  {| hfs_vector_rec_nil := fun _ => 0%N;
     hfs_vector_rec_adjoin :=
       fun _ x _tail_code recursive_max => N.max x recursive_max |}.

Definition hfs_vector_max (v : hfs_vector) : hfs_code :=
  hfs_vector_rec hfs_vector_max_recursion tt v.

Lemma hfs_vector_max_empty :
  hfs_vector_max hfs_vector_empty = 0%N.
Proof. reflexivity. Qed.

Lemma hfs_vector_max_adjoin : forall x v,
  hfs_vector_max (hfs_vector_adjoin x v) =
  N.max x (hfs_vector_max v).
Proof. intros x [xs]. reflexivity. Qed.

Theorem hfs_vector_nth_le_max : forall v i,
  i < hfs_vector_length v ->
  (hfs_vector_nth v i <= hfs_vector_max v)%N.
Proof.
  induction v using hfs_vector_induction; intros i Hi.
  - rewrite hfs_vector_length_empty in Hi. lia.
  - destruct i as [|i].
    + rewrite hfs_vector_nth_adjoin_zero, hfs_vector_max_adjoin.
      apply N.le_max_l.
    + rewrite hfs_vector_nth_adjoin_succ, hfs_vector_max_adjoin.
      apply N.le_trans with (m := hfs_vector_max v).
      * apply IHv. rewrite hfs_vector_length_adjoin in Hi. lia.
      * apply N.le_max_r.
Qed.

Theorem hfs_vector_max_le : forall v z,
  (forall i, i < hfs_vector_length v ->
    (hfs_vector_nth v i <= z)%N) ->
  (hfs_vector_max v <= z)%N.
Proof.
  induction v using hfs_vector_induction; intros z Hbound.
  - rewrite hfs_vector_max_empty. apply N.le_0_l.
  - rewrite hfs_vector_max_adjoin. apply N.max_lub.
    + specialize (Hbound 0).
      rewrite hfs_vector_nth_adjoin_zero in Hbound. apply Hbound.
      rewrite hfs_vector_length_adjoin. lia.
    + apply IHv. intros i Hi.
      specialize (Hbound (S i)).
      rewrite hfs_vector_nth_adjoin_succ in Hbound. apply Hbound.
      rewrite hfs_vector_length_adjoin. lia.
Qed.

Theorem hfs_vector_max_le_iff : forall v z,
  (hfs_vector_max v <= z)%N <->
  forall i, i < hfs_vector_length v ->
    (hfs_vector_nth v i <= z)%N.
Proof.
  intros v z. split.
  - intros Hmax i Hi. eapply N.le_trans.
    + now apply hfs_vector_nth_le_max.
    + exact Hmax.
  - apply hfs_vector_max_le.
Qed.

(** * Suffixes *)

Definition hfs_vector_take_last (v : hfs_vector) (k : nat) : hfs_vector :=
  hfs_vector_of_list
    (skipn (hfs_vector_length v - k) (hfs_vector_values v)).

Lemma hfs_vector_take_last_values : forall v k,
  hfs_vector_values (hfs_vector_take_last v k) =
  skipn (hfs_vector_length v - k) (hfs_vector_values v).
Proof. reflexivity. Qed.

Lemma hfs_vector_take_last_empty : forall k,
  hfs_vector_take_last hfs_vector_empty k = hfs_vector_empty.
Proof. reflexivity. Qed.

Lemma hfs_vector_take_last_adjoin : forall x v k,
  hfs_vector_take_last (hfs_vector_adjoin x v) k =
  if Nat.ltb (hfs_vector_length v) k
  then hfs_vector_adjoin x v
  else hfs_vector_take_last v k.
Proof.
  intros x [xs] k.
  change
    (hfs_vector_of_list (skipn (S (length xs) - k) (x :: xs)) =
     if Nat.ltb (length xs) k
     then hfs_vector_of_list (x :: xs)
     else hfs_vector_of_list (skipn (length xs - k) xs)).
  destruct (Nat.ltb (length xs) k) eqn:Hcompare.
  - apply Nat.ltb_lt in Hcompare.
    replace (S (length xs) - k) with 0 by lia. reflexivity.
  - apply Nat.ltb_ge in Hcompare.
    replace (S (length xs) - k) with (S (length xs - k)) by lia.
    reflexivity.
Qed.

Theorem hfs_vector_take_last_length : forall v k,
  hfs_vector_length (hfs_vector_take_last v k) =
  Nat.min k (hfs_vector_length v).
Proof.
  intros [xs] k. unfold hfs_vector_take_last, hfs_vector_length. simpl.
  rewrite length_skipn.
  destruct (Nat.le_ge_cases k (length xs)) as [Hle | Hge].
  - rewrite Nat.min_l by exact Hle. lia.
  - rewrite Nat.min_r by exact Hge. lia.
Qed.

Corollary hfs_vector_take_last_length_exact : forall v k,
  k <= hfs_vector_length v ->
  hfs_vector_length (hfs_vector_take_last v k) = k.
Proof.
  intros v k Hle. rewrite hfs_vector_take_last_length.
  now apply Nat.min_l.
Qed.

Theorem hfs_vector_take_last_all : forall v k,
  hfs_vector_length v <= k -> hfs_vector_take_last v k = v.
Proof.
  intros [xs] k Hle. change (length xs <= k) in Hle.
  apply hfs_vector_eq.
  change (skipn (length xs - k) xs = xs).
  replace (length xs - k) with 0 by lia. reflexivity.
Qed.

Corollary hfs_vector_take_last_full : forall v,
  hfs_vector_take_last v (hfs_vector_length v) = v.
Proof. intro v. apply hfs_vector_take_last_all. reflexivity. Qed.

Lemma hfs_vector_take_last_zero : forall v,
  hfs_vector_take_last v 0 = hfs_vector_empty.
Proof.
  intros [xs]. unfold hfs_vector_take_last, hfs_vector_length,
    hfs_vector_empty. simpl. rewrite Nat.sub_0_r. f_equal.
  apply skipn_all.
Qed.

Theorem hfs_vector_take_last_nth : forall v k j,
  hfs_vector_nth (hfs_vector_take_last v k) j =
  hfs_vector_nth v (hfs_vector_length v - k + j).
Proof.
  intros [xs] k j. unfold hfs_vector_take_last, hfs_vector_nth,
    hfs_vector_length. simpl. now apply nth_skipn.
Qed.

Lemma skipn_nth_cons : forall A (xs : list A) default start,
  start < length xs ->
  skipn start xs = nth start xs default :: skipn (S start) xs.
Proof.
  intros A xs default start. revert xs.
  induction start as [|start IH]; intros [|x xs] Hlength;
    simpl in *; try lia.
  - reflexivity.
  - apply IH. lia.
Qed.

Theorem hfs_vector_take_last_succ : forall v i,
  i < hfs_vector_length v ->
  hfs_vector_take_last v (S i) =
  hfs_vector_adjoin
    (hfs_vector_nth v (hfs_vector_length v - S i))
    (hfs_vector_take_last v i).
Proof.
  intros [xs] i Hi. change (i < length xs) in Hi.
  change
    (hfs_vector_of_list (skipn (length xs - S i) xs) =
     hfs_vector_of_list
       (nth (length xs - S i) xs hfs_empty ::
        skipn (length xs - i) xs)).
  f_equal.
  set (start := length xs - S i).
  rewrite (@skipn_nth_cons hfs_code xs hfs_empty start) by
    (unfold start; lia).
  replace (length xs - i) with (S start) by (unfold start; lia).
  reflexivity.
Qed.

(** * Appending one entry *)

(** Foundation calls this operation [concat], although its second argument is
    one entry rather than another vector.  [snoc] records the standard list
    terminology; [concat] remains as a source-compatible alias. *)
Definition hfs_vector_snoc (v : hfs_vector) (z : hfs_code) : hfs_vector :=
  hfs_vector_of_list (hfs_vector_values v ++ [z]).

Definition hfs_vector_concat := hfs_vector_snoc.

Lemma hfs_vector_concat_empty : forall z,
  hfs_vector_concat hfs_vector_empty z = hfs_vector_singleton z.
Proof. reflexivity. Qed.

Lemma hfs_vector_concat_adjoin : forall x v z,
  hfs_vector_concat (hfs_vector_adjoin x v) z =
  hfs_vector_adjoin x (hfs_vector_concat v z).
Proof. reflexivity. Qed.

Theorem hfs_vector_concat_length : forall v z,
  hfs_vector_length (hfs_vector_concat v z) =
  S (hfs_vector_length v).
Proof.
  intros [xs] z. unfold hfs_vector_concat, hfs_vector_snoc,
    hfs_vector_length. simpl. rewrite length_app. simpl. lia.
Qed.

Theorem hfs_vector_concat_nth_old : forall v z i,
  i < hfs_vector_length v ->
  hfs_vector_nth (hfs_vector_concat v z) i = hfs_vector_nth v i.
Proof.
  intros [xs] z i Hi. unfold hfs_vector_concat, hfs_vector_snoc,
    hfs_vector_nth, hfs_vector_length in *. simpl in *.
  now apply app_nth1.
Qed.

Theorem hfs_vector_concat_nth_last : forall v z,
  hfs_vector_nth (hfs_vector_concat v z) (hfs_vector_length v) = z.
Proof.
  intros [xs] z. unfold hfs_vector_concat, hfs_vector_snoc,
    hfs_vector_nth, hfs_vector_length. simpl. apply nth_middle.
Qed.

Corollary hfs_vector_concat_nth_at_length : forall v z i,
  hfs_vector_length v = i ->
  hfs_vector_nth (hfs_vector_concat v z) i = z.
Proof. intros v z i <-. apply hfs_vector_concat_nth_last. Qed.

(** * Membership and subset *)

Definition hfs_vector_mem (x : hfs_code) (v : hfs_vector) : Prop :=
  In x (hfs_vector_values v).

Lemma hfs_vector_mem_iff_nth_error : forall x v,
  hfs_vector_mem x v <->
  exists i, nth_error (hfs_vector_values v) i = Some x.
Proof.
  intros x [xs]. unfold hfs_vector_mem. simpl. apply In_iff_nth_error.
Qed.

Theorem hfs_vector_mem_iff_nth : forall x v,
  hfs_vector_mem x v <->
  exists i, i < hfs_vector_length v /\ x = hfs_vector_nth v i.
Proof.
  intros x [xs]. unfold hfs_vector_mem, hfs_vector_length,
    hfs_vector_nth. simpl. split.
  - intro Hmem. apply In_nth_error in Hmem.
    destruct Hmem as [i Hi]. exists i. split.
    + apply (proj1 (nth_error_Some xs i)). congruence.
    + symmetry. now apply nth_error_nth with (l := xs) (n := i).
  - intros [i [Hi ->]]. now apply nth_In.
Qed.

Lemma hfs_vector_not_mem_empty : forall x,
  ~ hfs_vector_mem x hfs_vector_empty.
Proof. intros x H. exact H. Qed.

Theorem hfs_vector_nth_mem : forall v i,
  i < hfs_vector_length v ->
  hfs_vector_mem (hfs_vector_nth v i) v.
Proof.
  intros [xs] i Hi. unfold hfs_vector_mem, hfs_vector_nth,
    hfs_vector_length in *. simpl in *. now apply nth_In.
Qed.

Lemma hfs_vector_mem_adjoin_head : forall x v,
  hfs_vector_mem x (hfs_vector_adjoin x v).
Proof. now intros x [xs]; left. Qed.

Lemma hfs_vector_mem_adjoin_iff : forall x y v,
  hfs_vector_mem x (hfs_vector_adjoin y v) <->
  x = y \/ hfs_vector_mem x v.
Proof.
  intros x y [xs]. unfold hfs_vector_mem. simpl. split;
    intros [H | H].
  - now left.
  - now right.
  - left. now symmetry.
  - now right.
Qed.

Definition hfs_vector_subset (v w : hfs_vector) : Prop :=
  forall x, hfs_vector_mem x v -> hfs_vector_mem x w.

Lemma hfs_vector_subset_empty : forall v,
  hfs_vector_subset hfs_vector_empty v.
Proof.
  intros v x H. exfalso. now apply hfs_vector_not_mem_empty in H.
Qed.

Lemma hfs_vector_subset_refl : forall v,
  hfs_vector_subset v v.
Proof. firstorder. Qed.

Lemma hfs_vector_subset_trans : forall u v w,
  hfs_vector_subset u v ->
  hfs_vector_subset v w ->
  hfs_vector_subset u w.
Proof. firstorder. Qed.

Lemma hfs_vector_subset_adjoin_tail : forall x v,
  hfs_vector_subset v (hfs_vector_adjoin x v).
Proof.
  intros x v y Hy. apply hfs_vector_mem_adjoin_iff. now right.
Qed.

Theorem hfs_vector_subset_adjoin_iff : forall x v w,
  hfs_vector_subset (hfs_vector_adjoin x v) w <->
  hfs_vector_mem x w /\ hfs_vector_subset v w.
Proof.
  intros x v w. split.
  - intro Hsubset. split.
    + apply Hsubset. apply hfs_vector_mem_adjoin_head.
    + intros y Hy. apply Hsubset. apply hfs_vector_mem_adjoin_iff.
      now right.
  - intros [Hx Htail] y Hy. apply hfs_vector_mem_adjoin_iff in Hy.
    destruct Hy as [-> | Hy]; [exact Hx | now apply Htail].
Qed.

(** * Repetition *)

Definition hfs_vector_repeat (x : hfs_code) (k : nat) : hfs_vector :=
  hfs_vector_of_list (repeat x k).

Lemma hfs_vector_repeat_zero : forall x,
  hfs_vector_repeat x 0 = hfs_vector_empty.
Proof. reflexivity. Qed.

Lemma hfs_vector_repeat_succ : forall x k,
  hfs_vector_repeat x (S k) =
  hfs_vector_adjoin x (hfs_vector_repeat x k).
Proof. reflexivity. Qed.

Theorem hfs_vector_repeat_length : forall x k,
  hfs_vector_length (hfs_vector_repeat x k) = k.
Proof.
  intros x k. unfold hfs_vector_repeat, hfs_vector_length. simpl.
  apply repeat_length.
Qed.

Theorem hfs_vector_repeat_nth : forall x k i,
  i < k -> hfs_vector_nth (hfs_vector_repeat x k) i = x.
Proof.
  intros x k i Hi. unfold hfs_vector_repeat, hfs_vector_nth. simpl.
  now apply nth_repeat_lt.
Qed.

Theorem hfs_vector_mem_repeat_iff : forall y x k,
  hfs_vector_mem y (hfs_vector_repeat x k) <->
  0 < k /\ y = x.
Proof.
  intros y x k. unfold hfs_vector_mem, hfs_vector_repeat. simpl. split.
  - intro Hmem. split.
    + destruct k; simpl in Hmem; [contradiction | lia].
    + now apply repeat_spec in Hmem.
  - intros [Hpositive ->]. destruct k; [lia |]. simpl. now left.
Qed.

(** * Duplicate-erasing conversion to an HFS set *)

Definition hfs_vector_to_set (v : hfs_vector) : hfs_code :=
  hfs_arithmetize_list (hfs_vector_values v).

Lemma hfs_vector_to_set_empty :
  hfs_vector_to_set hfs_vector_empty = hfs_empty.
Proof. reflexivity. Qed.

Lemma hfs_vector_to_set_adjoin : forall x v,
  hfs_vector_to_set (hfs_vector_adjoin x v) =
  hfs_insert x (hfs_vector_to_set v).
Proof. reflexivity. Qed.

Theorem hfs_mem_vector_to_set_iff : forall x v,
  hfs_mem x (hfs_vector_to_set v) <-> hfs_vector_mem x v.
Proof.
  intros x [xs]. unfold hfs_vector_to_set, hfs_vector_mem. simpl.
  apply hfs_mem_arithmetize_list_iff.
Qed.

Corollary hfs_mem_vector_to_set_iff_nth : forall x v,
  hfs_mem x (hfs_vector_to_set v) <->
  exists i, i < hfs_vector_length v /\ x = hfs_vector_nth v i.
Proof.
  intros x v. rewrite hfs_mem_vector_to_set_iff.
  apply hfs_vector_mem_iff_nth.
Qed.

Corollary hfs_vector_nth_mem_to_set : forall v i,
  i < hfs_vector_length v ->
  hfs_mem (hfs_vector_nth v i) (hfs_vector_to_set v).
Proof.
  intros v i Hi. apply hfs_mem_vector_to_set_iff.
  now apply hfs_vector_nth_mem.
Qed.

Theorem hfs_vector_to_set_subset_iff : forall v w,
  hfs_subset (hfs_vector_to_set v) (hfs_vector_to_set w) <->
  hfs_vector_subset v w.
Proof.
  intros v w. unfold hfs_subset, hfs_vector_subset. split;
    intros Hsubset x Hx.
  - apply hfs_mem_vector_to_set_iff. apply Hsubset.
    now apply hfs_mem_vector_to_set_iff.
  - apply hfs_mem_vector_to_set_iff. apply Hsubset.
    now apply hfs_mem_vector_to_set_iff.
Qed.

(** * Conversion to the indexed sequence representation *)

Definition hfs_vector_as_sequence (v : hfs_vector) : hfs_sequence :=
  hfs_sequence_of_list (hfs_vector_values v).

Lemma hfs_vector_as_sequence_length : forall v,
  hfs_sequence_length (hfs_vector_as_sequence v) = hfs_vector_length v.
Proof. reflexivity. Qed.

Lemma hfs_vector_as_sequence_nth : forall v i,
  hfs_sequence_znth (hfs_vector_as_sequence v) i = hfs_vector_nth v i.
Proof. reflexivity. Qed.
