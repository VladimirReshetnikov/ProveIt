(**
  Executable finite sequences in the standard HFS model.

  A sequence is represented exactly as in Foundation: its HFS code is the
  finite set of pairs [(i,x)] saying that the value at index [i] is [x].
  Indices are distinct, so the set code retains both order and repetition of
  values.  The proof-facing [hfs_sequence] wrapper stores the corresponding
  list; [hfs_sequence_code_injective] proves that this is a faithful, rather
  than merely convenient, presentation of the raw HFS representation.

  The source develops the same operations in every nonstandard model of
  ISigma_1 and then proves their internal definability.  Here all operations
  are constructive and executable in the standard [N] model.  Relational
  graphs expose length and indexing directly on raw codes, while the wrapper
  makes the uniquely determined operations computational.
*)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List NArith.NArith
  Vectors.Fin.
From Foundation.Vorspiel Require Import Arithmetic.
From Foundation.Vorspiel.Fin Require Import Basic.
From Foundation.Vorspiel.List Require Import Chain.
From Foundation.FirstOrder.Arithmetic.HFS Require Import Basic.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Pairing and its exact projections *)

Definition hfs_index_pair (i x : N) : hfs_code :=
  N.of_nat (nat_pair (N.to_nat i) (N.to_nat x)).

Definition hfs_index_fst (p : hfs_code) : N :=
  N.of_nat (nat_unpair1 (N.to_nat p)).

Definition hfs_index_snd (p : hfs_code) : N :=
  N.of_nat (nat_unpair2 (N.to_nat p)).

Lemma hfs_index_fst_pair : forall i x,
  hfs_index_fst (hfs_index_pair i x) = i.
Proof.
  intros i x. unfold hfs_index_fst, hfs_index_pair.
  rewrite Nat2N.id, nat_unpair1_pair, N2Nat.id. reflexivity.
Qed.

Lemma hfs_index_snd_pair : forall i x,
  hfs_index_snd (hfs_index_pair i x) = x.
Proof.
  intros i x. unfold hfs_index_snd, hfs_index_pair.
  rewrite Nat2N.id, nat_unpair2_pair, N2Nat.id. reflexivity.
Qed.

Lemma hfs_index_pair_injective : forall i x j y,
  hfs_index_pair i x = hfs_index_pair j y -> i = j /\ x = y.
Proof.
  intros i x j y H.
  split.
  - rewrite <- (hfs_index_fst_pair i x),
      <- (hfs_index_fst_pair j y). now rewrite H.
  - rewrite <- (hfs_index_snd_pair i x),
      <- (hfs_index_snd_pair j y). now rewrite H.
Qed.

Lemma hfs_index_pair_eq_iff : forall i x j y,
  hfs_index_pair i x = hfs_index_pair j y <-> i = j /\ x = y.
Proof.
  intros. split; [apply hfs_index_pair_injective|].
  now intros [-> ->].
Qed.

Lemma hfs_index_pair_projections : forall p,
  hfs_index_pair (hfs_index_fst p) (hfs_index_snd p) = p.
Proof.
  intro p. unfold hfs_index_pair, hfs_index_fst, hfs_index_snd.
  rewrite !Nat2N.id, nat_pair_unpair, N2Nat.id. reflexivity.
Qed.

Local Lemma hfs_nat_to_N_le : forall a b,
  a <= b -> (N.of_nat a <= N.of_nat b)%N.
Proof.
  intros a b Hle. unfold N.le. rewrite <- Nat2N.inj_compare.
  now apply Nat.compare_le_iff.
Qed.

Local Lemma hfs_N_to_nat_le : forall a b,
  (a <= b)%N -> N.to_nat a <= N.to_nat b.
Proof.
  intros a b Hle. apply (proj1 (Nat.compare_le_iff _ _)).
  rewrite <- N2Nat.inj_compare. exact Hle.
Qed.

Lemma hfs_index_pair_left_le : forall i x,
  (i <= hfs_index_pair i x)%N.
Proof.
  intros i x. unfold hfs_index_pair. rewrite <- (N2Nat.id i) at 1.
  apply hfs_nat_to_N_le. apply nat_le_pair_left.
Qed.

Lemma hfs_index_pair_right_le : forall i x,
  (x <= hfs_index_pair i x)%N.
Proof.
  intros i x. unfold hfs_index_pair. rewrite <- (N2Nat.id x) at 1.
  apply hfs_nat_to_N_le. apply nat_le_pair_right.
Qed.

Lemma hfs_index_pair_monotone : forall i x j y,
  (i <= j)%N -> (x <= y)%N ->
  (hfs_index_pair i x <= hfs_index_pair j y)%N.
Proof.
  intros i x j y Hi Hx. unfold hfs_index_pair.
  apply hfs_nat_to_N_le. apply nat_pair_monotone.
  - now apply hfs_N_to_nat_le.
  - now apply hfs_N_to_nat_le.
Qed.

Lemma hfs_index_fst_le : forall p,
  (hfs_index_fst p <= p)%N.
Proof.
  intro p. rewrite <- (hfs_index_pair_projections p) at 2.
  apply hfs_index_pair_left_le.
Qed.

Lemma hfs_index_snd_le : forall p,
  (hfs_index_snd p <= p)%N.
Proof.
  intro p. rewrite <- (hfs_index_pair_projections p) at 2.
  apply hfs_index_pair_right_le.
Qed.

(** * Raw HFS coding *)

Fixpoint hfs_sequence_code_from (start : nat) (xs : list hfs_code)
    : hfs_code :=
  match xs with
  | [] => hfs_empty
  | x :: tail =>
      hfs_insert (hfs_index_pair (N.of_nat start) x)
        (hfs_sequence_code_from (S start) tail)
  end.

Definition hfs_sequence_code_list (xs : list hfs_code) : hfs_code :=
  hfs_sequence_code_from 0 xs.

Inductive hfs_sequence_entry_from :
    nat -> list hfs_code -> hfs_code -> Prop :=
| hfs_sequence_entry_here : forall start x xs,
    hfs_sequence_entry_from start (x :: xs)
      (hfs_index_pair (N.of_nat start) x)
| hfs_sequence_entry_there : forall start x xs p,
    hfs_sequence_entry_from (S start) xs p ->
    hfs_sequence_entry_from start (x :: xs) p.

Lemma hfs_mem_sequence_code_from_iff : forall start xs p,
  hfs_mem p (hfs_sequence_code_from start xs) <->
  hfs_sequence_entry_from start xs p.
Proof.
  intros start xs. revert start.
  induction xs as [|x xs IH]; intros start p; simpl.
  - rewrite hfs_mem_empty_iff. split; [contradiction|intro H; inversion H].
  - rewrite hfs_mem_insert_iff, IH. split.
    + intros [-> | H].
      * constructor.
      * now constructor 2.
    + intro H. inversion H; subst.
      * now left.
      * now right.
Qed.

Lemma hfs_sequence_entry_from_nth_error : forall start xs p,
  hfs_sequence_entry_from start xs p <->
  exists k x,
    nth_error xs k = Some x /\
    p = hfs_index_pair (N.of_nat (start + k)) x.
Proof.
  intros start xs p. split.
  - intro H. induction H.
    + exists 0, x. split; [reflexivity|].
      replace (start + 0) with start by lia. reflexivity.
    + destruct IHhfs_sequence_entry_from as [k [y [Hnth ->]]].
      exists (S k), y. simpl. split; [exact Hnth|].
      replace (start + S k) with (S start + k) by lia. reflexivity.
  - intros [k [x [Hnth ->]]]. revert start k x Hnth.
    induction xs as [|y ys IH]; intros start k x Hnth; destruct k;
      simpl in Hnth;
      try discriminate.
    + inversion Hnth; subst. replace (start + 0) with start by lia.
      constructor.
    + replace (start + S k) with (S start + k) by lia.
      constructor 2. now apply IH with (k := k) (x := x).
Qed.

Theorem hfs_mem_sequence_code_list_iff : forall p xs,
  hfs_mem p (hfs_sequence_code_list xs) <->
  exists i x,
    nth_error xs i = Some x /\
    p = hfs_index_pair (N.of_nat i) x.
Proof.
  intros p xs. unfold hfs_sequence_code_list.
  rewrite hfs_mem_sequence_code_from_iff,
    hfs_sequence_entry_from_nth_error.
  setoid_rewrite Nat.add_0_l. reflexivity.
Qed.

Corollary hfs_mem_sequence_index_iff : forall xs i x,
  hfs_mem (hfs_index_pair (N.of_nat i) x)
    (hfs_sequence_code_list xs) <->
  nth_error xs i = Some x.
Proof.
  intros xs i x. rewrite hfs_mem_sequence_code_list_iff. split.
  - intros [j [y [Hnth Heq]]].
    apply hfs_index_pair_injective in Heq. destruct Heq as [Hij Hxy].
    apply Nat2N.inj in Hij. subst. now subst.
  - intro Hnth. exists i, x. now split.
Qed.

Lemma hfs_insert_comm : forall x y s,
  hfs_insert x (hfs_insert y s) =
  hfs_insert y (hfs_insert x s).
Proof.
  intros x y s. apply hfs_extensionality. intro p.
  rewrite !hfs_mem_insert_iff. tauto.
Qed.

Lemma hfs_remove_insert_fresh : forall x s,
  ~ hfs_mem x s -> hfs_remove x (hfs_insert x s) = s.
Proof.
  intros x s Hfresh. apply hfs_extensionality. intro p.
  rewrite hfs_mem_remove_iff, hfs_mem_insert_iff. split.
  - intros [[-> | Hp] Hneq]; [contradiction|exact Hp].
  - intro Hp. split; [now right|].
    intro Heq. subst p. contradiction.
Qed.

Lemma hfs_sequence_start_fresh : forall start xs x,
  ~ hfs_mem (hfs_index_pair (N.of_nat start) x)
      (hfs_sequence_code_from (S start) xs).
Proof.
  intros start xs x Hmem.
  apply hfs_mem_sequence_code_from_iff,
    hfs_sequence_entry_from_nth_error in Hmem.
  destruct Hmem as [k [y [_ Heq]]].
  apply hfs_index_pair_injective in Heq. destruct Heq as [Hindex _].
  apply Nat2N.inj in Hindex. lia.
Qed.

Theorem hfs_sequence_code_from_injective : forall start xs ys,
  hfs_sequence_code_from start xs = hfs_sequence_code_from start ys ->
  xs = ys.
Proof.
  intros start xs. revert start.
  induction xs as [|x xs IH]; intros start [|y ys] Heq; simpl in Heq.
  - reflexivity.
  - exfalso.
    assert (Hmem : hfs_mem (hfs_index_pair (N.of_nat start) y)
        hfs_empty).
    { rewrite Heq. apply hfs_mem_insert_self. }
    exact (hfs_not_mem_empty Hmem).
  - exfalso.
    assert (Hmem : hfs_mem (hfs_index_pair (N.of_nat start) x)
        hfs_empty).
    { rewrite <- Heq. apply hfs_mem_insert_self. }
    exact (hfs_not_mem_empty Hmem).
  - assert (Hhead : x = y).
    { assert (Hmem : hfs_mem (hfs_index_pair (N.of_nat start) x)
          (hfs_insert (hfs_index_pair (N.of_nat start) y)
             (hfs_sequence_code_from (S start) ys))).
      { rewrite <- Heq. apply hfs_mem_insert_self. }
      apply hfs_mem_insert_iff in Hmem. destruct Hmem as [Hpair | Htail].
      - now apply hfs_index_pair_injective in Hpair.
      - exfalso. exact (@hfs_sequence_start_fresh start ys x Htail). }
    subst y. f_equal. apply IH with (start := S start).
    apply (f_equal (hfs_remove (hfs_index_pair (N.of_nat start) x)))
      in Heq.
    rewrite !hfs_remove_insert_fresh in Heq;
      [exact Heq|apply hfs_sequence_start_fresh|apply hfs_sequence_start_fresh].
Qed.

Corollary hfs_sequence_code_list_injective : forall xs ys,
  hfs_sequence_code_list xs = hfs_sequence_code_list ys -> xs = ys.
Proof. intros. now apply hfs_sequence_code_from_injective in H. Qed.

(** Raw recognition and functional graphs. *)

Definition hfs_is_sequence (s : hfs_code) : Prop :=
  exists xs, s = hfs_sequence_code_list xs.

Definition hfs_sequence_length_graph (s : hfs_code) (n : nat) : Prop :=
  exists xs, s = hfs_sequence_code_list xs /\ n = length xs.

Definition hfs_sequence_nth_graph
    (s : hfs_code) (i : nat) (x : hfs_code) : Prop :=
  exists xs, s = hfs_sequence_code_list xs /\ nth_error xs i = Some x.

Lemma hfs_sequence_values_unique : forall s xs ys,
  s = hfs_sequence_code_list xs ->
  s = hfs_sequence_code_list ys -> xs = ys.
Proof.
  intros s xs ys Hx Hy. apply hfs_sequence_code_list_injective.
  now rewrite <- Hx, <- Hy.
Qed.

Lemma hfs_sequence_length_graph_functional : forall s n m,
  hfs_sequence_length_graph s n ->
  hfs_sequence_length_graph s m -> n = m.
Proof.
  intros s n m [xs [Hs ->]] [ys [Ht ->]].
  f_equal. eapply hfs_sequence_values_unique; eassumption.
Qed.

Lemma hfs_sequence_nth_graph_functional : forall s i x y,
  hfs_sequence_nth_graph s i x ->
  hfs_sequence_nth_graph s i y -> x = y.
Proof.
  intros s i x y [xs [Hs Hx]] [ys [Ht Hy]].
  assert (Hxy : xs = ys) by
    (eapply hfs_sequence_values_unique; eassumption).
  subst ys. rewrite Hx in Hy. now inversion Hy.
Qed.

(** * Computational sequence interface *)

Record hfs_sequence : Type := hfs_sequence_of_list {
  hfs_sequence_values : list hfs_code
}.

Definition hfs_sequence_code (s : hfs_sequence) : hfs_code :=
  hfs_sequence_code_list (hfs_sequence_values s).

Definition hfs_sequence_length (s : hfs_sequence) : nat :=
  length (hfs_sequence_values s).

Definition hfs_sequence_nth (s : hfs_sequence) (i : nat)
    : option hfs_code :=
  nth_error (hfs_sequence_values s) i.

Definition hfs_sequence_znth (s : hfs_sequence) (i : nat) : hfs_code :=
  nth i (hfs_sequence_values s) hfs_empty.

Definition hfs_sequence_empty : hfs_sequence :=
  hfs_sequence_of_list [].

Definition hfs_sequence_cons (s : hfs_sequence) (x : hfs_code)
    : hfs_sequence :=
  hfs_sequence_of_list (hfs_sequence_values s ++ [x]).

Definition hfs_sequence_take (n : nat) (s : hfs_sequence) : hfs_sequence :=
  hfs_sequence_of_list (firstn n (hfs_sequence_values s)).

Lemma hfs_sequence_eq : forall s t,
  hfs_sequence_values s = hfs_sequence_values t -> s = t.
Proof. intros [xs] [ys]. simpl. now intros ->. Qed.

Lemma hfs_sequence_code_injective : forall s t,
  hfs_sequence_code s = hfs_sequence_code t -> s = t.
Proof.
  intros [xs] [ys] H. apply hfs_sequence_eq. simpl in *.
  now apply hfs_sequence_code_list_injective.
Qed.

Lemma hfs_sequence_code_recognized : forall s,
  hfs_is_sequence (hfs_sequence_code s).
Proof. intros [xs]. exists xs. reflexivity. Qed.

Lemma hfs_sequence_length_spec : forall s,
  hfs_sequence_length_graph (hfs_sequence_code s)
    (hfs_sequence_length s).
Proof. intros [xs]. exists xs. now split. Qed.

Lemma hfs_sequence_nth_spec : forall s i x,
  hfs_sequence_nth s i = Some x ->
  hfs_sequence_nth_graph (hfs_sequence_code s) i x.
Proof. intros [xs] i x H. exists xs. now split. Qed.

Lemma hfs_sequence_znth_in_range : forall s i x,
  hfs_sequence_nth s i = Some x -> hfs_sequence_znth s i = x.
Proof.
  intros [xs] i x H. unfold hfs_sequence_nth, hfs_sequence_znth in *.
  revert i H. induction xs as [|y ys IH]; intros [|i] H; simpl in *;
    try discriminate.
  - now inversion H.
  - now apply IH.
Qed.

Lemma hfs_sequence_znth_out_of_range : forall s i,
  hfs_sequence_length s <= i ->
  hfs_sequence_znth s i = hfs_empty.
Proof.
  intros [xs] i H. unfold hfs_sequence_length, hfs_sequence_znth in *.
  apply nth_overflow. exact H.
Qed.

Lemma hfs_sequence_empty_code :
  hfs_sequence_code hfs_sequence_empty = hfs_empty.
Proof. reflexivity. Qed.

Lemma hfs_sequence_empty_length :
  hfs_sequence_length hfs_sequence_empty = 0.
Proof. reflexivity. Qed.

Lemma hfs_sequence_length_zero_iff : forall s,
  hfs_sequence_length s = 0 <-> s = hfs_sequence_empty.
Proof.
  intros [xs]. unfold hfs_sequence_length. simpl. split.
  - intro H. apply length_zero_iff_nil in H. subst. reflexivity.
  - intro H. inversion H. reflexivity.
Qed.

Lemma hfs_sequence_code_from_snoc : forall start xs x,
  hfs_sequence_code_from start (xs ++ [x]) =
  hfs_insert
    (hfs_index_pair (N.of_nat (start + length xs)) x)
    (hfs_sequence_code_from start xs).
Proof.
  intros start xs. revert start.
  induction xs as [|y ys IH]; intros start x; simpl.
  - replace (start + 0) with start by lia. reflexivity.
  - rewrite IH. replace (start + S (length ys))
      with (S start + length ys) by lia.
    apply hfs_insert_comm.
Qed.

Theorem hfs_sequence_cons_code : forall s x,
  hfs_sequence_code (hfs_sequence_cons s x) =
  hfs_insert
    (hfs_index_pair (N.of_nat (hfs_sequence_length s)) x)
    (hfs_sequence_code s).
Proof.
  intros [xs] x. unfold hfs_sequence_code, hfs_sequence_cons,
    hfs_sequence_length, hfs_sequence_code_list. simpl.
  rewrite hfs_sequence_code_from_snoc. reflexivity.
Qed.

Corollary hfs_mem_sequence_cons_code_iff : forall s x p,
  hfs_mem p (hfs_sequence_code (hfs_sequence_cons s x)) <->
  p = hfs_index_pair (N.of_nat (hfs_sequence_length s)) x \/
  hfs_mem p (hfs_sequence_code s).
Proof.
  intros s x p. rewrite hfs_sequence_cons_code,
    hfs_mem_insert_iff. reflexivity.
Qed.

Lemma hfs_sequence_cons_length : forall s x,
  hfs_sequence_length (hfs_sequence_cons s x) =
  S (hfs_sequence_length s).
Proof. intros [xs] x. unfold hfs_sequence_length, hfs_sequence_cons. simpl.
  rewrite length_app. simpl. lia.
Qed.

Lemma hfs_sequence_cons_nth_old : forall s x i,
  i < hfs_sequence_length s ->
  hfs_sequence_nth (hfs_sequence_cons s x) i =
  hfs_sequence_nth s i.
Proof.
  intros [xs] x i Hi. unfold hfs_sequence_nth, hfs_sequence_cons,
    hfs_sequence_length in *. simpl in *. now rewrite nth_error_app1.
Qed.

Lemma hfs_sequence_cons_nth_last : forall s x,
  hfs_sequence_nth (hfs_sequence_cons s x)
    (hfs_sequence_length s) = Some x.
Proof.
  intros [xs] x. unfold hfs_sequence_nth, hfs_sequence_cons,
    hfs_sequence_length. simpl. rewrite nth_error_app2 by lia.
  replace (length xs - length xs) with 0 by lia. reflexivity.
Qed.

Lemma hfs_sequence_cons_code_subset : forall s x,
  hfs_subset (hfs_sequence_code s)
    (hfs_sequence_code (hfs_sequence_cons s x)).
Proof.
  intros s x p Hp. rewrite hfs_sequence_cons_code,
    hfs_mem_insert_iff. now right.
Qed.

Lemma hfs_sequence_cons_code_strict : forall s x,
  hfs_sequence_code (hfs_sequence_cons s x) <>
  hfs_sequence_code s.
Proof.
  intros s x Heq.
  assert (Hmem : hfs_mem
      (hfs_index_pair (N.of_nat (hfs_sequence_length s)) x)
      (hfs_sequence_code s)).
  { rewrite <- Heq, hfs_sequence_cons_code. apply hfs_mem_insert_self. }
  unfold hfs_sequence_code in Hmem.
  rewrite hfs_mem_sequence_index_iff in Hmem.
  assert (Hnone : nth_error (hfs_sequence_values s)
      (hfs_sequence_length s) = None).
  { apply (proj2 (@nth_error_None hfs_code (hfs_sequence_values s)
      (hfs_sequence_length s))). unfold hfs_sequence_length. lia. }
  rewrite Hmem in Hnone. discriminate.
Qed.

Theorem hfs_sequence_extensionality : forall s t,
  (forall i, hfs_sequence_nth s i = hfs_sequence_nth t i) -> s = t.
Proof.
  intros [xs] [ys] H. apply hfs_sequence_eq. simpl in *.
  apply nth_error_ext. exact H.
Qed.

Theorem hfs_sequence_eq_of_length_and_code_subset : forall s t,
  hfs_sequence_length s = hfs_sequence_length t ->
  hfs_subset (hfs_sequence_code s) (hfs_sequence_code t) ->
  s = t.
Proof.
  intros s t Hlength Hsubset. apply hfs_sequence_extensionality. intro i.
  destruct (hfs_sequence_nth s i) as [x |] eqn:Hs.
  - assert (Hmem : hfs_mem
        (hfs_index_pair (N.of_nat i) x) (hfs_sequence_code s)).
    { unfold hfs_sequence_code. rewrite hfs_mem_sequence_index_iff.
      exact Hs. }
    specialize (Hsubset _ Hmem). unfold hfs_sequence_code in Hsubset.
    rewrite hfs_mem_sequence_index_iff in Hsubset.
    change (Some x = hfs_sequence_nth t i).
    unfold hfs_sequence_nth in Hsubset. now symmetry.
  - assert (Hsi : hfs_sequence_length s <= i).
    { apply (proj1 (@nth_error_None hfs_code (hfs_sequence_values s) i)).
      exact Hs. }
    assert (Hti : hfs_sequence_nth t i = None).
    { apply (proj2 (@nth_error_None hfs_code (hfs_sequence_values t) i)).
      unfold hfs_sequence_length in *. lia. }
    change (None = hfs_sequence_nth t i). now symmetry.
Qed.

Lemma hfs_sequence_cons_injective : forall s t x y,
  hfs_sequence_cons s x = hfs_sequence_cons t y <-> s = t /\ x = y.
Proof.
  intros [xs] [ys] x y. split.
  - intro H. inversion H. simpl in H1.
    apply app_inj_tail in H1. destruct H1 as [-> ->]. now split.
  - now intros [-> ->].
Qed.

Lemma hfs_sequence_cases : forall s,
  s = hfs_sequence_empty \/
  exists t x, s = hfs_sequence_cons t x.
Proof.
  intros [xs]. induction xs using rev_ind.
  - now left.
  - right. exists (hfs_sequence_of_list xs), x. reflexivity.
Qed.

Theorem hfs_sequence_induction : forall (P : hfs_sequence -> Prop),
  P hfs_sequence_empty ->
  (forall s x, P s -> P (hfs_sequence_cons s x)) ->
  forall s, P s.
Proof.
  intros P Hnil Hsnoc [xs]. induction xs using rev_ind.
  - exact Hnil.
  - change (P (hfs_sequence_cons (hfs_sequence_of_list xs) x)).
    now apply Hsnoc.
Qed.

Lemma hfs_sequence_take_length : forall n s,
  hfs_sequence_length (hfs_sequence_take n s) =
  Nat.min n (hfs_sequence_length s).
Proof.
  intros n [xs]. unfold hfs_sequence_length, hfs_sequence_take. simpl.
  apply length_firstn.
Qed.

Corollary hfs_sequence_take_length_bounded : forall n s,
  n <= hfs_sequence_length s ->
  hfs_sequence_length (hfs_sequence_take n s) = n.
Proof.
  intros n s H. rewrite hfs_sequence_take_length. now apply Nat.min_l.
Qed.

Lemma hfs_sequence_take_nth : forall n s i,
  i < n ->
  hfs_sequence_nth (hfs_sequence_take n s) i =
  hfs_sequence_nth s i.
Proof.
  intros n [xs] i Hi. unfold hfs_sequence_nth, hfs_sequence_take. simpl.
  rewrite nth_error_firstn. destruct (i <? n) eqn:Hlt.
  - reflexivity.
  - apply Nat.ltb_ge in Hlt. lia.
Qed.

Lemma hfs_sequence_take_code_subset : forall n s,
  hfs_subset (hfs_sequence_code (hfs_sequence_take n s))
    (hfs_sequence_code s).
Proof.
  intros n [xs] p Hp. unfold hfs_sequence_code, hfs_sequence_take in *.
  simpl in *. rewrite hfs_mem_sequence_code_list_iff in Hp.
  destruct Hp as [i [x [Hnth ->]]].
  rewrite hfs_mem_sequence_index_iff.
  rewrite nth_error_firstn in Hnth.
  destruct (i <? n) eqn:Hlt; [exact Hnth|discriminate].
Qed.

Lemma hfs_sequence_take_full : forall s,
  hfs_sequence_take (hfs_sequence_length s) s = s.
Proof.
  intros [xs]. apply hfs_sequence_eq. simpl.
  unfold hfs_sequence_length. simpl. apply firstn_all.
Qed.

(** Small literal sequences. *)

Definition hfs_sequence_singleton (x : hfs_code) : hfs_sequence :=
  hfs_sequence_cons hfs_sequence_empty x.

Definition hfs_sequence_doubleton (x y : hfs_code) : hfs_sequence :=
  hfs_sequence_cons (hfs_sequence_singleton x) y.

Lemma hfs_sequence_singleton_length : forall x,
  hfs_sequence_length (hfs_sequence_singleton x) = 1.
Proof. reflexivity. Qed.

Lemma hfs_sequence_doubleton_length : forall x y,
  hfs_sequence_length (hfs_sequence_doubleton x y) = 2.
Proof. reflexivity. Qed.

Lemma hfs_sequence_singleton_nth : forall x,
  hfs_sequence_nth (hfs_sequence_singleton x) 0 = Some x.
Proof. reflexivity. Qed.

(** * Finite vectors *)

Definition hfs_vector_to_sequence {n : nat} (v : Fin.t n -> hfs_code)
    : hfs_sequence :=
  hfs_sequence_of_list (map v (vorspiel_fin_enum n)).

Lemma vorspiel_fin_enum_nth_error : forall n (i : Fin.t n),
  nth_error (vorspiel_fin_enum n) (vorspiel_fin_value i) = Some i.
Proof.
  induction n as [|n IH]; intro i; [inversion i|].
  refine (@Fin.caseS' n i
    (fun j => nth_error (vorspiel_fin_enum (S n))
      (vorspiel_fin_value j) = Some j) _ _).
  - reflexivity.
  - intro j. rewrite fin_value_FS. simpl.
    apply map_nth_error. apply IH.
Qed.

Lemma hfs_vector_to_sequence_length : forall n (v : Fin.t n -> hfs_code),
  hfs_sequence_length (hfs_vector_to_sequence v) = n.
Proof.
  intros n v. unfold hfs_sequence_length, hfs_vector_to_sequence. simpl.
  now rewrite length_map, vorspiel_fin_enum_length.
Qed.

Lemma hfs_vector_to_sequence_nth : forall n (v : Fin.t n -> hfs_code)
    (i : Fin.t n),
  hfs_sequence_nth (hfs_vector_to_sequence v) (vorspiel_fin_value i) =
  Some (v i).
Proof.
  intros n v i. unfold hfs_sequence_nth, hfs_vector_to_sequence. simpl.
  rewrite nth_error_map, vorspiel_fin_enum_nth_error. reflexivity.
Qed.

Corollary hfs_vector_to_sequence_mem : forall n
    (v : Fin.t n -> hfs_code) (i : Fin.t n),
  hfs_mem
    (hfs_index_pair (N.of_nat (vorspiel_fin_value i)) (v i))
    (hfs_sequence_code (hfs_vector_to_sequence v)).
Proof.
  intros n v i. unfold hfs_sequence_code.
  rewrite hfs_mem_sequence_index_iff.
  apply hfs_vector_to_sequence_nth.
Qed.
