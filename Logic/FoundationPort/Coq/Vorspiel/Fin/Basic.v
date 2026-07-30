(** Finite ordinals: enumeration, decomposition, casts, and cardinal bounds. *)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List
  Logic.FunctionalExtensionality Vectors.Fin.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Definition vorspiel_fin_value {n} (i : Fin.t n) : nat :=
  proj1_sig (Fin.to_nat i).

Definition vorspiel_fin_zero {A} (i : Fin.t 0) : A :=
  match i with end.

Lemma fin_zero_eta : forall A (f : Fin.t 0 -> A),
  f = vorspiel_fin_zero.
Proof.
  intros A f. apply functional_extensionality. intro i. inversion i.
Qed.

Lemma nat_sub_one_lt_nonzero : forall n,
  n <> 0 -> n - 1 < n.
Proof. intros n Hn. lia. Qed.

Fixpoint vorspiel_fin_enum (n : nat) : list (Fin.t n) :=
  match n with
  | 0 => []
  | S k => Fin.F1 :: map Fin.FS (vorspiel_fin_enum k)
  end.

Lemma vorspiel_fin_enum_complete : forall n (i : Fin.t n),
  In i (vorspiel_fin_enum n).
Proof.
  induction n as [|n IH]; intro i; [inversion i |].
  refine (@Fin.caseS' n i
    (fun j => In j (vorspiel_fin_enum (S n))) _ _).
  - simpl. now left.
  - intro j. simpl. right. apply in_map. apply IH.
Qed.

Lemma list_map_nodup_of_injective : forall A B (f : A -> B) xs,
  (forall x y, f x = f y -> x = y) ->
  NoDup xs -> NoDup (map f xs).
Proof.
  intros A B f xs Hinj Hnodup. induction Hnodup as [|x xs Hx Hxs IH].
  - constructor.
  - simpl. constructor.
    + intro Hmem. apply in_map_iff in Hmem.
      destruct Hmem as [y [Hfy Hy]]. apply Hx.
      apply Hinj in Hfy. now subst.
    + exact IH.
Qed.

Lemma vorspiel_fin_enum_nodup : forall n,
  NoDup (vorspiel_fin_enum n).
Proof.
  induction n as [|n IH]; simpl; [constructor |]. constructor.
  - intro Hmem. apply in_map_iff in Hmem.
    destruct Hmem as [i [Hi _]]. discriminate.
  - apply list_map_nodup_of_injective.
    + intros x y Hxy. now apply Fin.FS_inj.
    + exact IH.
Qed.

Lemma vorspiel_fin_enum_length : forall n,
  length (vorspiel_fin_enum n) = n.
Proof.
  induction n; simpl; [reflexivity | now rewrite length_map, IHn].
Qed.

Record fin_embedding (n m : nat) := {
  fin_embedding_fun : Fin.t n -> Fin.t m;
  fin_embedding_injective : forall x y,
    fin_embedding_fun x = fin_embedding_fun y -> x = y
}.

Theorem no_fin_embedding_to_smaller : forall n m,
  m < n -> fin_embedding n m -> False.
Proof.
  intros n m Hmn [f Hinj].
  pose proof (list_map_nodup_of_injective
    (f := f) (xs := vorspiel_fin_enum n) Hinj
    (vorspiel_fin_enum_nodup n)) as Hnodup.
  assert (Hincl : incl (map f (vorspiel_fin_enum n))
    (vorspiel_fin_enum m)).
  { intros x Hx. apply vorspiel_fin_enum_complete. }
  pose proof (NoDup_incl_length Hnodup Hincl) as Hlen.
  rewrite length_map, !vorspiel_fin_enum_length in Hlen. lia.
Qed.

Definition vorspiel_fin_last (n : nat) : Fin.t (S n) :=
  Fin.of_nat_lt (Nat.lt_succ_diag_r n).

Lemma vorspiel_fin_last_value : forall n,
  vorspiel_fin_value (vorspiel_fin_last n) = n.
Proof.
  intro n. unfold vorspiel_fin_value, vorspiel_fin_last.
  now rewrite Fin.to_nat_of_nat.
Qed.

Lemma nat_lt_next_fin_last : forall n,
  n < vorspiel_fin_value (vorspiel_fin_last (S n)).
Proof. intro n. rewrite vorspiel_fin_last_value. lia. Qed.

Definition vorspiel_fin_last_nonzero (n : nat) (Hn : 0 < n) : Fin.t n.
Proof. refine (Fin.of_nat_lt (p := n - 1) _). lia. Defined.

Lemma vorspiel_fin_last_nonzero_value : forall n Hn,
  vorspiel_fin_value (@vorspiel_fin_last_nonzero n Hn) = n - 1.
Proof.
  intros n Hn. unfold vorspiel_fin_value, vorspiel_fin_last_nonzero.
  now rewrite Fin.to_nat_of_nat.
Qed.

Lemma vorspiel_fin_le_last_nonzero : forall n Hn (i : Fin.t n),
  vorspiel_fin_value i <=
    vorspiel_fin_value (@vorspiel_fin_last_nonzero n Hn).
Proof.
  intros n Hn i. rewrite vorspiel_fin_last_nonzero_value.
  unfold vorspiel_fin_value. pose proof (proj2_sig (Fin.to_nat i)) as Hi.
  destruct n as [|n]; [inversion i |]. simpl. lia.
Qed.

Lemma vorspiel_fin_positive_of_value_nonzero : forall n (i : Fin.t n),
  vorspiel_fin_value i <> 0 -> 0 < vorspiel_fin_value i.
Proof. intros n i Hi. lia. Qed.

Lemma vorspiel_fin_of_nat_positive : forall x n (H : x < n),
  x <> 0 -> 0 < vorspiel_fin_value (Fin.of_nat_lt H).
Proof.
  intros x n H Hx. unfold vorspiel_fin_value.
  rewrite Fin.to_nat_of_nat. destruct x; [contradiction | apply Nat.lt_0_succ].
Qed.

Lemma fin_forall_succ_iff : forall k (P : Fin.t (S k) -> Prop),
  (forall i, P i) <->
  P Fin.F1 /\ forall i : Fin.t k, P (Fin.FS i).
Proof.
  intros k P. split.
  - intro H. split; [apply H | intro i; apply H].
  - intros [Hzero Hsucc] i.
    refine (@Fin.caseS' k i P Hzero Hsucc).
Qed.

Lemma fin_exists_succ_iff : forall k (P : Fin.t (S k) -> Prop),
  (exists i, P i) <->
  P Fin.F1 \/ exists i : Fin.t k, P (Fin.FS i).
Proof.
  intros k P. split.
  - intros [i Hi].
    refine (@Fin.caseS' k i (fun j => P j ->
      P Fin.F1 \/ exists u, P (Fin.FS u)) _ _ Hi).
    + now left.
    + intros j Hj. right. now exists j.
  - intros [Hzero | [i Hi]].
    + now exists Fin.F1.
    + now exists (Fin.FS i).
Qed.

Definition fin_add_cast (m n : nat) (i : Fin.t n) : Fin.t (m + n) :=
  Fin.of_nat_lt (@Nat.lt_le_trans _ n (m + n)
    (proj2_sig (Fin.to_nat i)) (Nat.le_add_l n m)).

Lemma fin_add_cast_value : forall m n (i : Fin.t n),
  vorspiel_fin_value (fin_add_cast m i) = vorspiel_fin_value i.
Proof.
  intros m n i. unfold vorspiel_fin_value, fin_add_cast.
  now rewrite Fin.to_nat_of_nat.
Qed.

Lemma fin_one_eq_zero : forall i : Fin.t 1,
  vorspiel_fin_value i = 0.
Proof.
  intros i. unfold vorspiel_fin_value.
  apply (proj1 (Nat.lt_1_r _)). exact (proj2_sig (Fin.to_nat i)).
Qed.

Lemma fin_one_not_positive : forall i : Fin.t 1,
  ~ 0 < vorspiel_fin_value i.
Proof. intro i. rewrite fin_one_eq_zero. lia. Qed.
