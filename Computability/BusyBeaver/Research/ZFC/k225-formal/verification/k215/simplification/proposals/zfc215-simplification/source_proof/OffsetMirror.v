(** A single forward certificate suffices for the existing Rocq checker.
    This proves a new generic checker theorem without changing the checker. *)
From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia NArith ZArith.
From K230 Require Import RM.
From K230P Require Import Bisim230.
From K215F Require Import OffsetBisim230.
Import ListNotations.

Definition flip_entry (x : oentry) : oentry :=
  let '(a,b,z,j,k) := x in (b,a,(-z)%Z,j,k).

Lemma delta_neg z i : delta (-z) i = (- delta z i)%Z.
Proof. unfold delta. destruct (Nat.eqb i 5); reflexivity. Qed.

Lemma counts_ok_mirror z z' l1 l2 : counts_ok z z' l1 l2 = true ->
  counts_ok (-z) (-z') l2 l1 = true.
Proof.
  intros H. unfold counts_ok. apply forallb_forall. intros i _.
  apply Z.eqb_eq. rewrite !delta_neg.
  pose proof (counts_ok_sound _ _ _ _ H i). lia.
Qed.

Lemma ogetc_mirror C j : ogetc (omirror C) j =
  match ogetc C j with
  | Some (a,b,z) => Some (b,a,(-z)%Z)
  | None => None
  end.
Proof.
  unfold ogetc, omirror, oentry in *. rewrite nth_error_map.
  destruct (nth_error C (N.to_nat j)) as [[[[[a b] z] k] l]|] eqn:E;
    reflexivity.
Qed.

Lemma obranch_ok_mirror t1 t2 C A B z j :
  obranch_ok t1 t2 C A B z j = true ->
  obranch_ok t2 t1 (omirror C) B A (-z) j = true.
Proof.
  unfold obranch_ok. rewrite ogetc_mirror.
  destruct (seg t1 seg_fuel A) as [[l1 P1]|]; [|discriminate].
  destruct (seg t2 seg_fuel B) as [[l2 P2]|]; [|discriminate].
  destruct (ogetc C j) as [[[Q1 Q2] z']|]; [|discriminate].
  repeat rewrite andb_true_iff. intros [[Hc H1] H2].
  split; [split|]; try assumption. apply counts_ok_mirror. exact Hc.
Qed.

Lemma oentry_ok_mirror t1 t2 C x :
  oentry_ok t1 t2 C x = true ->
  oentry_ok t2 t1 (omirror C) (flip_entry x) = true.
Proof.
  destruct x as [[[[P1 P2] z] j] k]. unfold oentry_ok, flip_entry.
  destruct (tsite t1 P1) as [[e1 Q1]|]; [|discriminate].
  destruct (tsite t2 P2) as [[e2 Q2]|]; [|destruct e1; discriminate].
  destruct e1; try discriminate; destruct e2; try discriminate.
  - repeat rewrite andb_true_iff. intros [[[Hr Hz] Hj] Hk].
    apply Nat.eqb_eq in Hr. subst.
    repeat split.
    + apply Nat.eqb_refl.
    + apply Z.eqb_eq. rewrite delta_neg. apply Z.eqb_eq in Hz. lia.
    + apply obranch_ok_mirror. exact Hj.
    + apply obranch_ok_mirror. exact Hk.
  - reflexivity.
Qed.

Theorem ocheck_mirror t1 t2 C : ocheck t1 t2 C = true ->
  ocheck t2 t1 (omirror C) = true.
Proof.
  unfold ocheck. rewrite !andb_true_iff. intros [Hb He]. split.
  - exact (obranch_ok_mirror t1 t2 C [] [] 0 0 Hb).
  - unfold omirror. rewrite forallb_forall.
    rewrite forallb_forall in He. intros y Hy.
    apply in_map_iff in Hy as [x [<- Hx]].
    exact (oentry_ok_mirror t1 t2 C x (He x Hx)).
Qed.

Theorem ocheck_one_sided_iff p1 p2 C :
  ocheck (ptree p1) (ptree p2) C = true ->
  forall R, rm_halts p1 ([],R) <-> rm_halts p2 ([],R).
Proof.
  intros H R. apply (ocheck_iff p1 p2 C H).
  now apply ocheck_mirror.
Qed.

Print Assumptions ocheck_mirror.
Print Assumptions ocheck_one_sided_iff.
