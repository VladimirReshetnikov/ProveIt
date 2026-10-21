(** k225-formal/rocqperm/BisimMirror.v (SHA256 443d5b1a3bb179100660b68f9bddf40530de5a6113e30ac9e6ea209ab829283f) under namespace K215F. *)
(** One forward zero-offset certificate proves equivalence in the existing
    plain K230P checker.  K215's certificate needs no register offsets. *)
From Coq Require Import List Bool Arith NArith.
From K230 Require Import RM.
From K230P Require Import Bisim230.
Import ListNotations.

Definition flip_plain (x : entry) : entry :=
  let '(a,b,j,k) := x in (b,a,j,k).

Lemma cnt_eq_mirror l1 l2 : cnt_eq l1 l2 = true -> cnt_eq l2 l1 = true.
Proof.
  intros H. unfold cnt_eq. apply forallb_forall. intros i _.
  apply Nat.eqb_eq. symmetry. now apply cnt_eq_ok.
Qed.

Lemma getc_mirror C j : getc (mirror C) j =
  match getc C j with Some (a,b) => Some (b,a) | None => None end.
Proof.
  unfold getc, mirror, entry in *. rewrite nth_error_map.
  destruct (nth_error C (N.to_nat j)) as [[[[a b] k] l]|]; reflexivity.
Qed.

Lemma branch_ok_mirror t1 t2 C A B j : branch_ok t1 t2 C A B j = true ->
  branch_ok t2 t1 (mirror C) B A j = true.
Proof.
  unfold branch_ok. rewrite getc_mirror.
  destruct (seg t1 seg_fuel A) as [[l1 P1]|]; [|discriminate].
  destruct (seg t2 seg_fuel B) as [[l2 P2]|]; [|discriminate].
  destruct (getc C j) as [[Q1 Q2]|]; [|discriminate].
  repeat rewrite andb_true_iff. intros [[Hc H1] H2].
  split; [split|]; try assumption. apply cnt_eq_mirror. exact Hc.
Qed.

Lemma entry_ok_mirror t1 t2 C x : entry_ok t1 t2 C x = true ->
  entry_ok t2 t1 (mirror C) (flip_plain x) = true.
Proof.
  destruct x as [[[P1 P2] j] k]. unfold entry_ok, flip_plain.
  destruct (tsite t1 P1) as [[e1 Q1]|]; [|discriminate].
  destruct (tsite t2 P2) as [[e2 Q2]|]; [|destruct e1; discriminate].
  destruct e1; try discriminate; destruct e2; try discriminate.
  - repeat rewrite andb_true_iff. intros [[Hr Hj] Hk].
    apply Nat.eqb_eq in Hr. subst. repeat split.
    + apply Nat.eqb_refl.
    + apply branch_ok_mirror. exact Hj.
    + apply branch_ok_mirror. exact Hk.
  - reflexivity.
Qed.

Theorem check_mirror t1 t2 C : check t1 t2 C = true ->
  check t2 t1 (mirror C) = true.
Proof.
  unfold check. rewrite !andb_true_iff. intros [Hb He]. split.
  - exact (branch_ok_mirror t1 t2 C [] [] 0 Hb).
  - unfold mirror. rewrite forallb_forall. rewrite forallb_forall in He.
    intros y Hy. apply in_map_iff in Hy as [x [<- Hx]].
    exact (entry_ok_mirror t1 t2 C x (He x Hx)).
Qed.

Theorem check_one_sided_iff p1 p2 C : check (ptree p1) (ptree p2) C = true ->
  forall R, rm_halts p1 ([],R) <-> rm_halts p2 ([],R).
Proof.
  intros H R. apply (check_iff p1 p2 C H). now apply check_mirror.
Qed.

Print Assumptions check_mirror.
Print Assumptions check_one_sided_iff.
