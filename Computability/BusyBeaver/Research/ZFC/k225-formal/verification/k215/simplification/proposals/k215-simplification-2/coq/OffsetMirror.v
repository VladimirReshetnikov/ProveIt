(** One certificate suffices: symmetry of the actual K215 Rocq checker. *)
From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia NArith ZArith.
From K230 Require Import RM.
From K230P Require Import Bisim230.
From K215F Require Import OffsetBisim230.
Import ListNotations.

Lemma delta_neg z i : delta (-z) i = (- delta z i)%Z.
Proof. unfold delta. destruct (Nat.eqb i 5); reflexivity. Qed.

Lemma counts_ok_mirror z z' l1 l2 :
  counts_ok z z' l1 l2 = true -> counts_ok (-z) (-z') l2 l1 = true.
Proof.
  intros H. unfold counts_ok. apply forallb_forall. intros i _.
  apply Z.eqb_eq. rewrite !delta_neg.
  pose proof (counts_ok_sound _ _ _ _ H i). lia.
Qed.

Lemma ogetc_mirror C j :
  ogetc (omirror C) j =
  option_map (fun '(a,b,z) => (b,a,(-z)%Z)) (ogetc C j).
Proof.
  unfold ogetc, omirror. generalize (N.to_nat j).
  induction C as [|[[[[a b] z] u] v] C IH]; intros n; destruct n; cbn; auto.
Qed.

Lemma obranch_ok_mirror t1 t2 C A B z j :
  obranch_ok t1 t2 C A B z j = true ->
  obranch_ok t2 t1 (omirror C) B A (-z) j = true.
Proof.
  unfold obranch_ok. rewrite ogetc_mirror.
  destruct (seg t1 seg_fuel A) as [[l1 P1]|]; [|discriminate].
  destruct (seg t2 seg_fuel B) as [[l2 P2]|]; [|discriminate].
  destruct (ogetc C j) as [[[Q1 Q2] z']|]; [|discriminate].
  cbn. intros H. apply andb_prop in H as [H H2]. apply andb_prop in H as [Hc H1].
  apply andb_true_intro. split; [|exact H1].
  apply andb_true_intro. split; [now apply counts_ok_mirror|exact H2].
Qed.

Definition flip_entry (x : oentry) : oentry :=
  let '(a,b,z,j,k) := x in (b,a,(-z)%Z,j,k).

Lemma oentry_ok_mirror t1 t2 C x :
  oentry_ok t1 t2 C x = true ->
  oentry_ok t2 t1 (omirror C) (flip_entry x) = true.
Proof.
  destruct x as [[[[P1 P2] z] j] k]. unfold flip_entry, oentry_ok.
  destruct (tsite t1 P1) as [[e1 Q1]|]; [|discriminate].
  destruct (tsite t2 P2) as [[e2 Q2]|]; [|destruct e1; discriminate].
  destruct e1; try discriminate; destruct e2; try discriminate.
  - intros H. apply andb_prop in H as [H Hk]. apply andb_prop in H as [H Hj].
    apply andb_prop in H as [Hr Hz]. apply Nat.eqb_eq in Hr. subst.
    apply andb_true_intro. split; [|now apply obranch_ok_mirror].
    apply andb_true_intro. split; [|now apply obranch_ok_mirror].
    apply andb_true_intro. split; [apply Nat.eqb_refl|].
    apply Z.eqb_eq. apply Z.eqb_eq in Hz. rewrite delta_neg, Hz. reflexivity.
  - intros _. reflexivity.
Qed.

Theorem ocheck_mirror t1 t2 C :
  ocheck t1 t2 C = true -> ocheck t2 t1 (omirror C) = true.
Proof.
  unfold ocheck. intros H. apply andb_prop in H as [Hstart Hall].
  apply andb_true_intro. split.
  - replace 0%Z with (-0)%Z by reflexivity. now apply obranch_ok_mirror.
  - apply forallb_forall. intros y Hy.
    unfold omirror in Hy. apply in_map_iff in Hy as [x [Hx Hin]].
    subst y. apply oentry_ok_mirror.
    apply forallb_forall with (x:=x) in Hall; assumption.
Qed.

Theorem ocheck_iff_of_forward p1 p2 C :
  ocheck (ptree p1) (ptree p2) C = true ->
  forall R, rm_halts p1 ([],R) <-> rm_halts p2 ([],R).
Proof.
  intros HC R. exact (ocheck_iff p1 p2 C HC (ocheck_mirror _ _ _ HC) R).
Qed.

Print Assumptions ocheck_mirror.
Print Assumptions ocheck_iff_of_forward.
