(** Representation-independent normalized source certificates.
    Completion of the guarded-core / sharing-interfaces checked-lookup design.
    The terminating-run induction is adapted from current K215F.NormalizedBisim.
    Lookup need only return a locally checked row: no list-index or size law. *)
From Coq Require Import List Bool Arith Lia NArith.
From K230 Require Import RM RMEquiv.
From K230P Require Import Bisim230.
Require Import PathEq.
Import ListNotations.

Module LCheck.

Definition flip_plain (x : entry) : entry :=
  let '(a,b,j,k) := x in (b,a,j,k).

Definition flip_get (G : N -> option (list bool * list bool)) (j : N) :=
  match G j with Some (a,b) => Some (b,a) | None => None end.

Lemma cnt_eq_mirror l1 l2 : cnt_eq l1 l2 = true -> cnt_eq l2 l1 = true.
Proof.
  intros H. unfold cnt_eq. apply forallb_forall. intros i _.
  apply Nat.eqb_eq. symmetry. now apply cnt_eq_ok.
Qed.

Definition branch_ok (t1 t2 : tree) (G : N -> option (list bool * list bool))
    (A B : list bool) (j : N) : bool :=
  match seg t1 seg_fuel A, seg t2 seg_fuel B, G j with
  | Some (l1,P1), Some (l2,P2), Some (Q1,Q2) =>
      cnt_eq l1 l2 && ibeq P1 Q1 && ibeq P2 Q2
  | _,_,_ => false
  end.

Definition entry_ok (t1 t2 : tree) (G : N -> option (list bool * list bool)) (x : entry) : bool :=
  let '(P1,P2,j,k) := x in
  match tsite t1 P1, tsite t2 P2 with
  | Some (EHalt,_), Some (EHalt,_) => true
  | Some (EDecnz r1,Q1), Some (EDecnz r2,Q2) =>
      Nat.eqb r1 r2 &&
      branch_ok t1 t2 G (inc_path Q1) (inc_path Q2) j &&
      branch_ok t1 t2 G (brk 1 Q1) (brk 1 Q2) k
  | _,_ => false
  end.

Definition validated (t1 t2 : tree) (G : N -> option (list bool * list bool)) : Prop :=
  forall j P1 P2, G j = Some (P1,P2) ->
    exists j' k', entry_ok t1 t2 G (P1,P2,j',k') = true.

Section Sound.
Variables p1 p2 : prog.
Variable G : N -> option (list bool * list bool).
Hypothesis HC : validated (ptree p1) (ptree p2) G.

Lemma branch_sim N A B j R1 R2
  (IH : forall N', N' < S N -> forall P1 P2 j' k' R1 R2,
    entry_ok (ptree p1) (ptree p2) G (P1,P2,j',k') = true -> (forall i, R1 i = R2 i) ->
    Bisim230.hn p1 N' (P1,R1) -> rm_halts p2 (P2,R2)) :
  branch_ok (ptree p1) (ptree p2) G A B j = true ->
  (forall i, R1 i = R2 i) ->
  Bisim230.hn p1 N (A,R1) -> rm_halts p2 (B,R2).
Proof.
  unfold branch_ok. intros Hb HR Hh.
  destruct (seg (ptree p1) seg_fuel A) as [[l1 Q1]|] eqn:E1; [|discriminate].
  destruct (seg (ptree p2) seg_fuel B) as [[l2 Q2]|] eqn:E2; [|discriminate].
  destruct (G j) as [[P1 P2]|] eqn:Eg; [|discriminate].
  apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [Hc H1].
  apply ibeq_ok in H1,H2. pose proof (cnt_eq_ok _ _ Hc) as Hc'.
  destruct (HC j P1 P2 Eg) as (j' & k' & Hin).
  destruct (seg_hn p1 _ _ _ _ R1 N E1 Hh) as (N' & R1' & Hle & Hh' & HR1).
  destruct (seg_run p2 _ _ _ _ R2 E2) as (n & R2' & Hr & HR2).
  apply (halts_pre p2 n _ _ Hr).
  apply (halts_ipeq p2 P2 Q2 R2' (ipeq_sym _ _ H2)).
  apply (IH N' ltac:(lia) P1 P2 j' k' R1' R2' Hin).
  - intros i. rewrite HR1,HR2,HR,Hc'. reflexivity.
  - exact (RMEquiv.hn_ipeq p1 N' Q1 P1 R1' H1 Hh').
Qed.

Lemma sim N : forall P1 P2 j k R1 R2,
  entry_ok (ptree p1) (ptree p2) G (P1,P2,j,k) = true -> (forall i, R1 i = R2 i) ->
  Bisim230.hn p1 N (P1,R1) -> rm_halts p2 (P2,R2).
Proof.
  induction N as [N IH] using lt_wf_ind. intros P1 P2 j k R1 R2 He HR Hh.
  cbn [entry_ok] in He.
  destruct (tsite (ptree p1) P1) as [[e1 Q1]|] eqn:T1; [|discriminate].
  destruct (tsite (ptree p2) P2) as [[e2 Q2]|] eqn:T2; [|destruct e1; discriminate].
  destruct e1; try discriminate; destruct e2; try discriminate.
  - apply andb_prop in He as [He Hk]. apply andb_prop in He as [Hr Hj].
    apply Nat.eqb_eq in Hr. subst.
    destruct N as [|N].
    { destruct Hh as (c & Hc & Ha). injection Hc as <-.
      apply at_halt_tsite in Ha as [Q Ha]. rewrite T1 in Ha. discriminate. }
    destruct (R1 r0) as [|v] eqn:Ev.
    + assert (Hs : lres (EDecnz r0) Q1 R1 = Some (brk 1 Q1,R1))
        by (cbn; rewrite Ev; reflexivity).
      destruct (hn_step p1 _ _ _ _ _ _ T1 ltac:(discriminate) Hs Hh)
        as (N' & E & Hh'). assert (N'=N) by congruence. subst N'.
      apply (halts_pre p2 1 _ (brk 1 Q2,R2)).
      { cbn [rm_run]. rewrite step_tsite,T2. cbn. rewrite <- HR,Ev. reflexivity. }
      exact (branch_sim N (brk 1 Q1) (brk 1 Q2) k R1 R2 IH Hk HR Hh').
    + assert (Hs : lres (EDecnz r0) Q1 R1 = Some (inc_path Q1,upd R1 r0 v))
        by (cbn; rewrite Ev; reflexivity).
      destruct (hn_step p1 _ _ _ _ _ _ T1 ltac:(discriminate) Hs Hh)
        as (N' & E & Hh'). assert (N'=N) by congruence. subst N'.
      apply (halts_pre p2 1 _ (inc_path Q2,upd R2 r0 v)).
      { cbn [rm_run]. rewrite step_tsite,T2. cbn. rewrite <- HR,Ev. reflexivity. }
      apply (branch_sim N (inc_path Q1) (inc_path Q2) j
        (upd R1 r0 v) (upd R2 r0 v) IH Hj); auto.
      intros i. unfold upd. rewrite HR. reflexivity.
  - exists 0,(P2,R2). split; [reflexivity|]. apply at_halt_tsite. eauto.
Qed.
End Sound.

Theorem initial_sound p1 p2 G :
  validated (ptree p1) (ptree p2) G ->
  branch_ok (ptree p1) (ptree p2) G [] [] 0 = true ->
  forall R, rm_halts p1 ([],R) -> rm_halts p2 ([],R).
Proof.
  intros HC Hb R (N & c & Hr & Ha).
  assert (IH : forall N', N' < S N -> forall P1 P2 j' k' R1 R2,
    entry_ok (ptree p1) (ptree p2) G (P1,P2,j',k') = true ->
    (forall i, R1 i = R2 i) ->
    Bisim230.hn p1 N' (P1,R1) -> rm_halts p2 (P2,R2))
    by (intros N' _; apply (sim p1 p2 G HC N')).
  apply (branch_sim p1 p2 G HC N [] [] 0 R R IH Hb); [reflexivity|].
  exists c. auto.
Qed.

Lemma branch_ok_mirror t1 t2 G A B j : branch_ok t1 t2 G A B j = true ->
  branch_ok t2 t1 (flip_get G) B A j = true.
Proof.
  unfold branch_ok, flip_get.
  destruct (seg t1 seg_fuel A) as [[l1 P1]|]; [|discriminate].
  destruct (seg t2 seg_fuel B) as [[l2 P2]|]; [|discriminate].
  destruct (G j) as [[Q1 Q2]|]; [|discriminate].
  repeat rewrite andb_true_iff. intros [[Hc H1] H2].
  split; [split|]; try assumption. apply cnt_eq_mirror. exact Hc.
Qed.

Lemma entry_ok_mirror t1 t2 G x : entry_ok t1 t2 G x = true ->
  entry_ok t2 t1 (flip_get G) (flip_plain x) = true.
Proof.
  destruct x as [[[P1 P2] j] k]. unfold entry_ok,flip_plain.
  destruct (tsite t1 P1) as [[e1 Q1]|]; [|discriminate].
  destruct (tsite t2 P2) as [[e2 Q2]|]; [|destruct e1; discriminate].
  destruct e1; try discriminate; destruct e2; try discriminate.
  - repeat rewrite andb_true_iff. intros [[Hr Hj] Hk].
    apply Nat.eqb_eq in Hr. subst.
    repeat split; [apply Nat.eqb_refl | apply branch_ok_mirror; assumption ..].
  - reflexivity.
Qed.

Lemma validated_mirror t1 t2 G : validated t1 t2 G ->
  validated t2 t1 (flip_get G).
Proof.
  intros HC j A B E. unfold flip_get in E.
  destruct (G j) as [[U V]|] eqn:Hg; [|discriminate].
  injection E as EA EB. subst A B.
  destruct (HC j U V Hg) as (j' & k' & He).
  exists j', k'. exact (entry_ok_mirror t1 t2 G (U,V,j',k') He).
Qed.

Theorem initial_halts_iff p1 p2 G :
  validated (ptree p1) (ptree p2) G ->
  branch_ok (ptree p1) (ptree p2) G [] [] 0 = true ->
  forall R, rm_halts p1 ([],R) <-> rm_halts p2 ([],R).
Proof.
  intros HC Hb R. split; [exact (initial_sound p1 p2 G HC Hb R)|].
  exact (initial_sound p2 p1 (flip_get G)
    (validated_mirror _ _ _ HC) (branch_ok_mirror _ _ _ _ _ _ Hb) R).
Qed.

Print Assumptions initial_halts_iff.
End LCheck.
