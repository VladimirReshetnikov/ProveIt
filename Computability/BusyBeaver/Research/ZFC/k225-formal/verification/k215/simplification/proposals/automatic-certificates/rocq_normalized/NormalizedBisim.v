(** Normalized source-certificate checking for Wade register programs.
    Derived from the pinned K230P.Bisim230 soundness proof.  Certificate
    pointers are compared modulo their implicit infinite false suffix.
    The program, segment executor, register semantics, and exact halting
    predicate are unchanged.  No register offset is used. *)
From Coq Require Import List Bool Arith Lia NArith.
From K230 Require Import RM RMEquiv.
From K230P Require Import Bisim230.
Require Import BisimMirror.
Import ListNotations.

Module NCheck.

Fixpoint allzero (P : list bool) : bool :=
  match P with [] => true | b :: Q => negb b && allzero Q end.

Lemma allzero_ok P : allzero P = true -> ipeq P [].
Proof.
  induction P as [|b P IH]; intro H; [apply ipeq_refl|].
  cbn [allzero] in H. apply andb_prop in H as [Hb HP].
  destruct b; [discriminate|]. intros [|i]; [reflexivity|].
  change (bit P i = false). rewrite <- (bit_nil i). exact (IH HP i).
Qed.

Fixpoint ibeq (P Q : list bool) : bool :=
  match P, Q with
  | [], _ => allzero Q
  | _, [] => allzero P
  | b :: P, c :: Q => Bool.eqb b c && ibeq P Q
  end.

Lemma ibeq_ok P Q : ibeq P Q = true -> ipeq P Q.
Proof.
  revert Q. induction P as [|b P IH]; intros [|c Q] H.
  - apply ipeq_refl.
  - apply ipeq_sym, allzero_ok. exact H.
  - apply allzero_ok. exact H.
  - cbn [ibeq] in H. apply andb_prop in H as [Hbc HPQ].
    apply Bool.eqb_prop in Hbc. subst c.
    intros [|i]; [reflexivity|]. exact (IH Q HPQ i).
Qed.

Lemma halts_ipeq p P Q R : ipeq P Q ->
  rm_halts p (P,R) -> rm_halts p (Q,R).
Proof.
  intros E (n & c & Hr & Ha).
  destruct (RMEquiv.hn_ipeq p n P Q R E (ex_intro _ c (conj Hr Ha)))
    as (c' & Hr' & Ha'). exists n,c'. auto.
Qed.

Definition branch_ok (t1 t2 : tree) (C : list entry)
    (A B : list bool) (j : N) : bool :=
  match seg t1 seg_fuel A, seg t2 seg_fuel B, getc C j with
  | Some (l1,P1), Some (l2,P2), Some (Q1,Q2) =>
      cnt_eq l1 l2 && ibeq P1 Q1 && ibeq P2 Q2
  | _,_,_ => false
  end.

Definition entry_ok (t1 t2 : tree) (C : list entry) (x : entry) : bool :=
  let '(P1,P2,j,k) := x in
  match tsite t1 P1, tsite t2 P2 with
  | Some (EHalt,_), Some (EHalt,_) => true
  | Some (EDecnz r1,Q1), Some (EDecnz r2,Q2) =>
      Nat.eqb r1 r2 &&
      branch_ok t1 t2 C (inc_path Q1) (inc_path Q2) j &&
      branch_ok t1 t2 C (brk 1 Q1) (brk 1 Q2) k
  | _,_ => false
  end.

Definition check (t1 t2 : tree) (C : list entry) : bool :=
  branch_ok t1 t2 C [] [] 0 && forallb (entry_ok t1 t2 C) C.

Section Sound.
Variables p1 p2 : prog.
Variable C : list entry.
Hypothesis HC : forallb (entry_ok (ptree p1) (ptree p2) C) C = true.

Lemma branch_sim N A B j R1 R2
  (IH : forall N', N' < S N -> forall P1 P2 j' k' R1 R2,
    In (P1,P2,j',k') C -> (forall i, R1 i = R2 i) ->
    Bisim230.hn p1 N' (P1,R1) -> rm_halts p2 (P2,R2)) :
  branch_ok (ptree p1) (ptree p2) C A B j = true ->
  (forall i, R1 i = R2 i) ->
  Bisim230.hn p1 N (A,R1) -> rm_halts p2 (B,R2).
Proof.
  unfold branch_ok. intros Hb HR Hh.
  destruct (seg (ptree p1) seg_fuel A) as [[l1 Q1]|] eqn:E1; [|discriminate].
  destruct (seg (ptree p2) seg_fuel B) as [[l2 Q2]|] eqn:E2; [|discriminate].
  destruct (getc C j) as [[P1 P2]|] eqn:Eg; [|discriminate].
  apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [Hc H1].
  apply ibeq_ok in H1,H2. pose proof (cnt_eq_ok _ _ Hc) as Hc'.
  destruct (getc_in _ _ _ _ Eg) as (j' & k' & Hin).
  destruct (seg_hn p1 _ _ _ _ R1 N E1 Hh) as (N' & R1' & Hle & Hh' & HR1).
  destruct (seg_run p2 _ _ _ _ R2 E2) as (n & R2' & Hr & HR2).
  apply (halts_pre p2 n _ _ Hr).
  apply (halts_ipeq p2 P2 Q2 R2' (ipeq_sym _ _ H2)).
  apply (IH N' ltac:(lia) P1 P2 j' k' R1' R2' Hin).
  - intros i. rewrite HR1,HR2,HR,Hc'. reflexivity.
  - exact (RMEquiv.hn_ipeq p1 N' Q1 P1 R1' H1 Hh').
Qed.

Lemma sim N : forall P1 P2 j k R1 R2,
  In (P1,P2,j,k) C -> (forall i, R1 i = R2 i) ->
  Bisim230.hn p1 N (P1,R1) -> rm_halts p2 (P2,R2).
Proof.
  induction N as [N IH] using lt_wf_ind. intros P1 P2 j k R1 R2 Hin HR Hh.
  rewrite forallb_forall in HC. pose proof (HC _ Hin) as He. cbn [entry_ok] in He.
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

Theorem check_sound p1 p2 C : check (ptree p1) (ptree p2) C = true ->
  forall R, rm_halts p1 ([],R) -> rm_halts p2 ([],R).
Proof.
  unfold check. intros Hc R (N & c & Hr & Ha). apply andb_prop in Hc as [Hb HC].
  assert (IH : forall N', N' < S N -> forall P1 P2 j' k' R1 R2,
    In (P1,P2,j',k') C -> (forall i, R1 i = R2 i) ->
    Bisim230.hn p1 N' (P1,R1) -> rm_halts p2 (P2,R2))
    by (intros N' _; apply (sim p1 p2 C HC N')).
  apply (branch_sim p1 p2 C N [] [] 0 R R IH Hb); [reflexivity|].
  exists c. auto.
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
  destruct x as [[[P1 P2] j] k]. unfold entry_ok,flip_plain.
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

Theorem check_one_sided_iff p1 p2 C :
  check (ptree p1) (ptree p2) C = true ->
  forall R, rm_halts p1 ([],R) <-> rm_halts p2 ([],R).
Proof.
  intros H R. split.
  - exact (check_sound p1 p2 C H R).
  - exact (check_sound p2 p1 (mirror C) (check_mirror _ _ _ H) R).
Qed.

Print Assumptions ibeq_ok.
Print Assumptions check_one_sided_iff.
End NCheck.
