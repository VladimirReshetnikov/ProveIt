(** Rocq port of the zero-padding certificate normalization in incoming packet 2.
    It preserves RM.v, reuses Bisim230's segment lemmas, and transports completed
    segment endpoints with the existing RMEquiv.hn_ipeq theorem. *)
From Coq Require Import List Bool Arith Lia NArith.
From K230 Require Import RM RMEquiv.
From K230P Require Import Bisim230.
Require Import BisimMirror.
Import ListNotations.

Fixpoint zeros (P : list bool) : bool :=
  match P with [] => true | b :: P => negb b && zeros P end.

Lemma zeros_ok P : zeros P = true -> ipeq P [].
Proof.
  induction P as [|b P IH].
  - intros _ i. reflexivity.
  - destruct b; cbn [zeros]; [discriminate|].
    intros H [|i]; [reflexivity|].
    change (bit P i = false). rewrite <- (bit_nil i). apply (IH H i).
Qed.

Fixpoint ibeq (P Q : list bool) : bool :=
  match P, Q with
  | [], Q => zeros Q
  | P, [] => zeros P
  | b :: P, c :: Q => Bool.eqb b c && ibeq P Q
  end.

Lemma ibeq_ok P Q : ibeq P Q = true -> ipeq P Q.
Proof.
  revert Q. induction P as [|b P IH]; intros [|c Q] H.
  - apply ipeq_refl.
  - apply ipeq_sym, zeros_ok, H.
  - apply zeros_ok, H.
  - cbn [ibeq] in H. apply andb_prop in H as [Hbc HPQ].
    apply Bool.eqb_prop in Hbc. subst c.
    intros [|i]; [reflexivity|]. apply (IH _ HPQ i).
Qed.

Lemma ibeq_sym P Q : ibeq P Q = ibeq Q P.
Proof.
  revert Q. induction P as [|b P IH]; intros [|c Q]; try reflexivity.
  cbn [ibeq]. rewrite IH. destruct b,c; reflexivity.
Qed.

Lemma halts_ipeq p P Q R : ipeq P Q -> rm_halts p (P,R) -> rm_halts p (Q,R).
Proof.
  intros H [N HN]. exists N. exact (hn_ipeq p N P Q R H HN).
Qed.

Definition nbranch_ok (t1 t2 : tree) (C : list entry) (A B : list bool) (j : N) : bool :=
  match seg t1 seg_fuel A, seg t2 seg_fuel B, getc C j with
  | Some (l1, P1), Some (l2, P2), Some (Q1, Q2) => cnt_eq l1 l2 && ibeq P1 Q1 && ibeq P2 Q2
  | _, _, _ => false
  end.

Definition nentry_ok (t1 t2 : tree) (C : list entry) (x : entry) : bool :=
  let '(P1, P2, j, k) := x in
  match tsite t1 P1, tsite t2 P2 with
  | Some (EHalt, _), Some (EHalt, _) => true
  | Some (EDecnz r1, Q1), Some (EDecnz r2, Q2) =>
      Nat.eqb r1 r2 && nbranch_ok t1 t2 C (inc_path Q1) (inc_path Q2) j
                    && nbranch_ok t1 t2 C (brk 1 Q1) (brk 1 Q2) k
  | _, _ => false
  end.

Definition ncheck (t1 t2 : tree) (C : list entry) : bool :=
  nbranch_ok t1 t2 C [] [] 0 && forallb (nentry_ok t1 t2 C) C.

Section Sound.
Variables p1 p2 : prog.
Variable C : list entry.
Hypothesis HC : forallb (nentry_ok (ptree p1) (ptree p2) C) C = true.

Lemma getc_in j P1 P2 : getc C j = Some (P1, P2) -> exists j' k', In (P1, P2, j', k') C.
Proof.
  unfold getc. destruct (nth_error C (N.to_nat j)) as [[[[a b] j'] k']|] eqn:E; [|discriminate].
  intros H. injection H as <- <-. exists j', k'. eapply nth_error_In; eauto.
Qed.

(* one branch: the p1 side halts within N steps from the branch IP => the p2 side halts *)
Lemma nbranch_sim N A B j R1 R2 (IH : forall N', N' < S N -> forall P1 P2 j' k' R1 R2,
    In (P1, P2, j', k') C -> (forall i, R1 i = R2 i) -> hn p1 N' (P1, R1) -> rm_halts p2 (P2, R2)) :
  nbranch_ok (ptree p1) (ptree p2) C A B j = true -> (forall i, R1 i = R2 i) ->
  hn p1 N (A, R1) -> rm_halts p2 (B, R2).
Proof.
  unfold nbranch_ok. intros Hb HR Hh.
  destruct (seg (ptree p1) seg_fuel A) as [[l1 Q1]|] eqn:E1; [|discriminate].
  destruct (seg (ptree p2) seg_fuel B) as [[l2 Q2]|] eqn:E2; [|discriminate].
  destruct (getc C j) as [[P1 P2]|] eqn:Eg; [|discriminate].
  apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [Hc H1].
  apply ibeq_ok in H1, H2. pose proof (cnt_eq_ok _ _ Hc) as Hc'.
  destruct (getc_in _ _ _ Eg) as (j' & k' & Hin).
  destruct (seg_hn p1 _ _ _ _ R1 N E1 Hh) as (N' & R1' & Hle & Hh' & HR1).
  destruct (seg_run p2 _ _ _ _ R2 E2) as (n & R2' & Hr & HR2).
  apply (halts_pre p2 n _ _ Hr).
  apply (halts_ipeq p2 P2 Q2 R2' (ipeq_sym _ _ H2)).
  apply (IH N' ltac:(lia) _ _ j' k' R1' R2' Hin).
  2: exact (hn_ipeq p1 N' Q1 P1 R1' H1 Hh').
  intros i. rewrite HR1, HR2, HR, Hc'. reflexivity.
Qed.

Lemma nsim N : forall P1 P2 j k R1 R2, In (P1, P2, j, k) C -> (forall i, R1 i = R2 i) ->
  hn p1 N (P1, R1) -> rm_halts p2 (P2, R2).
Proof.
  induction N as [N IH] using lt_wf_ind. intros P1 P2 j k R1 R2 Hin HR Hh.
  rewrite forallb_forall in HC. pose proof (HC _ Hin) as He. cbn [nentry_ok] in He.
  destruct (tsite (ptree p1) P1) as [[e1 Q1]|] eqn:T1; [|discriminate].
  destruct (tsite (ptree p2) P2) as [[e2 Q2]|] eqn:T2; [|destruct e1; discriminate].
  destruct e1; try discriminate; destruct e2; try discriminate.
  - (* decnz *)
    apply andb_prop in He as [He Hk]. apply andb_prop in He as [Hr Hj].
    apply Nat.eqb_eq in Hr. subst.
    destruct N as [|N].
    { destruct Hh as (c & Hc & Ha). injection Hc as <-. apply at_halt_tsite in Ha as [Q Ha].
      rewrite T1 in Ha. discriminate. }
    destruct (R1 r0) as [|v] eqn:Ev.
    + assert (Hs : lres (EDecnz r0) Q1 R1 = Some (brk 1 Q1, R1)) by (cbn; rewrite Ev; reflexivity).
      destruct (hn_step p1 _ _ _ _ _ _ T1 ltac:(discriminate) Hs Hh) as (N' & E & Hh').
      assert (N' = N) by congruence; subst N'.
      apply (halts_pre p2 1 _ (brk 1 Q2, R2)).
      { cbn [rm_run]. rewrite step_tsite, T2. cbn. rewrite <- HR, Ev. reflexivity. }
      exact (nbranch_sim N (brk 1 Q1) (brk 1 Q2) k R1 R2 IH Hk HR Hh').
    + assert (Hs : lres (EDecnz r0) Q1 R1 = Some (inc_path Q1, upd R1 r0 v)) by (cbn; rewrite Ev; reflexivity).
      destruct (hn_step p1 _ _ _ _ _ _ T1 ltac:(discriminate) Hs Hh) as (N' & E & Hh').
      assert (N' = N) by congruence; subst N'.
      apply (halts_pre p2 1 _ (inc_path Q2, upd R2 r0 v)).
      { cbn [rm_run]. rewrite step_tsite, T2. cbn. rewrite <- HR, Ev. reflexivity. }
      apply (nbranch_sim N (inc_path Q1) (inc_path Q2) j (upd R1 r0 v) (upd R2 r0 v) IH Hj); auto.
      intros i. unfold upd. rewrite HR. reflexivity.
  - (* halt *)
    exists 0, (P2, R2). split; [reflexivity|]. apply at_halt_tsite. eauto.
Qed.

End Sound.

Theorem ncheck_sound p1 p2 C : ncheck (ptree p1) (ptree p2) C = true ->
  forall R, rm_halts p1 ([], R) -> rm_halts p2 ([], R).
Proof.
  unfold ncheck. intros Hc R (N & c & Hr & Ha). apply andb_prop in Hc as [Hb HC].
  assert (IH : forall N', N' < S N -> forall P1 P2 j' k' R1 R2, In (P1, P2, j', k') C ->
      (forall i, R1 i = R2 i) -> hn p1 N' (P1, R1) -> rm_halts p2 (P2, R2))
    by (intros N' _; apply (nsim p1 p2 C HC N')).
  apply (nbranch_sim p1 p2 C N [] [] 0 R R IH Hb); [reflexivity|]. exists c. auto.
Qed.

Lemma nbranch_ok_mirror t1 t2 C A B j : nbranch_ok t1 t2 C A B j = true ->
  nbranch_ok t2 t1 (mirror C) B A j = true.
Proof.
  unfold nbranch_ok. rewrite getc_mirror.
  destruct (seg t1 seg_fuel A) as [[l1 P1]|]; [|discriminate].
  destruct (seg t2 seg_fuel B) as [[l2 P2]|]; [|discriminate].
  destruct (getc C j) as [[Q1 Q2]|]; [|discriminate].
  repeat rewrite andb_true_iff. intros [[Hc H1] H2].
  split; [split|]; try assumption. apply cnt_eq_mirror. exact Hc.
Qed.

Lemma nentry_ok_mirror t1 t2 C x : nentry_ok t1 t2 C x = true ->
  nentry_ok t2 t1 (mirror C) (flip_plain x) = true.
Proof.
  destruct x as [[[P1 P2] j] k]. unfold nentry_ok, flip_plain.
  destruct (tsite t1 P1) as [[e1 Q1]|]; [|discriminate].
  destruct (tsite t2 P2) as [[e2 Q2]|]; [|destruct e1; discriminate].
  destruct e1; try discriminate; destruct e2; try discriminate.
  - repeat rewrite andb_true_iff. intros [[Hr Hj] Hk].
    apply Nat.eqb_eq in Hr. subst. repeat split.
    + apply Nat.eqb_refl.
    + apply nbranch_ok_mirror. exact Hj.
    + apply nbranch_ok_mirror. exact Hk.
  - reflexivity.
Qed.

Theorem ncheck_mirror t1 t2 C : ncheck t1 t2 C = true ->
  ncheck t2 t1 (mirror C) = true.
Proof.
  unfold ncheck. rewrite !andb_true_iff. intros [Hb He]. split.
  - exact (nbranch_ok_mirror t1 t2 C [] [] 0 Hb).
  - unfold mirror. rewrite forallb_forall. rewrite forallb_forall in He.
    intros y Hy. apply in_map_iff in Hy as [x [<- Hx]].
    exact (nentry_ok_mirror t1 t2 C x (He x Hx)).
Qed.


Theorem ncheck_one_sided_iff p1 p2 C : ncheck (ptree p1) (ptree p2) C = true ->
  forall R, rm_halts p1 ([],R) <-> rm_halts p2 ([],R).
Proof.
  intros H R. split.
  - apply (ncheck_sound p1 p2 C H).
  - apply (ncheck_sound p2 p1 (mirror C)). now apply ncheck_mirror.
Qed.

Print Assumptions ibeq_ok.
Print Assumptions ncheck_one_sided_iff.
