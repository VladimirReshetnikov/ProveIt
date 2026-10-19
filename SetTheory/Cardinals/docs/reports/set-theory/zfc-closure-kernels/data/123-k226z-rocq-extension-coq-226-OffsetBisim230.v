(** A finite register-offset extension of K230P.Bisim230.
    Only register 5 may differ at certificate checkpoints.  The offset is
    a mathematical integer; both actual register files remain natural-valued.
    Test outcomes are compared only when the tested register's offset is zero.
    The helper segment semantics are inherited unchanged from the pinned checker. *)
From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia NArith ZArith.
From K230 Require Import RM.
From K230P Require Import Bisim230.
Import ListNotations.

Definition delta (z : Z) (i : nat) : Z := if Nat.eqb i 5 then z else 0%Z.
Definition related (z : Z) (R1 R2 : regs) : Prop :=
  forall i, Z.of_nat (R1 i) = (Z.of_nat (R2 i) + delta z i)%Z.

Definition oentry : Type := (list bool * list bool * Z * N * N)%type.

Definition counts_ok (z z' : Z) (l1 l2 : list nat) : bool :=
  forallb (fun i => Z.eqb (delta z i + Z.of_nat (cnt l1 i))
                         (Z.of_nat (cnt l2 i) + delta z' i))
          (5 :: l1 ++ l2).

Lemma cnt_notin l i : ~ In i l -> cnt l i = 0.
Proof.
  intros H. unfold cnt. induction l as [|x l IH]; [reflexivity|].
  cbn [filter]. destruct (Nat.eqb_spec i x) as [->|].
  - exfalso. apply H. now left.
  - apply IH. intros Hi. apply H. now right.
Qed.

Lemma counts_ok_sound z z' l1 l2 : counts_ok z z' l1 l2 = true ->
  forall i, (delta z i + Z.of_nat (cnt l1 i))%Z =
            (Z.of_nat (cnt l2 i) + delta z' i)%Z.
Proof.
  unfold counts_ok. rewrite forallb_forall. intros H i.
  destruct (in_dec Nat.eq_dec i (5 :: l1 ++ l2)) as [Hi|Hi].
  - apply Z.eqb_eq, H, Hi.
  - assert (H5 : Nat.eqb i 5 = false).
    { apply Nat.eqb_neq. intros ->. apply Hi. now left. }
    assert (H1 : ~ In i l1) by (intros E; apply Hi; right; apply in_or_app; now left).
    assert (H2 : ~ In i l2) by (intros E; apply Hi; right; apply in_or_app; now right).
    unfold delta. rewrite H5, (cnt_notin _ _ H1), (cnt_notin _ _ H2). reflexivity.
Qed.

Definition ogetc (C : list oentry) (j : N) : option (list bool * list bool * Z) :=
  match nth_error C (N.to_nat j) with Some (a,b,z,_,_) => Some (a,b,z) | None => None end.

Definition obranch_ok (t1 t2 : tree) (C : list oentry)
    (A B : list bool) (z : Z) (j : N) : bool :=
  match seg t1 seg_fuel A, seg t2 seg_fuel B, ogetc C j with
  | Some (l1,P1), Some (l2,P2), Some (Q1,Q2,z') =>
      counts_ok z z' l1 l2 && lbeq P1 Q1 && lbeq P2 Q2
  | _,_,_ => false
  end.

Definition oentry_ok (t1 t2 : tree) (C : list oentry) (x : oentry) : bool :=
  let '(P1,P2,z,j,k) := x in
  match tsite t1 P1, tsite t2 P2 with
  | Some (EHalt,_), Some (EHalt,_) => true
  | Some (EDecnz r1,Q1), Some (EDecnz r2,Q2) =>
      Nat.eqb r1 r2 && Z.eqb (delta z r1) 0 &&
      obranch_ok t1 t2 C (inc_path Q1) (inc_path Q2) z j &&
      obranch_ok t1 t2 C (brk 1 Q1) (brk 1 Q2) z k
  | _,_ => false
  end.

Definition ocheck (t1 t2 : tree) (C : list oentry) : bool :=
  obranch_ok t1 t2 C [] [] 0 0 && forallb (oentry_ok t1 t2 C) C.

Definition omirror (C : list oentry) : list oentry :=
  map (fun '(a,b,z,j,k) => (b,a,(-z)%Z,j,k)) C.

Lemma related_at z R1 R2 r : related z R1 R2 -> delta z r = 0%Z -> R1 r = R2 r.
Proof. intros HR Hz. specialize (HR r). rewrite Hz in HR. lia. Qed.

Lemma related_update z R1 R2 r v : related z R1 R2 -> delta z r = 0%Z ->
  related z (upd R1 r v) (upd R2 r v).
Proof.
  intros HR Hz i. unfold upd. destruct (Nat.eqb_spec i r) as [->|Hne].
  - rewrite Hz. lia.
  - exact (HR i).
Qed.

Section Sound.
Variables p1 p2 : prog.
Variable C : list oentry.
Hypothesis HC : forallb (oentry_ok (ptree p1) (ptree p2) C) C = true.

Lemma ogetc_in j P1 P2 z : ogetc C j = Some (P1,P2,z) ->
  exists j' k', In (P1,P2,z,j',k') C.
Proof.
  unfold ogetc.
  destruct (nth_error C (N.to_nat j)) as [[[[[a b] z'] j'] k']|] eqn:E; [|discriminate].
  intros H. injection H as <- <- <-. exists j',k'. eapply nth_error_In; eauto.
Qed.

Lemma obranch_sim N A B z j R1 R2
  (IH : forall N', N' < S N -> forall P1 P2 z' j' k' R1 R2,
    In (P1,P2,z',j',k') C -> related z' R1 R2 ->
    hn p1 N' (P1,R1) -> rm_halts p2 (P2,R2)) :
  obranch_ok (ptree p1) (ptree p2) C A B z j = true -> related z R1 R2 ->
  hn p1 N (A,R1) -> rm_halts p2 (B,R2).
Proof.
  unfold obranch_ok. intros Hb HR Hh.
  destruct (seg (ptree p1) seg_fuel A) as [[l1 Q1]|] eqn:E1; [|discriminate].
  destruct (seg (ptree p2) seg_fuel B) as [[l2 Q2]|] eqn:E2; [|discriminate].
  destruct (ogetc C j) as [[[P1 P2] z']|] eqn:Eg; [|discriminate].
  apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [Hc H1].
  apply lbeq_ok in H1,H2. subst P1 P2.
  pose proof (counts_ok_sound _ _ _ _ Hc) as Hcounts.
  destruct (ogetc_in _ _ _ _ Eg) as (j' & k' & Hin).
  destruct (seg_hn p1 _ _ _ _ R1 N E1 Hh) as (N' & R1' & Hle & Hh' & HR1).
  destruct (seg_run p2 _ _ _ _ R2 E2) as (n & R2' & Hr & HR2).
  apply (halts_pre p2 n _ _ Hr).
  apply (IH N' ltac:(lia) _ _ z' j' k' R1' R2' Hin); [|exact Hh'].
  intros i. rewrite HR1,HR2,!Nat2Z.inj_add.
  specialize (HR i). specialize (Hcounts i). lia.
Qed.

Lemma osim N : forall P1 P2 z j k R1 R2, In (P1,P2,z,j,k) C -> related z R1 R2 ->
  hn p1 N (P1,R1) -> rm_halts p2 (P2,R2).
Proof.
  induction N as [N IH] using lt_wf_ind. intros P1 P2 z j k R1 R2 Hin HR Hh.
  rewrite forallb_forall in HC. pose proof (HC _ Hin) as He. cbn [oentry_ok] in He.
  destruct (tsite (ptree p1) P1) as [[e1 Q1]|] eqn:T1; [|discriminate].
  destruct (tsite (ptree p2) P2) as [[e2 Q2]|] eqn:T2; [|destruct e1; discriminate].
  destruct e1; try discriminate; destruct e2; try discriminate.
  - apply andb_prop in He as [He Hk]. apply andb_prop in He as [He Hj].
    apply andb_prop in He as [Hr Hz].
    apply Nat.eqb_eq in Hr. subst. apply Z.eqb_eq in Hz.
    pose proof (related_at _ _ _ _ HR Hz) as HRr.
    destruct N as [|N].
    { destruct Hh as (c & Hc & Ha). injection Hc as <-.
      apply at_halt_tsite in Ha as [Q Ha]. rewrite T1 in Ha. discriminate. }
    destruct (R1 r0) as [|v] eqn:Ev.
    + assert (Hs : lres (EDecnz r0) Q1 R1 = Some (brk 1 Q1,R1)) by (cbn; rewrite Ev; reflexivity).
      destruct (hn_step p1 _ _ _ _ _ _ T1 ltac:(discriminate) Hs Hh) as (N' & E & Hh').
      assert (N'=N) by congruence. subst N'.
      apply (halts_pre p2 1 _ (brk 1 Q2,R2)).
      { cbn [rm_run]. rewrite step_tsite,T2. cbn. rewrite <- HRr. reflexivity. }
      exact (obranch_sim N (brk 1 Q1) (brk 1 Q2) z k R1 R2 IH Hk HR Hh').
    + assert (Hs : lres (EDecnz r0) Q1 R1 = Some (inc_path Q1,upd R1 r0 v)) by (cbn; rewrite Ev; reflexivity).
      destruct (hn_step p1 _ _ _ _ _ _ T1 ltac:(discriminate) Hs Hh) as (N' & E & Hh').
      assert (N'=N) by congruence. subst N'.
      apply (halts_pre p2 1 _ (inc_path Q2,upd R2 r0 v)).
      { cbn [rm_run]. rewrite step_tsite,T2. cbn. rewrite <- HRr. reflexivity. }
      apply (obranch_sim N (inc_path Q1) (inc_path Q2) z j
                   (upd R1 r0 v) (upd R2 r0 v) IH Hj); [|exact Hh'].
      apply related_update; assumption.
  - exists 0,(P2,R2). split; [reflexivity|]. apply at_halt_tsite. eauto.
Qed.

End Sound.

Theorem ocheck_sound p1 p2 C : ocheck (ptree p1) (ptree p2) C = true ->
  forall R, rm_halts p1 ([],R) -> rm_halts p2 ([],R).
Proof.
  unfold ocheck. intros Hc R (N & c & Hr & Ha). apply andb_prop in Hc as [Hb HC].
  assert (IH : forall N', N' < S N -> forall P1 P2 z j' k' R1 R2,
      In (P1,P2,z,j',k') C -> related z R1 R2 ->
      hn p1 N' (P1,R1) -> rm_halts p2 (P2,R2))
    by (intros N' _; apply (osim p1 p2 C HC N')).
  apply (obranch_sim p1 p2 C N [] [] 0 0 R R IH Hb).
  - intros i. unfold delta. destruct (Nat.eqb i 5); lia.
  - exists c. auto.
Qed.

Theorem ocheck_iff p1 p2 C :
  ocheck (ptree p1) (ptree p2) C = true ->
  ocheck (ptree p2) (ptree p1) (omirror C) = true ->
  forall R, rm_halts p1 ([],R) <-> rm_halts p2 ([],R).
Proof.
  intros H1 H2 R. split.
  - apply (ocheck_sound p1 p2 C H1).
  - apply (ocheck_sound p2 p1 _ H2).
Qed.

Print Assumptions ocheck_iff.
