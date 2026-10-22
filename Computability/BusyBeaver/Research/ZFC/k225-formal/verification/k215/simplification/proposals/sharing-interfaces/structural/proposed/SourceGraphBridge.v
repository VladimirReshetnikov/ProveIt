From Coq Require Import Lists.List Bool Arith Lia NArith.
From K230 Require Import RM RMEquiv.
From K230P Require Import Bisim230.
Require Import PathEq DrainCore.
Import ListNotations.

(** The graph certificate is checked against the literal program tree.
    Generated vertex labels, addresses and increment lists are untrusted. *)
Fixpoint expand (a : increments) : list nat :=
  match a with [] => [] | (r,k)::xs => repeat r k ++ expand xs end.

Lemma cnt_app xs ys i : cnt (xs ++ ys) i = cnt xs i + cnt ys i.
Proof. unfold cnt; rewrite filter_app, app_length; reflexivity. Qed.

Lemma cnt_repeat r k i : cnt (repeat r k) i = if Nat.eqb i r then k else 0.
Proof.
  induction k as [|k IH]; unfold cnt in *; simpl; [destruct (Nat.eqb i r); reflexivity|].
  destruct (Nat.eqb i r); simpl in *; rewrite IH; reflexivity.
Qed.

Lemma cnt_expand a i : cnt (expand a) i = amount a i.
Proof.
  induction a as [|[r k] xs IH]; simpl; [reflexivity|].
  rewrite cnt_app, cnt_repeat, IH; reflexivity.
Qed.

Definition branch_ok (t : Bisim230.tree) (L : N -> list bool)
    (A : list bool) (a : arc) : bool :=
  match seg t seg_fuel A with
  | Some (l,P) => cnt_eq l (expand (adds a)) && PathEq.ibeq P (L (destination a))
  | None => false
  end.

Definition node_ok (t : Bisim230.tree) (G : graph)
    (L : N -> list bool) (v : N) : bool :=
  match G v with
  | Some DrainCore.Halt =>
      match tsite t (L v) with Some (EHalt,_) => true | _ => false end
  | Some (Test r a b) =>
      match tsite t (L v) with
      | Some (EDecnz s,Q) =>
          Nat.eqb r s && branch_ok t L (inc_path Q) a && branch_ok t L (brk 1 Q) b
      | _ => false
      end
  | None => false
  end.

Lemma branch_ok_spec t L A a : branch_ok t L A a = true ->
  exists l P, seg t seg_fuel A = Some (l,P) /\
    (forall i, cnt l i = amount (adds a) i) /\ ipeq P (L (destination a)).
Proof.
  unfold branch_ok; destruct (seg t seg_fuel A) as [[l P]|] eqn:E; [|discriminate].
  rewrite andb_true_iff; intros [C B]; exists l,P; split; [reflexivity|]; split.
  - intro i; rewrite (cnt_eq_ok _ _ C), cnt_expand; reflexivity.
  - apply PathEq.ibeq_ok; assumption.
Qed.

Section Adequacy.
Variable p : prog.
Variable G : graph.
Variable L : N -> list bool.
Hypothesis valid : forall v x, G v = Some x -> node_ok (ptree p) G L v = true.
Hypothesis closed : forall v r a b, G v = Some (Test r a b) ->
  (exists x, G (destination a) = Some x) /\
  (exists x, G (destination b) = Some x).

Lemma halt_site v : G v = Some DrainCore.Halt ->
  exists Q, tsite (ptree p) (L v) = Some (EHalt,Q).
Proof.
  intro E; pose proof (valid _ _ E) as H; unfold node_ok in H; rewrite E in H.
  destruct (tsite (ptree p) (L v)) as [[e Q]|] eqn:T; [|discriminate].
  destruct e; try discriminate; eauto.
Qed.

Lemma test_site v r a b : G v = Some (Test r a b) ->
  exists Q, tsite (ptree p) (L v) = Some (EDecnz r,Q) /\
    branch_ok (ptree p) L (inc_path Q) a = true /\
    branch_ok (ptree p) L (brk 1 Q) b = true.
Proof.
  intro E; pose proof (valid _ _ E) as H; unfold node_ok in H; rewrite E in H.
  destruct (tsite (ptree p) (L v)) as [[e Q]|] eqn:T; [|discriminate].
  destruct e; try discriminate.
  repeat rewrite andb_true_iff in H; destruct H as [[A B] C].
  apply Nat.eqb_eq in A; subst; exists Q; auto.
Qed.

Lemma branch_pre A a R V : branch_ok (ptree p) L A a = true ->
  req V (plus R (adds a)) ->
  (forall S, req V S -> rm_halts p (L (destination a),S)) -> rm_halts p (A,R).
Proof.
  intros B E H; destruct (branch_ok_spec _ _ _ _ B) as (l & P & Seg & C & Loc).
  destruct (seg_run p _ _ _ _ R Seg) as (n & S & Run & Eq).
  eapply halts_pre; [exact Run|].
  apply (PathEq.halts_ipeq p (L (destination a)) P S (ipeq_sym _ _ Loc)).
  apply H; intro i; rewrite E, Eq, C; reflexivity.
Qed.

Lemma step_pre v R w V : step G v R w V ->
  (forall S, req V S -> rm_halts p (L w,S)) ->
  forall T, req R T -> rm_halts p (L v,T).
Proof.
  intro E; destruct E as [v r a b R V Gv Rz Vq | v r a b R V Gv Rp Vq];
    intros Tail T RT; destruct (test_site _ _ _ _ Gv) as (Q & Site & Ba & Bb).
  - assert (Tz : T r = 0) by (rewrite <- RT; exact Rz).
    apply (halts_pre p 1 (L v,T) (brk 1 Q,T)).
    { cbn [rm_run]; rewrite step_tsite, Site; cbn [lres]; rewrite Tz; reflexivity. }
    apply (branch_pre _ b T V Bb); [|exact Tail].
    intro i; rewrite Vq; unfold plus; rewrite RT; reflexivity.
  - destruct (T r) as [|n] eqn:Tn; [rewrite RT, Tn in Rp; lia|].
    apply (halts_pre p 1 (L v,T) (inc_path Q,upd T r n)).
    { cbn [rm_run]; rewrite step_tsite, Site; cbn [lres]; rewrite Tn; reflexivity. }
    apply (branch_pre _ a (upd T r n) V Ba); [|exact Tail].
    intro i; rewrite Vq; unfold decplus, plus, upd; rewrite RT, RT, Tn.
    destruct (Nat.eqb i r); reflexivity.
Qed.

Theorem graph_to_source v R : halts G v R ->
  forall S, req R S -> rm_halts p (L v,S).
Proof.
  intro H; induction H as [v R H | v R w Q E H IH]; intros S RS.
  - exists 0,(L v,S); split; [reflexivity|].
    apply at_halt_tsite; apply halt_site; exact H.
  - eapply step_pre; eauto.
Qed.

Lemma source_to_graph_bounded N : forall v x R,
  G v = Some x -> Bisim230.hn p N (L v,R) -> halts G v R.
Proof.
  induction N as [N IH] using lt_wf_ind; intros v x R Gv H.
  destruct x as [|r a b].
  - constructor; exact Gv.
  - destruct (test_site _ _ _ _ Gv) as (Q & Site & Ba & Bb).
    destruct (closed _ _ _ _ Gv) as [[xa Ca] [xb Cb]].
    destruct (R r) as [|n] eqn:Rr.
    + assert (Lr : lres (EDecnz r) Q R = Some (brk 1 Q,R))
        by (cbn [lres]; rewrite Rr; reflexivity).
      destruct (hn_step p N (L v) R _ Q _ Site ltac:(discriminate) Lr H)
        as (N1 & NN & H1).
      destruct (branch_ok_spec _ _ _ _ Bb) as (l & P & Seg & C & Loc).
      destruct (seg_hn p _ _ _ _ R N1 Seg H1) as (N2 & S & Le & H2 & Eq).
      eapply halt_later with (w:=destination b) (S:=S).
      * eapply step_zero with (r:=r) (a:=a) (b:=b); eauto.
        intro i; rewrite Eq, C; reflexivity.
      * eapply (IH N2 ltac:(lia) _ xb); [exact Cb|].
        exact (RMEquiv.hn_ipeq p N2 P (L (destination b)) S Loc H2).
    + assert (Lr : lres (EDecnz r) Q R = Some (inc_path Q,upd R r n))
        by (cbn [lres]; rewrite Rr; reflexivity).
      destruct (hn_step p N (L v) R _ Q _ Site ltac:(discriminate) Lr H)
        as (N1 & NN & H1).
      destruct (branch_ok_spec _ _ _ _ Ba) as (l & P & Seg & C & Loc).
      destruct (seg_hn p _ _ _ _ (upd R r n) N1 Seg H1) as (N2 & S & Le & H2 & Eq).
      eapply halt_later with (w:=destination a) (S:=S).
      * eapply step_pos with (r:=r) (a:=a) (b:=b); [exact Gv|lia|].
        intro i; rewrite Eq, C; unfold upd, decplus; rewrite Rr; reflexivity.
      * eapply (IH N2 ltac:(lia) _ xa); [exact Ca|].
        exact (RMEquiv.hn_ipeq p N2 P (L (destination a)) S Loc H2).
Qed.

Theorem source_graph_halts_iff v x R : G v = Some x ->
  rm_halts p (L v,R) <-> halts G v R.
Proof.
  intro E; split.
  - intros (n & c & Run & Stop); apply (source_to_graph_bounded n v x R E).
    exists c; split; assumption.
  - intro H; exact (graph_to_source _ _ H R (req_refl R)).
Qed.
End Adequacy.

Print Assumptions source_graph_halts_iff.
