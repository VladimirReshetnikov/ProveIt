From Coq Require Import Arith Lia List Bool NArith.
Import ListNotations.
Set Implicit Arguments.

(* Lists avoid functional extensionality and keep the theorem closed. *)
Definition regs := list nat.
Definition get (R : regs) (j : nat) : nat := nth j R 0.
Fixpoint tab (n : nat) (f : nat -> nat) : regs :=
  match n with 0 => [] | S k => f 0 :: tab k (fun j => f (S j)) end.
Lemma tab_length : forall n f, length (tab n f) = n.
Proof. induction n; intros; simpl; auto. Qed.
Lemma get_tab : forall n f j, j < n -> get (tab n f) j = f j.
Proof. induction n as [|n IH]; intros f j H; [lia|]. destruct j as [|j]; [reflexivity|]. change (get (tab n (fun k => f (S k))) j = f (S j)). apply (IH (fun k => f (S k)) j); lia. Qed.
Lemma regs_ext : forall A B, length A = length B ->
  (forall j, j < length A -> get A j = get B j) -> A = B.
Proof. intros A B H E. apply nth_ext with (d:=0) (d':=0); auto. Qed.
Definition plus (R c : regs) := tab (length R) (fun j => get R j + get c j).
Definition dec (R : regs) (r : nat) :=
  tab (length R) (fun j => if Nat.eqb j r then Nat.pred (get R j) else get R j).
Definition affine (R : regs) (r : nat) (c d : regs) :=
  tab (length R) (fun j => if Nat.eqb j r then get d j
     else get R j + get R r * get c j + get d j).
Lemma plus_length : forall R c, length (plus R c) = length R.
Proof. intros; apply tab_length. Qed.
Lemma dec_length : forall R r, length (dec R r) = length R.
Proof. intros; apply tab_length. Qed.
Lemma affine_length : forall R r c d, length (affine R r c d) = length R.
Proof. intros; apply tab_length. Qed.
Lemma get_plus : forall R c j, j < length R -> get (plus R c) j = get R j + get c j.
Proof. intros R c j H; exact (@get_tab (length R) (fun k => get R k + get c k) j H). Qed.
Lemma get_dec : forall R r j, j < length R ->
  get (dec R r) j = if Nat.eqb j r then Nat.pred (get R j) else get R j.
Proof. intros R r j H; exact (@get_tab (length R) (fun k => if Nat.eqb k r then Nat.pred (get R k) else get R k) j H). Qed.
Lemma get_affine : forall R r c d j, j < length R ->
  get (affine R r c d) j =
  if Nat.eqb j r then get d j else get R j + get R r * get c j + get d j.
Proof. intros R r c d j H; exact (@get_tab (length R) (fun k => if Nat.eqb k r then get d k else get R k + get R r * get c k + get d k) j H). Qed.
Lemma affine_zero : forall R r c d, get R r = 0 -> plus R d = affine R r c d.
Proof.
 intros R r c d Z; apply regs_ext; [rewrite plus_length, affine_length; reflexivity|].
 intros j J; rewrite plus_length in J; rewrite get_plus, get_affine by auto.
 destruct (Nat.eqb j r) eqn:E; [apply Nat.eqb_eq in E; subst; rewrite Z; simpl; auto|].
 rewrite Z; simpl; lia.
Qed.
Lemma body_count : forall R r c n, r < length R -> get c r = 0 ->
  get R r = S n -> get (plus (dec R r) c) r = n.
Proof.
 intros; rewrite get_plus by (rewrite dec_length; auto).
 rewrite get_dec by auto. rewrite Nat.eqb_refl, H0, H1; simpl; lia.
Qed.
Lemma affine_body : forall R r c d n, r < length R -> get c r = 0 ->
 get R r = S n -> affine (plus (dec R r) c) r c d = affine R r c d.
Proof.
 intros R r c d n Hr Hc Hn; apply regs_ext.
 - repeat rewrite affine_length; rewrite plus_length, dec_length; reflexivity.
 - intros j J. rewrite affine_length, plus_length, dec_length in J.
   rewrite !get_affine by (try rewrite plus_length, dec_length; auto).
   destruct (Nat.eqb j r) eqn:E; auto.
   rewrite get_plus by (rewrite dec_length; auto).
   rewrite get_dec by auto; rewrite E.
   rewrite (@body_count R r c n Hr Hc Hn), Hn; nia.
Qed.
Inductive node := Stop | Test (r : nat) (nz : N) (c : regs) (z : N) (d : regs).
Definition graph := N -> node.
Definition config := (N * regs)%type.
Definition step (G : graph) (s : config) : option config :=
 let '(v,R) := s in
 match G v with
 | Stop => None
 | Test r nz c z d =>
   match get R r with
   | 0 => Some (z, plus R d)
   | S _ => Some (nz, plus (dec R r) c)
   end
 end.
Inductive Run (G : graph) : nat -> config -> config -> Prop :=
 | run_zero : forall s, Run G 0 s s
 | run_step : forall n s t u, step G s = Some t -> Run G n t u -> Run G (S n) s u.
Theorem drain_run : forall G v r c w d R,
 G v = Test r v c w d -> get c r = 0 -> r < length R ->
 Run G (S (get R r)) (v,R) (w,affine R r c d).
Proof.
 intros G v r c w d R Shape NoInc Bound.
 remember (get R r) as n eqn:E; symmetry in E.
 revert R E Bound. induction n as [|n IH]; intros R E Bound.
 - econstructor; [unfold step; rewrite Shape,E; simpl; reflexivity|].
   rewrite (@affine_zero R r c d E). constructor.
 - econstructor; [unfold step; rewrite Shape,E; reflexivity|].
   rewrite <- (@affine_body R r c d n Bound NoInc E).
   apply IH; [eapply body_count; eauto| rewrite plus_length, dec_length; auto].
Qed.

Definition Halts (G : graph) (s : config) :=
 exists n t, Run G n s t /\ step G t = None.
Lemma halts_one : forall G s t, step G s = Some t -> (Halts G s <-> Halts G t).
Proof.
 intros G s t E; split.
 - intros [n [u [H F]]]. inversion H; subst.
   + rewrite E in F; discriminate.
   + match goal with Hs : step _ _ = _ |- _ => rewrite E in Hs; inversion Hs; subst end.
     eexists; eexists; eauto.
 - intros [n [u [H F]]]. exists (S n),u; split; [econstructor; eauto|auto].
Qed.
Lemma halts_run : forall G n s t, Run G n s t -> (Halts G s <-> Halts G t).
Proof. intros G n s t H; induction H; [tauto|]. rewrite (@halts_one G s t H), IHRun; tauto. Qed.
Theorem drain_halts_iff : forall G v r c w d R,
 G v = Test r v c w d -> get c r = 0 -> r < length R ->
 (Halts G (v,R) <-> Halts G (w,affine R r c d)).
Proof. intros; apply halts_run with (n:=S (get R r)); apply drain_run; auto. Qed.

(* The finite checker binds every local certificate to the literal graph. *)
Definition drain_check (G : graph) (v : N) : bool :=
 match G v with
 | Stop => false
 | Test r nz c z d => N.eqb nz v && Nat.eqb (get c r) 0 && Nat.ltb r 9
 end.
Theorem drain_check_sound : forall G v,
 drain_check G v = true ->
 exists r c w d, G v = Test r v c w d /\ get c r = 0 /\ r < 9 /\
 forall R, length R = 9 ->
 Run G (S (get R r)) (v,R) (w,affine R r c d) /\
 (Halts G (v,R) <-> Halts G (w,affine R r c d)).
Proof.
 intros G v H. unfold drain_check in H.
 destruct (G v) as [|r nz c z d] eqn:E; [discriminate|].
 apply andb_true_iff in H as [H B]. apply andb_true_iff in H as [V Z].
 apply N.eqb_eq in V; subst nz. apply Nat.eqb_eq in Z. apply Nat.ltb_lt in B.
 exists r,c,z,d. split; [reflexivity|]. split; [exact Z|]. split; [exact B|].
 intros R L; split.
 - apply drain_run; auto; lia.
 - apply drain_halts_iff; auto; lia.
Qed.
Print Assumptions drain_run.
Print Assumptions drain_halts_iff.
Print Assumptions drain_check_sound.



Lemma run_append : forall G n s t, Run G n s t ->
 forall m u, Run G m t u -> Run G (n+m) s u.
Proof. intros G n s t H; induction H; intros; simpl; auto; econstructor; eauto. Qed.

(* Bounded normalization composes whole drain executions. Every finite fuel
   already preserves halting; ranks prove that six drains suffice to reach core. *)
Fixpoint normalize (fuel : nat) (G : graph) (s : config) : config :=
 match fuel with
 | 0 => s
 | S k =>
   let '(v,R) := s in
   if drain_check G v then
     match G v with
     | Stop => s
     | Test r nz c z d => normalize k G (z,affine R r c d)
     end
   else s
 end.
Theorem normalize_run : forall fuel G v R, length R = 9 ->
 exists n, Run G n (v,R) (normalize fuel G (v,R)) /\
 length (snd (normalize fuel G (v,R))) = 9.
Proof.
 induction fuel as [|fuel IH]; intros G v R L; [exists 0; split; [constructor|exact L]|].
 cbn [normalize]. destruct (drain_check G v) eqn:C.
 - destruct (@drain_check_sound G v C) as [r [c [w [d [E [Z [B P]]]]]]].
   rewrite E. destruct (IH G w (affine R r c d)) as [n [H Len]].
   + rewrite affine_length; exact L.
   + exists (S (get R r)+n); split; [|exact Len].
     apply run_append with (t:=(w,affine R r c d)); [apply drain_run; auto; lia|exact H].
 - exists 0; split; [constructor|exact L].
Qed.
Theorem normalize_halts_iff : forall fuel G v R, length R = 9 ->
 (Halts G (v,R) <-> Halts G (normalize fuel G (v,R))).
Proof. intros; destruct (@normalize_run fuel G v R H) as [n [N L]]. eapply halts_run; eauto. Qed.

Definition rank_ok (G : graph) (rank : N -> nat) :=
 forall v r c z d, G v = Test r v c z d ->
 drain_check G v = true -> rank z < rank v.
Theorem normalize_core : forall fuel G rank, rank_ok G rank ->
 forall v R, rank v <= fuel ->
 drain_check G (fst (normalize fuel G (v,R))) = false.
Proof.
 induction fuel as [|fuel IH]; intros G rank Good v R Bound.
 - cbn [normalize]. destruct (drain_check G v) eqn:C; [|exact C].
   destruct (@drain_check_sound G v C) as [r [c [w [d [E P]]]]].
   specialize (Good v r c w d E C). lia.
 - cbn [normalize]. destruct (drain_check G v) eqn:C; [|exact C].
   destruct (@drain_check_sound G v C) as [r [c [w [d [E P]]]]].
   rewrite E. apply (IH G rank Good).
   specialize (Good v r c w d E C). lia.
Qed.

Fixpoint lookup (v : N) (xs : list (N * node)) : node :=
 match xs with
 | [] => Stop
 | (w,a)::ys => if N.eqb v w then a else lookup v ys
 end.
Lemma lookup_test_in : forall xs v r nz c z d,
 lookup v xs = Test r nz c z d -> In v (map fst xs).
Proof.
 induction xs as [|[w a] xs IH]; intros v r nz c z d H; [discriminate|].
 cbn in H. destruct (N.eqb v w) eqn:E.
 - apply N.eqb_eq in E; subst; simpl; auto.
 - simpl; right; eapply IH; eauto.
Qed.
Definition rank_check (G : graph) (rank : N -> nat) (v : N) :=
 if drain_check G v then
   match G v with Stop => false | Test r nz c z d => Nat.ltb (rank z) (rank v) end
 else true.
Lemma rank_check_sound : forall G rank v r c z d,
 rank_check G rank v = true -> G v = Test r v c z d ->
 drain_check G v = true -> rank z < rank v.
Proof. intros. unfold rank_check in H; rewrite H1,H0 in H. apply Nat.ltb_lt; exact H. Qed.
Theorem rank_list_sound : forall xs rank,
 forallb (rank_check (fun v => lookup v xs) rank) (map fst xs) = true ->
 rank_ok (fun v => lookup v xs) rank.
Proof.
 intros xs rank H v r c z d E C.
 apply forallb_forall with (x:=v) in H; [eapply rank_check_sound; eauto|].
 eapply lookup_test_in; eauto.
Qed.
Print Assumptions normalize_halts_iff.
Print Assumptions normalize_core.
Print Assumptions rank_list_sound.

