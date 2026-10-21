From Coq Require Import ZArith Bool Arith Lia Lists.List.
Require Import M124Table M124Facts.
Open Scope Z_scope.

Definition tape := Z -> bool.
(* Avoid function extensionality: a write of the current symbol is definitionally
   shared with the old tape, while a changed symbol uses ordinary point update. *)
Definition put (t : tape) (h : Z) (b : bool) : tape :=
  if Bool.eqb b (t h) then t
  else fun x => if Z.eqb x h then b else t x.

Lemma put_same t h : put t h (t h) = t.
Proof. unfold put; destruct (t h); reflexivity. Qed.

Lemma put_here t h b : put t h b h = b.
Proof.
  unfold put. destruct b; destruct (t h) eqn:E; cbn; rewrite ?Z.eqb_refl; auto.
Qed.

Lemma put_standard t h b x :
  put t h b x = if Z.eqb x h then b else t x.
Proof.
  unfold put. destruct (Bool.eqb b (t h)) eqn:E; [|reflexivity].
  rewrite Bool.eqb_true_iff in E.
  destruct (Z.eqb x h) eqn:X; [|reflexivity].
  apply Z.eqb_eq in X. subst x. symmetry. exact E.
Qed.

Record config := C { state : nat; head : Z; cells : tape }.
Definition applyI (i : instr) (c : config) :=
  C (target i) (head c + delta i) (put (cells c) (head c) (out i)).
Definition step (T : table) (c : config) :=
  match T (state c) (cells c (head c)) with
  | Some i => applyI i c
  | None => c
  end.
Fixpoint run (T : table) (n : nat) (c : config) :=
  match n with 0%nat => c | S n => step T (run T n c) end.
Definition lift (c : config) := C (phi (state c)) (head c) (cells c).
Definition Inv (c : config) :=
  (state c = 124%nat -> cells c (head c - 1) = true) /\
  (state c = 127%nat -> cells c (head c - 1) = false).
Definition Halts (T : table) (c : config) :=
  exists n, state (run T n c) = 254%nat.

Lemma Inv_start h t : Inv (C 0 h t).
Proof. unfold Inv; cbn; split; discriminate. Qed.

Lemma Inv_step c : Inv c -> Inv (step K c).
Proof.
  intros H. unfold step.
  destruct (K (state c) (cells c (head c))) as [i|] eqn:E; [|exact H].
  unfold Inv, applyI; cbn. split; intros Q.
  - destruct (K_incoming124 _ _ _ E Q) as [W D].
    rewrite W,D. replace (head c + 1 - 1) with (head c) by lia.
    apply put_here.
  - destruct (K_incoming127 _ _ _ E Q) as [W D].
    rewrite W,D. replace (head c + 1 - 1) with (head c) by lia.
    apply put_here.
Qed.

Lemma Inv_run c n : Inv c -> Inv (run K n c).
Proof. intros H; induction n; cbn; auto using Inv_step. Qed.

Lemma lift_apply i c : lift (applyI i c) = applyI (mapI i) (lift c).
Proof. reflexivity. Qed.

Lemma outer_step c : state c <> 124%nat -> state c <> 127%nat ->
  step M (lift c) = lift (step K c).
Proof.
  intros A B. unfold step at 1. unfold lift at 1; cbn.
  rewrite (K_M_outer _ _ A B).
  unfold step. destruct (K (state c) (cells c (head c))); reflexivity.
Qed.

Lemma preserved_step T q h t d r :
  T q (t h) = Some (I (t h) d r) ->
  step T (C q h t) = C r (h+d) t.
Proof.
  intros E. unfold step; cbn [state head cells]. rewrite E.
  change (C r (h+d) (put t h (t h)) = C r (h+d) t).
  now rewrite put_same.
Qed.

Lemma exceptional124 h t : t (h-1)=true ->
  exists d, (1 <= d <= 3)%nat /\
    run M d (lift (C 124 h t)) = lift (step K (C 124 h t)).
Proof.
  intros L. destruct (t h) eqn:B.
  - exists 1%nat; split; [lia|].
    assert (O : step K (C 124 h t) = C 138 (h+1) t).
    { apply preserved_step. rewrite B. reflexivity. }
    assert (N : step M (C 124 h t) = C 138 (h+1) t).
    { apply preserved_step. rewrite B. reflexivity. }
    change (step M (C 124 h t) = lift (step K (C 124 h t))).
    rewrite O,N. reflexivity.
  - exists 3%nat; split; [lia|].
    assert (O : step K (C 124 h t) = C 62 (h+1) t).
    { apply preserved_step. rewrite B. reflexivity. }
    assert (N1 : step M (C 124 h t) = C 127 (h-1) t).
    { replace (h-1) with (h+(-1)) by lia.
      apply preserved_step. rewrite B. reflexivity. }
    assert (N2 : step M (C 127 (h-1) t) = C 59 h t).
    { replace h with ((h-1)+1) at 2 by lia.
      apply preserved_step. rewrite L. reflexivity. }
    assert (N3 : step M (C 59 h t) = C 62 (h+1) t).
    { apply preserved_step. rewrite B. reflexivity. }
    change (step M (step M (step M (C 124 h t))) =
      lift (step K (C 124 h t))).
    rewrite N1,N2,N3,O. reflexivity.
Qed.

Lemma exceptional127 h t : t (h-1)=false ->
  exists d, (1 <= d <= 3)%nat /\
    run M d (lift (C 127 h t)) = lift (step K (C 127 h t)).
Proof.
  intros L. destruct (t h) eqn:B.
  - exists 1%nat; split; [lia|].
    assert (O : step K (C 127 h t) = C 138 (h+1) t).
    { apply preserved_step. rewrite B. reflexivity. }
    assert (N : step M (C 124 h t) = C 138 (h+1) t).
    { apply preserved_step. rewrite B. reflexivity. }
    change (step M (C 124 h t) = lift (step K (C 127 h t))).
    rewrite O,N. reflexivity.
  - exists 3%nat; split; [lia|].
    assert (O : step K (C 127 h t) = C 14 (h+1) t).
    { apply preserved_step. rewrite B. reflexivity. }
    assert (N1 : step M (C 124 h t) = C 127 (h-1) t).
    { replace (h-1) with (h+(-1)) by lia.
      apply preserved_step. rewrite B. reflexivity. }
    assert (N2 : step M (C 127 (h-1) t) = C 8 h t).
    { replace h with ((h-1)+1) at 2 by lia.
      apply preserved_step. rewrite L. reflexivity. }
    assert (N3 : step M (C 8 h t) = C 14 (h+1) t).
    { apply preserved_step. rewrite B. reflexivity. }
    change (step M (step M (step M (C 124 h t))) =
      lift (step K (C 127 h t))).
    rewrite N1,N2,N3,O. reflexivity.
Qed.

Lemma local_simulation c : Inv c ->
  exists d, (1 <= d <= 3)%nat /\ run M d (lift c) = lift (step K c).
Proof.
  intros [A B]. destruct c as [q h t]; cbn in *.
  destruct (Nat.eq_dec q 124) as [E|E].
  - subst q. apply exceptional124. auto.
  - destruct (Nat.eq_dec q 127) as [F|F].
    + subst q. apply exceptional127. auto.
    + exists 1%nat; split; [lia|]. apply outer_step; assumption.
Qed.

Lemma run_add T n m c : run T (n+m) c = run T m (run T n c).
Proof. induction m; [rewrite Nat.add_0_r; reflexivity|].
  rewrite Nat.add_succ_r; cbn; now rewrite IHm.
Qed.

Theorem timed_simulation c n : Inv c ->
  exists m, (n <= m <= 3*n)%nat /\
    run M m (lift c) = lift (run K n c).
Proof.
  intros H; induction n as [|n [m [Hbound Heq]]].
  - exists 0%nat; split; [lia|reflexivity].
  - destruct (local_simulation (run K n c) (Inv_run c n H)) as [d [Hd Ed]].
    exists (m+d)%nat; split; [lia|]. rewrite run_add, Heq. exact Ed.
Qed.

Lemma phi_halt q : phi q = 254%nat <-> q = 254%nat.
Proof.
  unfold phi. destruct (Nat.eqb q 127) eqn:E.
  - apply Nat.eqb_eq in E. subst q. split; discriminate.
  - tauto.
Qed.

Lemma M_halt_step c : state c = 254%nat -> step M c = c.
Proof. destruct c as [q h t]; cbn; intros E; subst q.
  unfold step; cbn [state cells head M K]. destruct (t h); reflexivity.
Qed.

Lemma M_halt_run c n : state c = 254%nat -> state (run M n c)=254%nat.
Proof.
  intros E; induction n; cbn; [exact E|].
  rewrite (M_halt_step _ IHn). exact IHn.
Qed.

Lemma M_halt_stable c n m : (n <= m)%nat -> state (run M n c) = 254%nat ->
  state (run M m c) = 254%nat.
Proof.
  intros H E. assert (D : m=(n+(m-n))%nat) by lia. rewrite D,run_add.
  now apply M_halt_run.
Qed.

Theorem invariant_equihalting c : Inv c -> (Halts K c <-> Halts M (lift c)).
Proof.
  intros H; split.
  - intros [n E]. destruct (timed_simulation c n H) as [m [B Q]].
    exists m. rewrite Q. cbn [lift]. apply phi_halt. exact E.
  - intros [n E]. destruct (timed_simulation c n H) as [m [B Q]].
    exists n. assert (F : state (run M m (lift c))=254%nat).
    { eapply M_halt_stable; [apply B|exact E]. }
    rewrite Q in F. change (phi (state (run K n c)) = 254%nat) in F.
    exact (proj1 (phi_halt _) F).
Qed.

Theorem all_tapes_equihalting h t :
  Halts K (C 0 h t) <-> Halts M (C 0 h t).
Proof. apply (invariant_equihalting (C 0 h t) (Inv_start h t)). Qed.

Corollary blank_nonhalting_iff :
  ~ Halts K (C 0 0 (fun _ => false)) <->
  ~ Halts M (C 0 0 (fun _ => false)).
Proof. pose proof (all_tapes_equihalting 0 (fun _=>false)); tauto. Qed.

Corollary calibration_transfer (P : Prop) :
  (~ Halts K (C 0 0 (fun _=>false)) <-> P) ->
  (~ Halts M (C 0 0 (fun _=>false)) <-> P).
Proof. pose proof blank_nonhalting_iff. tauto. Qed.

Print Assumptions all_tapes_equihalting.
Print Assumptions blank_nonhalting_iff.
Print Assumptions calibration_transfer.
