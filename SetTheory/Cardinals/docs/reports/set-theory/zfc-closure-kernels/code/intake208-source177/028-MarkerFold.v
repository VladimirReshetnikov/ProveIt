(** A finite certificate for an opposite-marker state fold.
    New generic checker and soundness theorem, 2026-10-21.
    The local two-marker argument generalizes the M124 and FM215 proofs in
    ProveIt's incoming packets. Machine tables and their authorship are
    inherited; see NOTICE.md. No functional-extensionality axiom is used. *)
From Coq Require Import ZArith Bool Arith Lia Lists.List.
Import ListNotations.
Open Scope Z_scope.

Record instr := I { out : bool; right : bool; target : nat }.
Definition table := list (option instr * option instr).
Definition row (T : table) (q : nat) (bit : bool) :=
  let p := nth q T (None,None) in if bit then snd p else fst p.
Definition eqI (a b : instr) := Bool.eqb (out a) (out b) &&
  Bool.eqb (right a) (right b) && Nat.eqb (target a) (target b).
Definition eqO (a b : option instr) := match a,b with
  | None,None => true | Some a,Some b => eqI a b | _,_ => false end.
Lemma eqO_sound a b : eqO a b = true -> a=b.
Proof.
  destruct a as [[w d q]|], b as [[w' d' q']|]; cbn; try discriminate; auto.
  unfold eqI; cbn. rewrite !andb_true_iff, !Bool.eqb_true_iff, Nat.eqb_eq.
  intros [[-> ->] ->]. reflexivity.
Qed.
Lemma row_above T q bit : (length T <= q)%nat -> row T q bit=None.
Proof. intros H. unfold row. rewrite nth_overflow by exact H.
  destruct bit; reflexivity. Qed.
Definition finite_rows (T : table) (P : nat -> bool -> bool) :=
  forallb (fun q => P q false && P q true) (seq 0 (length T)).
Lemma finite_rows_sound T P q bit : (q < length T)%nat ->
  finite_rows T P = true -> P q bit = true.
Proof.
  intros B H. unfold finite_rows in H.
  apply forallb_forall with (x:=q) in H.
  - apply andb_true_iff in H. destruct bit; tauto.
  - apply in_seq. lia.
Qed.

Definition tape := Z -> bool.
(* Sharing a no-op write makes whole-tape equality constructive. *)
Definition put (t : tape) (h : Z) (bit : bool) : tape :=
  if Bool.eqb bit (t h) then t
  else fun x => if Z.eqb x h then bit else t x.
Lemma put_same t h : put t h (t h)=t.
Proof. unfold put; destruct (t h); reflexivity. Qed.
Lemma put_here t h bit : put t h bit h=bit.
Proof. unfold put. destruct bit; destruct (t h) eqn:E;
  cbn; rewrite ?Z.eqb_refl; auto. Qed.
Lemma put_standard t h bit x :
  put t h bit x = if Z.eqb x h then bit else t x.
Proof.
  unfold put. destruct (Bool.eqb bit (t h)) eqn:E; [|reflexivity].
  rewrite Bool.eqb_true_iff in E. destruct (Z.eqb x h) eqn:X; [|reflexivity].
  apply Z.eqb_eq in X. subst x. symmetry. exact E.
Qed.
Definition displacement (r : bool) : Z := if r then 1 else -1.
Record config := C { state : nat; head : Z; cells : tape }.
Definition applyI (i : instr) (c : config) :=
  C (target i) (head c + displacement (right i))
    (put (cells c) (head c) (out i)).
Definition step T c := match row T (state c) (cells c (head c)) with
  | Some i => applyI i c | None => c end.
Fixpoint run T (n : nat) c :=
  match n with 0%nat => c | S n => step T (run T n c) end.
Definition Halts (T : table) (halt : nat) c :=
  exists n, state (run T n c)=halt.
Lemma run_add T n m c : run T (n+m) c=run T m (run T n c).
Proof. induction m; [rewrite Nat.add_0_r; reflexivity|].
  rewrite Nat.add_succ_r; cbn; now rewrite IHm. Qed.
Lemma preserved_step T q h t r z :
  row T q (t h)=Some (I (t h) r z) ->
  step T (C q h t)=C z (h+displacement r) t.
Proof.
  intro E. unfold step; cbn [state cells head]. rewrite E.
  change (C z (h+displacement r) (put t h (t h))=C z (h+displacement r) t).
  now rewrite put_same.
Qed.

Section Fold.
Variable O N : table.
Variables a b halt u v w r0 r1 : nat.
Definition phi q := if Nat.eqb q b then a else q.
Definition mapI i := I (out i) (right i) (phi (target i)).
Definition incoming_check q bit := match row O q bit with
  | None => true
  | Some i =>
      (if Nat.eqb (target i) a then out i && right i else true) &&
      (if Nat.eqb (target i) b then negb (out i) && right i else true)
  end.
Definition outer_check q bit :=
  if (Nat.eqb q a || Nat.eqb q b)%bool then true
  else eqO (row N (phi q) bit) (option_map mapI (row O q bit)).
Definition shape_check :=
  eqO (row O a false) (Some (I false true u)) &&
  eqO (row O b false) (Some (I false true v)) &&
  eqO (row O a true) (Some (I true true w)) &&
  eqO (row O b true) (Some (I true true w)) &&
  eqO (row N a false) (Some (I false false b)) &&
  eqO (row N a true) (Some (I true true (phi w))) &&
  eqO (row N b false) (Some (I false true r0)) &&
  eqO (row N b true) (Some (I true true r1)) &&
  eqO (row N r0 false) (Some (I false true (phi v))) &&
  eqO (row N r1 false) (Some (I false true (phi u))) &&
  eqO (row N halt false) None && eqO (row N halt true) None.
Definition check :=
  Nat.eqb (length O) (length N) &&
  negb (Nat.eqb a 0) && negb (Nat.eqb b 0) &&
  negb (Nat.eqb a b) &&
  negb (Nat.eqb a halt) && negb (Nat.eqb b halt) &&
  finite_rows O incoming_check && finite_rows O outer_check && shape_check.

Record Contract : Prop := {
  lengths : length O=length N;
  nonzero_a : a<>0%nat; nonzero_b : b<>0%nat; distinct : a<>b;
  halt_a : a<>halt; halt_b : b<>halt;
  incoming_finite : finite_rows O incoming_check=true;
  outer_finite : finite_rows O outer_check=true;
  old_a0 : row O a false=Some (I false true u);
  old_b0 : row O b false=Some (I false true v);
  old_a1 : row O a true=Some (I true true w);
  old_b1 : row O b true=Some (I true true w);
  new_a0 : row N a false=Some (I false false b);
  new_a1 : row N a true=Some (I true true (phi w));
  new_b0 : row N b false=Some (I false true r0);
  new_b1 : row N b true=Some (I true true r1);
  new_r0 : row N r0 false=Some (I false true (phi v));
  new_r1 : row N r1 false=Some (I false true (phi u));
  new_h0 : row N halt false=None; new_h1 : row N halt true=None
}.
Lemma check_sound : check=true -> Contract.
Proof.
  unfold check,shape_check. rewrite !andb_true_iff.
  rewrite Nat.eqb_eq, !negb_true_iff, !Nat.eqb_neq.
  intros H. repeat match goal with H : _ /\ _ |- _ => destruct H end.
  constructor; try assumption; apply eqO_sound; assumption.
Qed.

Variable cert : Contract.
Lemma incoming q bit i : row O q bit=Some i ->
  (target i=a -> out i=true /\ right i=true) /\
  (target i=b -> out i=false /\ right i=true).
Proof.
  intro E. destruct (Nat.lt_ge_cases q (length O)) as [L|L].
  - pose proof (finite_rows_sound O incoming_check q bit L
      (incoming_finite cert)) as H.
    unfold incoming_check in H. rewrite E in H.
    apply andb_true_iff in H. destruct H as [A B]. split; intro Q.
    + rewrite Q,Nat.eqb_refl in A. now apply andb_true_iff in A.
    + rewrite Q,Nat.eqb_refl in B. apply andb_true_iff in B.
      destruct B as [B D]. apply negb_true_iff in B. auto.
  - rewrite row_above in E by lia. discriminate.
Qed.
Lemma outer q bit : q<>a -> q<>b ->
  row N (phi q) bit=option_map mapI (row O q bit).
Proof.
  intros A B. destruct (Nat.lt_ge_cases q (length O)) as [L|L].
  - pose proof (finite_rows_sound O outer_check q bit L
      (outer_finite cert)) as H.
    unfold outer_check in H.
    assert (X : Nat.eqb q a=false) by now apply Nat.eqb_neq.
    assert (Y : Nat.eqb q b=false) by now apply Nat.eqb_neq.
    rewrite X,Y in H. cbn in H. now apply eqO_sound.
  - assert (Y : Nat.eqb q b=false) by now apply Nat.eqb_neq.
    unfold phi. rewrite Y.
    rewrite (row_above O q bit L).
    rewrite row_above; [reflexivity|rewrite <- (lengths cert); lia].
Qed.
Definition lift c := C (phi (state c)) (head c) (cells c).
Definition Inv c :=
  (state c=a -> cells c (head c-1)=true) /\
  (state c=b -> cells c (head c-1)=false).
Lemma phi_a : phi a=a.
Proof. unfold phi. rewrite (proj2 (Nat.eqb_neq a b) (distinct cert)). reflexivity. Qed.
Lemma phi_b : phi b=a.
Proof. unfold phi. now rewrite Nat.eqb_refl. Qed.
Lemma Inv_start h t : Inv (C 0 h t).
Proof. unfold Inv; cbn. split; intro E;
  [exfalso; apply (nonzero_a cert)|exfalso; apply (nonzero_b cert)]; auto. Qed.
Lemma Inv_step c : Inv c -> Inv (step O c).
Proof.
  intros H. unfold step. destruct (row O (state c) (cells c (head c)))
    as [i|] eqn:E; [|exact H].
  destruct (incoming _ _ _ E) as [A B].
  unfold Inv,applyI; cbn. split; intro Q.
  - destruct (A Q) as [W D]. rewrite W,D. cbn [displacement].
    replace (head c+1-1) with (head c) by lia. apply put_here.
  - destruct (B Q) as [W D]. rewrite W,D. cbn [displacement].
    replace (head c+1-1) with (head c) by lia. apply put_here.
Qed.
Lemma Inv_run c n : Inv c -> Inv (run O n c).
Proof. intros H; induction n; cbn; auto using Inv_step. Qed.
Lemma outer_step c : state c<>a -> state c<>b ->
  step N (lift c)=lift (step O c).
Proof.
  intros A B. unfold step at 1. unfold lift at 1; cbn.
  rewrite (outer _ _ A B). unfold step.
  destruct (row O (state c) (cells c (head c))); reflexivity.
Qed.

Lemma zero_block h t : t h=false ->
  run N 3 (C a h t)=
    C (if t (h-1) then phi u else phi v) (h+1) t.
Proof.
  intro E.
  assert (N1 : step N (C a h t)=C b (h-1) t).
  { replace (h-1) with (h+displacement false) by (cbn;lia).
    apply preserved_step with (r:=false). rewrite E. exact (new_a0 cert). }
  destruct (t (h-1)) eqn:B.
  - assert (N2 : step N (C b (h-1) t)=C r1 h t).
    { replace h with ((h-1)+displacement true) at 2 by (cbn;lia).
      apply preserved_step with (r:=true). rewrite B. exact (new_b1 cert). }
    assert (N3 : step N (C r1 h t)=C (phi u) (h+1) t).
    { apply preserved_step with (r:=true). rewrite E. exact (new_r1 cert). }
    cbn [run]. now rewrite N1,N2,N3.
  - assert (N2 : step N (C b (h-1) t)=C r0 h t).
    { replace h with ((h-1)+displacement true) at 2 by (cbn;lia).
      apply preserved_step with (r:=true). rewrite B. exact (new_b0 cert). }
    assert (N3 : step N (C r0 h t)=C (phi v) (h+1) t).
    { apply preserved_step with (r:=true). rewrite E. exact (new_r0 cert). }
    cbn [run]. now rewrite N1,N2,N3.
Qed.
Lemma exceptional qa h t : (qa=a \/ qa=b) -> Inv (C qa h t) ->
  exists d, (1<=d<=3)%nat /\ run N d (lift (C qa h t))=lift (step O (C qa h t)).
Proof.
  intros Q H. destruct Q as [Q|Q]; subst qa.
  - destruct (t h) eqn:E.
    + exists 1%nat; split; [lia|].
      assert (A : step O (C a h t)=C w (h+1) t).
      { apply preserved_step with (r:=true). rewrite E. exact (old_a1 cert). }
      assert (B : step N (C a h t)=C (phi w) (h+1) t).
      { apply preserved_step with (r:=true). rewrite E. exact (new_a1 cert). }
      change (step N (C (phi a) h t)=lift (step O (C a h t))).
      rewrite phi_a,A,B. reflexivity.
    + exists 3%nat; split; [lia|].
      assert (A : step O (C a h t)=C u (h+1) t).
      { apply preserved_step with (r:=true). rewrite E. exact (old_a0 cert). }
      change (run N 3 (C (phi a) h t)=lift (step O (C a h t))).
      rewrite phi_a,zero_block by exact E.
      unfold Inv in H; cbn in H. rewrite (proj1 H eq_refl),A. reflexivity.
  - destruct (t h) eqn:E.
    + exists 1%nat; split; [lia|].
      assert (A : step O (C b h t)=C w (h+1) t).
      { apply preserved_step with (r:=true). rewrite E. exact (old_b1 cert). }
      assert (B : step N (C a h t)=C (phi w) (h+1) t).
      { apply preserved_step with (r:=true). rewrite E. exact (new_a1 cert). }
      change (step N (C (phi b) h t)=lift (step O (C b h t))).
      rewrite phi_b,A,B. reflexivity.
    + exists 3%nat; split; [lia|].
      assert (A : step O (C b h t)=C v (h+1) t).
      { apply preserved_step with (r:=true). rewrite E. exact (old_b0 cert). }
      change (run N 3 (C (phi b) h t)=lift (step O (C b h t))).
      rewrite phi_b,zero_block by exact E.
      unfold Inv in H; cbn in H. rewrite (proj2 H eq_refl),A. reflexivity.
Qed.
Lemma local_simulation c : Inv c ->
  exists d, (1<=d<=3)%nat /\ run N d (lift c)=lift (step O c).
Proof.
  intro H. destruct (Nat.eq_dec (state c) a) as [A|A].
  - destruct c. apply exceptional; auto.
  - destruct (Nat.eq_dec (state c) b) as [B|B].
    + destruct c. apply exceptional; auto.
    + exists 1%nat; split; [lia|]. now apply outer_step.
Qed.
Theorem timed_simulation c n : Inv c ->
  exists m, (n<=m<=3*n)%nat /\ run N m (lift c)=lift (run O n c).
Proof.
  intro H; induction n as [|n [m [B E]]].
  - exists 0%nat; split; [lia|reflexivity].
  - destruct (local_simulation (run O n c) (Inv_run c n H)) as [d [D F]].
    exists (m+d)%nat; split; [lia|]. rewrite run_add,E. exact F.
Qed.
Lemma phi_halt q : phi q=halt <-> q=halt.
Proof.
  unfold phi. destruct (Nat.eqb q b) eqn:E.
  - apply Nat.eqb_eq in E. subst q. split; intro H;
    [exfalso; exact (halt_a cert H)|exfalso; exact (halt_b cert H)].
  - tauto.
Qed.
Lemma halt_step c : state c=halt -> step N c=c.
Proof.
  intro H. unfold step. rewrite H. destruct (cells c (head c));
    [rewrite (new_h1 cert)|rewrite (new_h0 cert)]; reflexivity.
Qed.
Lemma halt_run c n : state c=halt -> state (run N n c)=halt.
Proof. intro H. induction n; cbn; [exact H|].
  rewrite (halt_step _ IHn); exact IHn. Qed.
Lemma halt_stable c n m : (n<=m)%nat ->
  state (run N n c)=halt -> state (run N m c)=halt.
Proof. intros B E. replace m with (n+(m-n))%nat by lia.
  rewrite run_add. now apply halt_run. Qed.
Theorem invariant_equihalting c : Inv c ->
  (Halts O halt c <-> Halts N halt (lift c)).
Proof.
  intro H; split; intros [n E].
  - destruct (timed_simulation c n H) as [m [B F]]. exists m.
    rewrite F. cbn [lift state]. now apply phi_halt.
  - destruct (timed_simulation c n H) as [m [B F]]. exists n.
    assert (G : state (run N m (lift c))=halt).
    { eapply halt_stable; [apply B|exact E]. }
    rewrite F in G. change (phi (state (run O n c))=halt) in G.
    exact (proj1 (phi_halt _) G).
Qed.
Theorem all_tapes_equihalting h t :
  Halts O halt (C 0 h t) <-> Halts N halt (C 0 h t).
Proof.
  pose proof (invariant_equihalting (C 0 h t) (Inv_start h t)) as H.
  change (Halts O halt (C 0 h t) <-> Halts N halt (C (phi 0) h t)) in H.
  assert (B : Nat.eqb 0 b=false) by (apply Nat.eqb_neq; intro E;
    apply (nonzero_b cert); auto).
  assert (P : phi 0=0%nat) by (unfold phi; now rewrite B).
  now rewrite P in H.
Qed.
End Fold.

Theorem checked_fold O N a b halt u v w r0 r1 :
  check O N a b halt u v w r0 r1=true -> forall h t,
  Halts O halt (C 0 h t) <-> Halts N halt (C 0 h t).
Proof. intro H. apply all_tapes_equihalting with
  (a:=a) (b:=b) (u:=u) (v:=v) (w:=w) (r0:=r0) (r1:=r1).
  now apply check_sound. Qed.

Print Assumptions checked_fold.
Print Assumptions timed_simulation.
