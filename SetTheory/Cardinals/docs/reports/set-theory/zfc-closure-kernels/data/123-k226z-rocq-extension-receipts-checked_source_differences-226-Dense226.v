(** Exact compaction of the verified sparse-label runtime to 226 working states.
    The state type here is bnat 226: 0..228 work, 226 halts.  There is no
    extra unreachable state in this dense presentation. *)
From Coq Require Import Lists.List Lists.Streams Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From K226F Require Import TM230 Table226.
Import ListNotations.

Module Sparse := K226F.TM230.TM230.

Module Ctx226 <: Ctx.
  Definition Q := bnat 226.
  Definition Sym := bool.
  Definition q0 := bmk 226 0.
  Definition s0 := false.
  Definition q1 := bmk 226 1.
  Lemma q0_neq_q1 : q0 <> q1.
  Proof. intros H. apply (f_equal bval) in H. vm_compute in H. discriminate. Qed.
  Definition s1 := true.
  Lemma s0_neq_s1 : s0 <> s1. Proof. discriminate. Qed.
  Definition eqb_q : forall a b : Q, {a = b} + {a <> b} := bnat_dec.
  Definition eqb_sym := bool_dec.
  Definition all_qs := ball 226.
  Definition all_qs_spec := ball_spec 226.
  Definition all_syms := [false; true].
  Lemma all_syms_spec : forall a, In a all_syms.
  Proof. intros []; simpl; tauto. Qed.
End Ctx226.

Module Dense := TM.TM Ctx226.

Definition dense_tmn (q : nat) (b : bool) : option (bool * dir * nat) :=
  match nth_error table226 q with
  | None => None
  | Some (w0, d0, n0, w1, d1, n1) =>
      if b then Some (w1, d1, n1) else Some (w0, d0, n0)
  end.

Definition dense_tm : Dense.TM := fun '(q,b) =>
  match dense_tmn (bval q) b with
  | None => None
  | Some (w,d,n) => Some (w,d,bmk 226 n)
  end.

Definition expand (q : nat) :=
  if Nat.ltb q 65 then q else
  if Nat.ltb q 78 then S (q) else
  if Nat.ltb q 138 then S (S (q)) else
  if Nat.ltb q 172 then S (S (S (q))) else S (S (S (S (q)))).
Definition decode_state (q : Ctx226.Q) : Ctx230.Q := st (expand (bval q)).
Definition bool_tape := (Stream bool * bool * Stream bool)%type.
Definition decode_conf (c : Ctx226.Q * bool_tape) : Ctx230.Q * bool_tape :=
  let '(q,t) := c in (decode_state q,t).

Lemma dense_working_rows : length table226 = 226.
Proof. reflexivity. Qed.

Lemma dense_targets_ok :
  forallb (fun '(_,_,n0,_,_,n1) => andb (Nat.leb n0 226) (Nat.leb n1 226)) table226 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dense_terminal b : dense_tm (bmk 226 226,b) = None.
Proof. reflexivity. Qed.

(** This is a total transition identity, including the terminal state.
    Its finite proof checks all 230 states and both symbols. *)
Lemma transition_commutes (q : Ctx226.Q) b :
  tm (decode_state q,b) =
  match dense_tm (q,b) with
  | None => None
  | Some (w,d,q') => Some (w,d,decode_state q')
  end.
Proof.
  destruct q as [n Hn].
  assert (Hle : n <= 226) by (apply Nat.leb_le; exact Hn).
  do 227 (destruct n as [|n]; [destruct b; vm_compute; reflexivity|]).
  lia.
Qed.

Lemma decode_initial : decode_conf Dense.c0 = Sparse.c0.
Proof. reflexivity. Qed.

Lemma dense_step_sparse c c' :
  Dense.step dense_tm c c' -> Sparse.step tm (decode_conf c) (decode_conf c').
Proof.
  intros H. destruct H as [q q' s s' l r E | q q' s s' l r E].
  - apply Sparse.step_left. rewrite transition_commutes.
    exact (f_equal (fun a => match a with None => None | Some (w,d,z) => Some (w,d,decode_state z) end) E).
  - apply Sparse.step_right. rewrite transition_commutes.
    exact (f_equal (fun a => match a with None => None | Some (w,d,z) => Some (w,d,decode_state z) end) E).
Qed.

Lemma dense_halted_sparse c :
  Dense.halted dense_tm c -> Sparse.halted tm (decode_conf c).
Proof.
  destruct c as [q [[l b] r]].
  change (dense_tm (q,b) = None -> tm (decode_state q,b) = None).
  rewrite transition_commutes. intros E.
  exact (f_equal (fun a => match a with None => None | Some (w,d,z) => Some (w,d,decode_state z) end) E).
Qed.

Lemma dense_multistep_sparse n c c' :
  Dense.multistep dense_tm n c c' ->
  Sparse.multistep tm n (decode_conf c) (decode_conf c').
Proof.
  intros H. induction H.
  - constructor.
  - eapply Sparse.multistep_S; [apply dense_step_sparse; exact H | exact IHmultistep].
Qed.

Lemma dense_halts_sparse :
  Dense.halts dense_tm Dense.c0 -> Sparse.halts tm Sparse.c0.
Proof.
  intros (n & c & Hr & Hh). exists n, (decode_conf c). split.
  - rewrite <- decode_initial. apply dense_multistep_sparse, Hr.
  - apply dense_halted_sparse, Hh.
Qed.

Lemma dense_next c :
  Dense.halted dense_tm c \/ exists c', Dense.step dense_tm c c'.
Proof.
  destruct c as [q [[l b] r]].
  destruct (dense_tm (q,b)) as [[[w d] q']|] eqn:E.
  - right. destruct d.
    + eexists. eapply Dense.step_left. exact E.
    + eexists. eapply Dense.step_right. exact E.
  - left. exact E.
Qed.

(** No inverse-state axiom or excluded-middle assumption is used.  The
    finite transition identity lifts each dense step and reflects stopping. *)
Lemma sparse_halts_dense :
  Sparse.halts tm Sparse.c0 -> Dense.halts dense_tm Dense.c0.
Proof.
  intros HH.
  set (P := fun c : Ctx230.Q * bool_tape =>
      exists d, c = decode_conf d /\ Dense.evstep dense_tm Dense.c0 d).
  destruct (Sparse.progress_halts tm P
      (fun _ => Dense.halts dense_tm Dense.c0) Sparse.c0) as (c & _ & HZ).
  - intros c [d [-> Hr]].
    destruct (dense_next d) as [Hh | (d' & Hs)].
    + left. exact (Dense.halted_evstep_halts dense_tm Dense.c0 d Hr Hh).
    + right. exists (decode_conf d'). split.
      * exists d'. split; [reflexivity|].
        eapply Dense.evstep_trans; [exact Hr|].
        eapply Dense.evstep_step; [exact Hs|constructor].
      * apply Sparse.progress_base. apply dense_step_sparse, Hs.
  - exists Dense.c0. split; [reflexivity|constructor].
  - exact HH.
  - exact HZ.
Qed.

Theorem dense_sparse_halts_iff :
  Dense.halts dense_tm Dense.c0 <-> Sparse.halts tm Sparse.c0.
Proof. split; [exact dense_halts_sparse | exact sparse_halts_dense]. Qed.

Print Assumptions dense_sparse_halts_iff.
