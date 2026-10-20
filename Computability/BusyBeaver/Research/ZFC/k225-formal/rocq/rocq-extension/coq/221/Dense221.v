(** Exact relabelling of the verified sparse-label runtime to 221 working states.
    The state type here is bnat 221: 0..220 work, 221 halts.  There is no
    extra unreachable state in this dense presentation. *)
From Coq Require Import Lists.List Lists.Streams Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From K221F Require Import TM230 Table221.
Import ListNotations.

Module Sparse := K221F.TM230.TM230.

Module Ctx221 <: Ctx.
  Definition Q := bnat 221.
  Definition Sym := bool.
  Definition q0 := bmk 221 0.
  Definition s0 := false.
  Definition q1 := bmk 221 1.
  Lemma q0_neq_q1 : q0 <> q1.
  Proof. intros H. apply (f_equal bval) in H. vm_compute in H. discriminate. Qed.
  Definition s1 := true.
  Lemma s0_neq_s1 : s0 <> s1. Proof. discriminate. Qed.
  Definition eqb_q : forall a b : Q, {a = b} + {a <> b} := bnat_dec.
  Definition eqb_sym := bool_dec.
  Definition all_qs := ball 221.
  Definition all_qs_spec := ball_spec 221.
  Definition all_syms := [false; true].
  Lemma all_syms_spec : forall a, In a all_syms.
  Proof. intros []; simpl; tauto. Qed.
End Ctx221.

Module Dense := TM.TM Ctx221.

Definition dense_tmn (q : nat) (b : bool) : option (bool * dir * nat) :=
  match nth_error table221 q with
  | None => None
  | Some (w0, d0, n0, w1, d1, n1) =>
      if b then Some (w1, d1, n1) else Some (w0, d0, n0)
  end.

Definition dense_tm : Dense.TM := fun '(q,b) =>
  match dense_tmn (bval q) b with
  | None => None
  | Some (w,d,n) => Some (w,d,bmk 221 n)
  end.

(** canonical dense index -> K230 label (the public canonical numbering is a BFS order) *)
Definition dense_labels : list nat := [0; 94; 66; 198; 54; 113; 40; 97; 4; 6; 10; 16; 1; 2; 3; 5; 9; 15; 23; 34; 50; 75; 84; 95; 214; 27; 110; 111; 212; 39; 127; 8; 104; 128; 92; 185; 11; 36; 14; 138; 13; 123; 124; 21; 141; 107; 174; 143; 26; 162; 51; 22; 130; 91; 31; 73; 62; 24; 60; 161; 126; 17; 142; 163; 164; 37; 38; 33; 144; 20; 82; 81; 47; 83; 28; 35; 55; 49; 32; 71; 135; 146; 77; 98; 129; 53; 48; 30; 57; 63; 93; 42; 41; 64; 80; 12; 90; 87; 88; 19; 114; 76; 134; 68; 69; 25; 45; 46; 61; 108; 109; 74; 105; 106; 102; 103; 29; 152; 148; 204; 119; 78; 72; 59; 58; 125; 120; 121; 122; 43; 44; 159; 170; 186; 173; 115; 203; 228; 89; 56; 70; 139; 137; 166; 118; 99; 169; 147; 86; 153; 182; 131; 132; 202; 211; 227; 160; 179; 155; 154; 171; 145; 149; 201; 207; 210; 224; 225; 194; 85; 150; 136; 158; 183; 165; 151; 65; 7; 67; 215; 172; 157; 117; 177; 176; 168; 205; 223; 221; 112; 184; 116; 193; 188; 181; 206; 222; 101; 220; 200; 195; 196; 190; 199; 209; 52; 100; 217; 167; 197; 189; 180; 133; 18; 96; 216; 156; 187; 213; 178; 218; 230].
Definition expand (q : nat) := nth q dense_labels 230.
Definition decode_state (q : Ctx221.Q) : Ctx230.Q := st (expand (bval q)).
Definition bool_tape := (Stream bool * bool * Stream bool)%type.
Definition decode_conf (c : Ctx221.Q * bool_tape) : Ctx230.Q * bool_tape :=
  let '(q,t) := c in (decode_state q,t).

Lemma dense_working_rows : length table221 = 221.
Proof. reflexivity. Qed.

Lemma dense_targets_ok :
  forallb (fun '(_,_,n0,_,_,n1) => andb (Nat.leb n0 221) (Nat.leb n1 221)) table221 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dense_terminal b : dense_tm (bmk 221 221,b) = None.
Proof. reflexivity. Qed.

(** This is a total transition identity, including the terminal state.
    Its finite proof checks all 222 states and both symbols. *)
Lemma transition_commutes (q : Ctx221.Q) b :
  tm (decode_state q,b) =
  match dense_tm (q,b) with
  | None => None
  | Some (w,d,q') => Some (w,d,decode_state q')
  end.
Proof.
  destruct q as [n Hn].
  assert (Hle : n <= 221) by (apply Nat.leb_le; exact Hn).
  do 222 (destruct n as [|n]; [destruct b; vm_compute; reflexivity|]).
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
