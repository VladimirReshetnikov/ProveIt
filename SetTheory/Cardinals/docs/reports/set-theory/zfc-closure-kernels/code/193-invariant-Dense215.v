(** Exact relabelling of the verified sparse-label runtime to 215 working states.
    The state type here is bnat 215: 0..214 work, 215 halts.  There is no
    extra unreachable state in this dense presentation. *)
From Coq Require Import Lists.List Lists.Streams Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From K215F Require Import TM230 Table215 StateRelabel.
Import ListNotations.

Module Sparse := K215F.TM230.TM230.

Module Ctx215 <: Ctx.
  Definition Q := bnat 215.
  Definition Sym := bool.
  Definition q0 := bmk 215 0.
  Definition s0 := false.
  Definition q1 := bmk 215 1.
  Lemma q0_neq_q1 : q0 <> q1.
  Proof. intros H. apply (f_equal bval) in H. vm_compute in H. discriminate. Qed.
  Definition s1 := true.
  Lemma s0_neq_s1 : s0 <> s1. Proof. discriminate. Qed.
  Definition eqb_q : forall a b : Q, {a = b} + {a <> b} := bnat_dec.
  Definition eqb_sym := bool_dec.
  Definition all_qs := ball 215.
  Definition all_qs_spec := ball_spec 215.
  Definition all_syms := [false; true].
  Lemma all_syms_spec : forall a, In a all_syms.
  Proof. intros []; simpl; tauto. Qed.
End Ctx215.

Module Dense := TM.TM Ctx215.

Definition dense_tmn (q : nat) (b : bool) : option (bool * dir * nat) :=
  match nth_error table215 q with
  | None => None
  | Some (w0, d0, n0, w1, d1, n1) =>
      if b then Some (w1, d1, n1) else Some (w0, d0, n0)
  end.

Definition dense_tm : Dense.TM := fun '(q,b) =>
  match dense_tmn (bval q) b with
  | None => None
  | Some (w,d,n) => Some (w,d,bmk 215 n)
  end.

(** canonical dense index -> sparse label (K230 labels; native 301, 302 renamed 102, 120) *)
Definition dense_labels : list nat := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 40; 41; 42; 43; 44; 45; 46; 47; 48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 58; 59; 60; 61; 62; 63; 64; 65; 66; 67; 68; 69; 70; 71; 72; 73; 74; 75; 76; 77; 78; 80; 81; 82; 83; 84; 85; 86; 87; 88; 89; 90; 91; 92; 93; 94; 95; 96; 97; 98; 99; 100; 101; 103; 104; 105; 106; 107; 108; 109; 110; 111; 112; 113; 114; 115; 116; 117; 118; 119; 122; 123; 124; 125; 126; 127; 128; 129; 130; 131; 132; 133; 134; 135; 136; 137; 138; 139; 141; 142; 143; 144; 145; 146; 147; 148; 149; 150; 151; 152; 153; 154; 155; 156; 157; 158; 159; 160; 161; 162; 163; 164; 165; 166; 167; 168; 169; 170; 171; 172; 173; 174; 176; 177; 178; 179; 180; 181; 182; 184; 185; 186; 187; 188; 189; 190; 193; 194; 195; 196; 197; 198; 199; 200; 201; 203; 204; 205; 206; 207; 209; 210; 211; 212; 213; 214; 215; 216; 217; 218; 220; 221; 222; 223; 225; 102; 120; 230].
Definition expand (q : nat) := nth q dense_labels 230.
Definition decode_state (q : Ctx215.Q) : Ctx230.Q := st (expand (bval q)).
Definition bool_tape := (Stream bool * bool * Stream bool)%type.
Definition decode_conf (c : Ctx215.Q * bool_tape) : Ctx230.Q * bool_tape :=
  let '(q,t) := c in (decode_state q,t).

Lemma dense_working_rows : length table215 = 215.
Proof. reflexivity. Qed.

Lemma dense_targets_ok :
  forallb (fun '(_,_,n0,_,_,n1) => andb (Nat.leb n0 215) (Nat.leb n1 215)) table215 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dense_terminal b : dense_tm (bmk 215 215,b) = None.
Proof. reflexivity. Qed.

(** This is a total transition identity, including the terminal state.
    Its finite proof checks all 216 states and both symbols. *)
Lemma transition_commutes (q : Ctx215.Q) b :
  tm (decode_state q,b) =
  match dense_tm (q,b) with
  | None => None
  | Some (w,d,q') => Some (w,d,decode_state q')
  end.
Proof.
  destruct q as [n Hn].
  assert (Hle : n <= 215) by (apply Nat.leb_le; exact Hn).
  do 216 (destruct n as [|n]; [destruct b; vm_compute; reflexivity|]).
  lia.
Qed.

Lemma decode_initial : decode_conf Dense.c0 = Sparse.c0.
Proof. reflexivity. Qed.

Module Relabel.
  Include StateRelabel.StateRelabel Ctx215 Ctx230 Dense Sparse.
End Relabel.

Theorem dense_sparse_halts_iff :
  Dense.halts dense_tm Dense.c0 <-> Sparse.halts tm Sparse.c0.
Proof.
  change (Dense.halts dense_tm Dense.c0 <-> Sparse.halts tm (decode_conf Dense.c0)).
  exact (Relabel.halts_iff dense_tm tm decode_state transition_commutes Dense.c0).
Qed.

Print Assumptions dense_sparse_halts_iff.
