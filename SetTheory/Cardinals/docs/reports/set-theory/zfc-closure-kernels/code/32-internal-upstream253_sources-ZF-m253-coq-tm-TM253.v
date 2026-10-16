(** * TM253: the exact 253-working-state candidate with old numeric proof labels.

    The physical state type is [bnat 253]: working states 0..252 plus halt 253.
    [st] translates the old numeric labels retained by the symbolic executor.
    The machine [tm] reads only the literal compact [table253].  [tmn] reads
    a generated old-label view; [all_labels_ok] proves its exact correspondence
    with that literal table.  Old label 8 is deleted and maps to halt. *)

From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia Eqdep_dec.
From BusyCoq Require Import TM.
From M253 Require Import Table253.
Import ListNotations.

(** ** Bounded naturals (as in zf/v335/coq/ZFTM.v) *)
Definition bnat (k : nat) : Type := { n : nat | Nat.leb n k = true }.

Definition bval {k} (x : bnat k) : nat := proj1_sig x.

Definition bmk (k n : nat) : bnat k :=
  match Nat.leb n k as b return Nat.leb n k = b -> bnat k with
  | true => fun H => exist _ n H
  | false => fun _ => exist _ k (Nat.leb_refl k)
  end eq_refl.

Lemma bnat_eq : forall k (x y : bnat k), bval x = bval y -> x = y.
Proof.
  intros k [x Hx] [y Hy]; simpl; intros ->.
  f_equal. apply UIP_dec. exact bool_dec.
Qed.

Lemma bval_bmk : forall k n, n <= k -> bval (bmk k n) = n.
Proof.
  intros k n H. unfold bmk.
  generalize (@eq_refl bool (Nat.leb n k)).
  generalize (Nat.leb n k) at 2 3. intros b E. destruct b; [reflexivity|].
  apply Nat.leb_nle in E. lia.
Qed.

Lemma bmk_bval : forall k (x : bnat k), bmk k (bval x) = x.
Proof.
  intros k x. apply bnat_eq. apply bval_bmk.
  destruct x as [n H]. simpl. apply Nat.leb_le, H.
Qed.

Lemma bval_le : forall k (x : bnat k), bval x <= k.
Proof. intros k [n H]. simpl. apply Nat.leb_le, H. Qed.

Definition bnat_dec {k} (x y : bnat k) : {x = y} + {x <> y}.
Proof.
  destruct (Nat.eq_dec (bval x) (bval y)) as [E|E].
  - left. apply bnat_eq, E.
  - right. intros ->. apply E. reflexivity.
Defined.

Definition ball (k : nat) : list (bnat k) := map (bmk k) (seq 0 (S k)).

Lemma ball_spec : forall k x, In x (ball k).
Proof.
  intros k x. unfold ball. rewrite <- (bmk_bval k x).
  apply in_map, in_seq. pose proof (bval_le k x). lia.
Qed.

(** ** Old proof labels and compact physical states *)
Definition NH := 254.                     (* old terminal label *)
Definition PNH := 253.                    (* actual terminal state *)
Definition state := bnat PNH.
Definition compact_of (q : nat) : nat := nth q compact_labels PNH.
Definition old_of (q : nat) : nat := nth q old_labels NH.
Definition st (q : nat) : state := bmk PNH (compact_of q).

Lemma compact_labels_ok : forallb (fun q => Nat.leb q PNH) compact_labels = true.
Proof. vm_compute. reflexivity. Qed.

Lemma compact_of_bound q : compact_of q <= PNH.
Proof.
  unfold compact_of. destruct (lt_dec q (length compact_labels)) as [H|H].
  - pose proof compact_labels_ok as A. rewrite forallb_forall in A.
    apply Nat.leb_le. apply A. apply nth_In, H.
  - rewrite nth_overflow by lia. lia.
Qed.

Lemma bval_st q : bval (st q) = compact_of q.
Proof. apply bval_bmk, compact_of_bound. Qed.

Lemma compact_old_of_certificate :
  forallb (fun n => Nat.eqb (compact_of (old_of n)) n) (seq 0 254) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma compact_old_of n : n <= PNH -> compact_of (old_of n) = n.
Proof.
  intros H. pose proof compact_old_of_certificate as A. rewrite forallb_forall in A.
  apply Nat.eqb_eq. apply A. apply in_seq. unfold PNH in H. lia.
Qed.

Lemma st_surjective (q : state) : st (old_of (bval q)) = q.
Proof. apply bnat_eq. rewrite bval_st. apply compact_old_of, bval_le. Qed.

Module Ctx253 <: Ctx.
  Definition Q := state.
  Definition Sym := bool.
  Definition q0 := st 5.                  (* compact start state 0 *)
  Definition s0 := false.
  Definition q1 := st 1.
  Lemma q0_neq_q1 : q0 <> q1.
  Proof. intros H. apply (f_equal bval) in H. vm_compute in H. discriminate. Qed.
  Definition s1 := true.
  Lemma s0_neq_s1 : s0 <> s1. Proof. discriminate. Qed.
  Definition eqb_q : forall a b : Q, {a = b} + {a <> b} := bnat_dec.
  Definition eqb_sym := bool_dec.
  Definition all_qs := ball PNH.
  Definition all_qs_spec := ball_spec PNH.
  Definition all_syms := [false; true].
  Lemma all_syms_spec : forall a, In a all_syms.
  Proof. intros []; simpl; tauto. Qed.
End Ctx253.

Module TM253 := TM.TM Ctx253.
Export TM253.

(** ** The actual literal machine, and the old-label proof-execution view *)
Definition compact_tmn (q : nat) (s : bool) : option (bool * dir * nat) :=
  match nth_error table253 q with
  | None => None
  | Some (w0, d0, n0, w1, d1, n1) =>
      if s then Some (w1, d1, n1) else Some (w0, d0, n0)
  end.

Definition tm : TM := fun '(q, s) =>
  match compact_tmn (bval q) s with
  | None => None
  | Some (w, d, n) => Some (w, d, bmk PNH n)
  end.

Definition tmn (q : nat) (s : bool) : option (bool * dir * nat) :=
  match nth_error logical_table253 q with
  | Some (Some (w0, d0, n0, w1, d1, n1)) =>
      if s then Some (w1, d1, n1) else Some (w0, d0, n0)
  | _ => None
  end.

Definition physical_of_transition (t : option (bool * dir * nat)) :=
  match t with
  | Some (w, d, n) => Some (w, d, compact_of n)
  | None => None
  end.

Definition dir_eqb (x y : dir) : bool :=
  match x, y with L, L | R, R => true | _, _ => false end.

Definition transition_eqb (x y : option (bool * dir * nat)) : bool :=
  match x, y with
  | None, None => true
  | Some (w, d, n), Some (w', d', n') =>
      andb (Bool.eqb w w') (andb (dir_eqb d d') (Nat.eqb n n'))
  | _, _ => false
  end.

Lemma transition_eqb_eq x y : transition_eqb x y = true -> x = y.
Proof.
  destruct x as [[[w d] n]|], y as [[[w' d'] n']|]; simpl; try discriminate; try reflexivity.
  intros H. apply andb_true_iff in H as [Hw H]. apply andb_true_iff in H as [Hd Hn].
  apply Bool.eqb_prop in Hw. apply Nat.eqb_eq in Hn.
  destruct d, d'; simpl in Hd; try discriminate; subst; reflexivity.
Qed.

Definition label_ok (q : nat) (s : bool) : bool :=
  transition_eqb (physical_of_transition (tmn q s)) (compact_tmn (compact_of q) s).

Lemma all_labels_ok :
  forallb (fun q => andb (label_ok q false) (label_ok q true)) (seq 0 254) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tmn_corresponds q s : q < 254 ->
  physical_of_transition (tmn q s) = compact_tmn (compact_of q) s.
Proof.
  intros Hq. pose proof all_labels_ok as A. rewrite forallb_forall in A.
  assert (I : In q (seq 0 254)) by (apply in_seq; lia).
  specialize (A q I). apply andb_true_iff in A as [A0 A1].
  unfold label_ok in A0, A1. destruct s; apply transition_eqb_eq; assumption.
Qed.

Lemma logical_table_length : length logical_table253 = 254.
Proof. reflexivity. Qed.

Lemma tmn_source_bound q s w d n : tmn q s = Some (w, d, n) -> q < 254.
Proof.
  unfold tmn. destruct (nth_error logical_table253 q) as [row|] eqn:E; [|discriminate].
  destruct row as [row|]; [|discriminate]. intros _.
  rewrite <- logical_table_length. apply nth_error_Some. rewrite E. discriminate.
Qed.

Lemma tm_st q s w d n : tmn q s = Some (w, d, n) ->
  tm (st q, s) = Some (w, d, st n).
Proof.
  intros H. pose proof (tmn_source_bound _ _ _ _ _ H) as Hq.
  pose proof (tmn_corresponds q s Hq) as C. rewrite H in C. cbn [physical_of_transition] in C.
  unfold tm. rewrite bval_st. rewrite <- C. reflexivity.
Qed.

Lemma table_length : length table253 = PNH.
Proof. reflexivity. Qed.

Lemma tm_halt s : tm (st NH, s) = None.
Proof. reflexivity. Qed.

Lemma targets_ok :
  forallb (fun '(_, _, n0, _, _, n1) => andb (Nat.leb n0 PNH) (Nat.leb n1 PNH)) table253 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma start_compact : bval (st 5) = 0.
Proof. reflexivity. Qed.

Lemma halt_compact : bval (st NH) = 253.
Proof. reflexivity. Qed.

Lemma working_rows : length table253 = 253.
Proof. reflexivity. Qed.

Print Assumptions tm_st.
Print Assumptions st_surjective.
