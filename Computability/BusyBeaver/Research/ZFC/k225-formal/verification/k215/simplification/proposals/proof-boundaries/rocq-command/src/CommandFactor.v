(** A codec/command interface for the current Rocq K215 enumerator.
    This adapter leaves every maintained definition unchanged.
    The factorization is already the design of the maintained Lean EnumPerm;
    the present file checks it against the Rocq definitions at 6d9800d1ca67.
    No formula well-formedness or valid-code hypothesis is used. *)
From Coq Require Import Arith Lia Bool List.
From K230L Require Import Codes230.
From K215F Require Import Codes222 Thm222 EnumPerm L1_CompPerm L1_SoundPerm.
Import ListNotations.

Local Opaque P wim wal rho1 rho2 rho3 rho4 rho5 rho6 rho8 growG bundle222.

Definition decode (z : nat) : cmd * nat :=
  let '(ac, rest) := unP z in
  match ac with
  | 0 => (CNIP, rest)
  | 1 => (CDROP, rest)
  | 2 => let '(x, rest') := unP rest in (CMP x, rest')
  | S (S (S c)) => let '(y, rest') := unP rest in
                    let '(x, rest'') := unP rest' in (CAX c x y, rest'')
  end.

Definition fetch (s : state) : nat * nat :=
  if Nat.eqb (pl s) 0 then (np s, S (np s)) else (pred (pl s), np s).

Definition restore (rest next : nat) (q : tup) : state :=
  let '(t,w,dd,hh) := q in mkState rest next t w dd hh.

Definition exec_at (z next : nat) (s : state) : option state :=
  let '(c,rest) := decode z in option_map (restore rest next) (xstep c (tupof s)).

Theorem enum_step_factor s : enum_step s = exec_at (fst (fetch s)) (snd (fetch s)) s.
Proof.
  unfold enum_step, exec_at, fetch, decode.
  destruct (if Nat.eqb (pl s) 0 then _ else _) as [z next]. cbn [fst snd].
  destruct (unP z) as [ac rest]. destruct ac as [|[|[|c]]]; cbn [xstep tupof].
  - destruct (Nat.eqb (h s) 1); [reflexivity|]. now destruct (unP (ws s)).
  - reflexivity.
  - destruct (unP rest) as [x rest']. destruct (Nat.eqb _ _); reflexivity.
  - destruct (unP rest) as [y rest']. now destruct (unP rest').
Qed.

Theorem decode_fields c rest : decode (enc_fields (fields c) rest) = (c,rest).
Proof.
  destruct c; cbn [fields enc_fields fold_right]; unfold decode; rewrite !unP_P; reflexivity.
Qed.

Theorem decode_le z : snd (decode z) <= z.
Proof.
  pose proof (unP_le z) as [_ H1]. unfold decode.
  destruct (unP z) as [ac rest]. cbn in H1.
  destruct ac as [|[|[|c]]]; cbn [snd]; try exact H1.
  - pose proof (unP_le rest) as [_ H2]. destruct (unP rest). cbn in *; lia.
  - pose proof (unP_le rest) as [_ H2]. destruct (unP rest) as [y rest']. cbn in H2.
    pose proof (unP_le rest') as [_ H3]. destruct (unP rest'). cbn in *; lia.
Qed.

(** Replacement body for step_read; the command cases are confined to decode_fields. *)
Theorem step_read_factored s c rest next :
  (pl s = S (enc_fields (fields c) rest) /\ next = np s) \/
  (pl s = 0 /\ np s = enc_fields (fields c) rest /\ next = S (np s)) ->
  enum_step s = option_map (restore rest next) (xstep c (tupof s)).
Proof.
  intro H. rewrite enum_step_factor.
  assert (E : fetch s = (enc_fields (fields c) rest, next)).
  { unfold fetch. destruct H as [[-> ->] | [-> [-> ->]]]; reflexivity. }
  rewrite E. cbn [fst snd]. unfold exec_at. now rewrite decode_fields.
Qed.

(** Replacement body for step_pl; only the codec knows the variable field count. *)
Theorem step_pl_factored s s' : enum_step s = Some s' ->
  pl s' <= fst (fetch s) /\ np s' = snd (fetch s).
Proof.
  rewrite enum_step_factor. unfold exec_at.
  pose proof (decode_le (fst (fetch s))) as Hle.
  destruct (decode (fst (fetch s))) as [c rest]. cbn [snd] in Hle.
  destruct (xstep c (tupof s)) as [[[[t w] dd] hh]|]; cbn; [|discriminate].
  intro E; injection E as <-. now split.
Qed.

(** Generic lifting separates command soundness from all codec details. *)
Theorem lift_invariant (I : tup -> Prop)
    (closed : forall c q q', I q -> xstep c q = Some q' -> I q') s s' :
  I (tupof s) -> enum_step s = Some s' -> I (tupof s').
Proof.
  intros H. rewrite enum_step_factor. unfold exec_at.
  destruct (decode (fst (fetch s))) as [c rest].
  destruct (xstep c (tupof s)) as [[[[t w] dd] hh]|] eqn:E; cbn; [|discriminate].
  intro He; injection He as <-. exact (closed c _ _ H E).
Qed.

Theorem lift_halt (I : tup -> Prop) (P : Prop)
    (closed : forall c q, I q -> xstep c q = None -> P) s :
  I (tupof s) -> enum_step s = None -> P.
Proof.
  intros H. rewrite enum_step_factor. unfold exec_at.
  destruct (decode (fst (fetch s))) as [c rest].
  destruct (xstep c (tupof s)) as [q|] eqn:E; [discriminate|].
  intros _. exact (closed c _ H E).
Qed.

Definition WorkingInv (q : tup) : Prop :=
  let '(t,w,dd,hh) := q in thm222 t /\ thm222 hh /\ goodstack w.

Theorem xstep_inv c q q' : WorkingInv q -> xstep c q = Some q' -> WorkingInv q'.
Proof.
  destruct q as [[[t w] dd] hh]. intros [Ht [Hh Hw]].
  destruct c as [| |x|c x y]; cbn [xstep].
  - destruct (Nat.eqb hh 1); [discriminate|].
    destruct (good_pop _ Hw) as [H1 H2]. destruct (unP w) as [h1 w1].
    intro E; injection E as <-. repeat split; assumption.
  - intro E; injection E as <-. repeat split; try assumption. now apply good_push.
  - destruct (Nat.eqb (wim t (dd+x)) hh) eqn:E; intro He; injection He as <-.
    + apply Nat.eqb_eq in E. repeat split; cbn [WorkingInv].
      * apply (W_mp t); [exact Ht | now rewrite E].
      * exact W_true.
      * apply good_push; [exact W_true | exact Hw].
    + repeat split; try exact W_true; exact Hw.
  - intro E; injection E as <-. repeat split; cbn [WorkingInv].
    + apply gate_thm.
    + exact W_true.
    + unfold ax_stack. repeat apply good_push; try assumption; constructor; assumption.
Qed.

Theorem xstep_halt c q : WorkingInv q -> xstep c q = None -> thm222 1.
Proof.
  destruct q as [[[t w] dd] hh]. intros [_ [Hh _]].
  destruct c; cbn [xstep]; try (destruct (Nat.eqb _ _); discriminate); try discriminate.
  destruct (Nat.eqb hh 1) eqn:E; [|discriminate].
  intros _. apply Nat.eqb_eq in E. now rewrite <- E.
Qed.

Theorem Inv_step_factored s s' : Inv s -> enum_step s = Some s' -> Inv s'.
Proof. exact (lift_invariant WorkingInv xstep_inv s s'). Qed.

Theorem halt_step_factored s : Inv s -> enum_step s = None -> thm222 1.
Proof. exact (lift_halt WorkingInv (thm222 1) xstep_halt s). Qed.

Print Assumptions enum_step_factor.
Print Assumptions decode_fields.
Print Assumptions decode_le.
Print Assumptions step_read_factored.
Print Assumptions step_pl_factored.
Print Assumptions Inv_step_factored.
Print Assumptions halt_step_factored.
