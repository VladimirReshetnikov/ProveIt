(** CM215 in the EXACT stream semantics of K215F.Dense215.
    No integer-tape model or function-extensionality bridge is used. *)
From Coq Require Import List Streams Bool Arith Lia.
From BusyCoq Require Import TM.
From K215F Require Import TM230 Dense215.
Require Import CM215Table.
Import ListNotations.
Module Import D := Dense215.Dense.
Set Default Goal Selector "!".
Definition cfg := (Ctx215.Q * (Stream bool * bool * Stream bool))%type.
Definition cm_tmn (q : nat) (b : bool) : option (bool * dir * nat) :=
  match nth_error tableCM215 q with
  | None => None
  | Some (w0,d0,n0,w1,d1,n1) =>
      if b then Some (w1,d1,n1) else Some (w0,d0,n0)
  end.
Definition cm_tm : D.TM := fun '(q,b) =>
  match cm_tmn (bval q) b with
  | None => None
  | Some (w,d,n) => Some (w,d,bmk 215 n)
  end.
Definition phi (q : Ctx215.Q) : Ctx215.Q :=
  if Nat.eqb (bval q) 170 then bmk 215 52 else q.
Definition lift (c : cfg) : cfg := let '(q,t) := c in (phi q,t).
Definition maprow (r : bool * dir * Ctx215.Q) :=
  let '(w,d,q) := r in (w,d,phi q).
Definition Inv (c : cfg) : Prop :=
  let '(q,((l,b),r)) := c in
  (bval q = 52 -> hd l = true) /\
  (bval q = 170 -> b = false -> hd l = false) /\
  (bval q = 151 -> hd r = true).

(* One reflected table certificate, rather than 5 x 432 case splits. *)
Definition s_and {P Q : Prop} (p : {P}+{~P}) (q : {Q}+{~Q}) :
  {P /\ Q}+{~(P /\ Q)}.
Proof. destruct p,q; [left|right|right|right]; tauto. Defined.
Definition s_or {P Q : Prop} (p : {P}+{~P}) (q : {Q}+{~Q}) :
  {P \/ Q}+{~(P \/ Q)}.
Proof. destruct p,q; [left|left|left|right]; tauto. Defined.
Definition s_imp {P Q : Prop} (p : {P}+{~P}) (q : {Q}+{~Q}) :
  {P -> Q}+{~(P -> Q)}.
Proof. destruct p,q; [left|right|left|left]; tauto. Defined.
Definition s_iff {P Q : Prop} (p : {P}+{~P}) (q : {Q}+{~Q}) :
  {P <-> Q}+{~(P <-> Q)}.
Proof. destruct p,q; [left|right|right|left]; tauto. Defined.
Definition s_not {P : Prop} (p : {P}+{~P}) : {~P}+{~~P}.
Proof. destruct p; [right|left]; tauto. Defined.
Definition dir_dec (x y : dir) : {x=y}+{x<>y}.
Proof. decide equality. Defined.
Definition row_dec (x y : option (bool * dir * Ctx215.Q)) : {x=y}+{x<>y}.
Proof. repeat first [apply bnat_dec | apply bool_dec | apply dir_dec | decide equality]. Defined.
Definition Incoming (q : Ctx215.Q) (z : option (bool * dir * Ctx215.Q)) : Prop :=
  match z with
  | None => True
  | Some (w,d,q') =>
    (bval q' = 52 -> w = true /\ d = R) /\
    (bval q' = 170 ->
      (w = false /\ d = R) \/ (bval q = 151 /\ w = true /\ d = R)) /\
    (bval q' = 151 -> w = true /\ d = L)
  end.
Definition Facts q b : Prop :=
  (bval q <> 52 -> bval q <> 170 ->
    cm_tm (phi q,b) = option_map maprow (dense_tm (q,b))) /\
  (dense_tm (q,b) = None <-> cm_tm (phi q,b) = None) /\
  Incoming q (dense_tm (q,b)).
Ltac decide_fact :=
  first [apply s_and; decide_fact | apply s_or; decide_fact |
    apply s_imp; decide_fact | apply s_iff; decide_fact | apply s_not; decide_fact |
    apply row_dec | apply Nat.eq_dec | apply bool_dec | apply dir_dec | left; exact I].
Definition facts_dec q b : {Facts q b}+{~Facts q b}.
Proof.
  unfold Facts, Incoming. destruct (dense_tm (q,b)) as [[[w d] q']|]; decide_fact.
Defined.
Definition check_facts q b := if facts_dec q b then true else false.
Lemma checked_facts :
  forallb (fun q => andb (check_facts q false) (check_facts q true)) (ball 215) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma facts q b : Facts q b.
Proof.
  pose proof (proj1 (forallb_forall _ _) checked_facts q (ball_spec 215 q)) as H.
  apply andb_true_iff in H.
  assert (E : check_facts q b = true) by (destruct b; tauto).
  unfold check_facts in E. destruct (facts_dec q b); [assumption|discriminate].
Qed.
Lemma common_rows q b : bval q <> 52 -> bval q <> 170 ->
  cm_tm (phi q,b) = option_map maprow (dense_tm (q,b)).
Proof. exact (proj1 (facts q b)). Qed.
Lemma halt_rows q b : dense_tm (q,b) = None <-> cm_tm (phi q,b) = None.
Proof. exact (proj1 (proj2 (facts q b))). Qed.
Lemma incoming_facts q b w d q' : dense_tm (q,b) = Some (w,d,q') ->
  Incoming q (Some (w,d,q')).
Proof.
  intros E. exact (eq_rect _ (Incoming q) (proj2 (proj2 (facts q b))) _ E).
Qed.
Lemma incoming52 q b w d q' : dense_tm (q,b) = Some (w,d,q') ->
  bval q' = 52 -> w = true /\ d = R.
Proof. intros E. exact (proj1 (incoming_facts q b w d q' E)). Qed.
Lemma incoming170 q b w d q' : dense_tm (q,b) = Some (w,d,q') ->
  bval q' = 170 ->
  (w = false /\ d = R) \/ (bval q = 151 /\ w = true /\ d = R).
Proof. intros E. exact (proj1 (proj2 (incoming_facts q b w d q' E))). Qed.
Lemma incoming151 q b w d q' : dense_tm (q,b) = Some (w,d,q') ->
  bval q' = 151 -> w = true /\ d = L.
Proof. intros E. exact (proj2 (proj2 (incoming_facts q b w d q' E))). Qed.

Lemma initial_invariant l b r : Inv (bmk 215 0,(l,b,r)).
Proof. unfold Inv; cbn. repeat split; discriminate. Qed.

Lemma invariant_step c c' : Inv c -> D.step dense_tm c c' -> Inv c'.
Proof.
  intros I S. destruct S as [q q' b w l r E | q q' b w l r E].
  - change ((bval q = 52 -> hd l = true) /\
      (bval q = 170 -> b = false -> hd l = false) /\
      (bval q = 151 -> hd r = true)) in I.
    unfold Inv; cbn. repeat split.
    + intros Q. destruct (incoming52 q b w L q' E Q); discriminate.
    + intros Q B. destruct (incoming170 q b w L q' E Q) as [[_ H]|[_ [_ H]]]; discriminate.
    + intros Q. exact (proj1 (incoming151 q b w L q' E Q)).
  - change ((bval q = 52 -> hd l = true) /\
      (bval q = 170 -> b = false -> hd l = false) /\
      (bval q = 151 -> hd r = true)) in I.
    unfold Inv; cbn. repeat split.
    + intros Q. exact (proj1 (incoming52 q b w R q' E Q)).
    + intros Q B. destruct (incoming170 q b w R q' E Q) as [[W _]|[Q0 [W _]]].
      * exact W.
      * pose proof (proj2 (proj2 I) Q0). congruence.
    + intros Q. destruct (incoming151 q b w R q' E Q); discriminate.
Qed.

Lemma ordinary_step c c' :
  bval (fst c) <> 52 -> bval (fst c) <> 170 ->
  D.step dense_tm c c' -> D.step cm_tm (lift c) (lift c').
Proof.
  intros A B S. destruct S as [q q' b w l r E | q q' b w l r E].
  - apply D.step_left. rewrite common_rows by assumption.
    exact (f_equal (option_map maprow) E).
  - apply D.step_right. rewrite common_rows by assumption.
    exact (f_equal (option_map maprow) E).
Qed.

Lemma halt_lift c : D.halted dense_tm c <-> D.halted cm_tm (lift c).
Proof. destruct c as [q [[l b] r]]. apply halt_rows. Qed.

Lemma special52 l b r c' : Inv (bmk 215 52,(l,b,r)) ->
  D.step dense_tm (bmk 215 52,(l,b,r)) c' ->
  D.progress cm_tm (lift (bmk 215 52,(l,b,r))) (lift c').
Proof.
  intros I S.
  assert (S0 : D.step dense_tm (bmk 215 52,(l,b,r))
    (bmk 215 (if b then 145 else 149),D.move_right (l,b,r))).
  { apply D.step_right. destruct b; reflexivity. }
  pose proof (D.step_deterministic dense_tm _ _ _ S S0) as E. subst c'.
  destruct b.
  - change (D.progress cm_tm (bmk 215 52,(l,true,r))
      (bmk 215 145,D.move_right (l,true,r))).
    apply D.progress_base, D.step_right. reflexivity.
  - destruct l as [a l]. assert (A : a = true) by (apply (proj1 I); reflexivity). subst a.
    change (D.progress cm_tm (bmk 215 52,(Cons true l,false,r))
      (bmk 215 149,D.move_right (Cons true l,false,r))).
    eapply (@D.progress_step cm_tm _ (bmk 215 170,D.move_left (Cons true l,false,r)) _).
    + apply D.step_left. reflexivity.
    + eapply (@D.progress_step cm_tm _ (bmk 215 125,(Cons true l,false,r)) _).
      * change (D.step cm_tm (bmk 215 170,(l,true,Cons false r))
          (bmk 215 125,D.move_right (l,true,Cons false r))).
        apply D.step_right. reflexivity.
      * apply D.progress_base, D.step_right. reflexivity.
Qed.

Lemma special170 l b r c' : Inv (bmk 215 170,(l,b,r)) ->
  D.step dense_tm (bmk 215 170,(l,b,r)) c' ->
  D.progress cm_tm (lift (bmk 215 170,(l,b,r))) (lift c').
Proof.
  intros I S.
  assert (S0 : D.step dense_tm (bmk 215 170,(l,b,r))
    (bmk 215 (if b then 145 else 163),D.move_right (l,b,r))).
  { apply D.step_right. destruct b; reflexivity. }
  pose proof (D.step_deterministic dense_tm _ _ _ S S0) as E. subst c'.
  destruct b.
  - change (D.progress cm_tm (bmk 215 52,(l,true,r))
      (bmk 215 145,D.move_right (l,true,r))).
    apply D.progress_base, D.step_right. reflexivity.
  - destruct l as [a l].
    assert (A : a = false) by (apply (proj1 (proj2 I)); reflexivity). subst a.
    change (D.progress cm_tm (bmk 215 52,(Cons false l,false,r))
      (bmk 215 163,D.move_right (Cons false l,false,r))).
    eapply (@D.progress_step cm_tm _ (bmk 215 170,D.move_left (Cons false l,false,r)) _).
    + apply D.step_left. reflexivity.
    + eapply (@D.progress_step cm_tm _ (bmk 215 178,(Cons false l,false,r)) _).
      * change (D.step cm_tm (bmk 215 170,(l,false,Cons false r))
          (bmk 215 178,D.move_right (l,false,Cons false r))).
        apply D.step_right. reflexivity.
      * apply D.progress_base, D.step_right. reflexivity.
Qed.

Lemma local_progress c c' : Inv c -> D.step dense_tm c c' ->
  D.progress cm_tm (lift c) (lift c').
Proof.
  destruct c as [q [[l b] r]]. intros I S.
  destruct (Nat.eq_dec (bval q) 52) as [A|A].
  - assert (E : q = bmk 215 52) by (apply bnat_eq; exact A).
    subst q. apply special52; assumption.
  - destruct (Nat.eq_dec (bval q) 170) as [B|B].
    + assert (E : q = bmk 215 170) by (apply bnat_eq; exact B).
      subst q. apply special170; assumption.
    + apply D.progress_base. apply ordinary_step; assumption.
Qed.

(** Generic positive-block transport in the SAME native stream semantics. *)
Section PositiveTransport.
Variables (old new : D.TM) (J : cfg -> Prop) (f : cfg -> cfg).
Hypothesis Jstep : forall c c', J c -> D.step old c c' -> J c'.
Hypothesis halt_f : forall c, D.halted old c <-> D.halted new (f c).
Hypothesis step_f : forall c c', J c -> D.step old c c' ->
  D.progress new (f c) (f c').

Lemma evstep_f c c' : J c -> D.evstep old c c' -> D.evstep new (f c) (f c').
Proof.
  intros I H. induction H.
  - constructor.
  - eapply D.evstep_trans.
    + apply D.progress_evstep. apply step_f; eassumption.
    + apply IHevstep. eapply Jstep; eassumption.
Qed.
Lemma halts_forward c : J c -> D.halts old c -> D.halts new (f c).
Proof.
  intros I (n & c' & H & Z). eapply D.halted_evstep_halts.
  - apply evstep_f; [exact I|]. apply D.without_counter with n; exact H.
  - apply halt_f. exact Z.
Qed.
Lemma halts_backward c : J c -> D.halts new (f c) -> D.halts old c.
Proof.
  intros I H.
  set (P := fun d => exists e, d = f e /\ J e /\ D.evstep old c e).
  destruct (D.progress_halts new P (fun _ => D.halts old c) (f c)) as (d & _ & Z).
  - intros d (e & -> & Je & R).
    destruct e as [q [[l b] r]].
    destruct (old (q,b)) as [[[w dir] q']|] eqn:E.
    + right. destruct dir.
      * eexists. split.
        -- eexists; split; [reflexivity|]. split.
           ++ eapply Jstep; [exact Je|]. eapply D.step_left; exact E.
           ++ eapply D.evstep_trans; [exact R|]. apply D.evstep_one. eapply D.step_left; exact E.
        -- apply step_f; [exact Je|]. eapply D.step_left; exact E.
      * eexists. split.
        -- eexists; split; [reflexivity|]. split.
           ++ eapply Jstep; [exact Je|]. eapply D.step_right; exact E.
           ++ eapply D.evstep_trans; [exact R|]. apply D.evstep_one. eapply D.step_right; exact E.
        -- apply step_f; [exact Je|]. eapply D.step_right; exact E.
    + left. eapply D.halted_evstep_halts; [exact R|exact E].
  - exists c. split; [reflexivity|]. split; [exact I|constructor].
  - exact H.
  - exact Z.
Qed.
Theorem positive_transport c : J c -> (D.halts old c <-> D.halts new (f c)).
Proof. intros I; split; [apply halts_forward|apply halts_backward]; exact I. Qed.
End PositiveTransport.

Theorem invariant_equihalting c : Inv c ->
  (D.halts dense_tm c <-> D.halts cm_tm (lift c)).
Proof.
  apply (positive_transport dense_tm cm_tm Inv lift invariant_step halt_lift local_progress c).
Qed.
Theorem all_tapes_equihalting l b r :
  D.halts dense_tm (bmk 215 0,(l,b,r)) <->
  D.halts cm_tm (bmk 215 0,(l,b,r)).
Proof. apply invariant_equihalting, initial_invariant. Qed.
Corollary blank_halts_iff : D.halts dense_tm D.c0 <-> D.halts cm_tm D.c0.
Proof. apply all_tapes_equihalting. Qed.
Corollary blank_nonhalting_iff : (~ D.halts dense_tm D.c0) <-> (~ D.halts cm_tm D.c0).
Proof. rewrite blank_halts_iff. reflexivity. Qed.
Print Assumptions all_tapes_equihalting.
Print Assumptions blank_halts_iff.
