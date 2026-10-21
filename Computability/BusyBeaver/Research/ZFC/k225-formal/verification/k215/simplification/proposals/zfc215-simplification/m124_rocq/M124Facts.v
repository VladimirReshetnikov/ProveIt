From Coq Require Import ZArith Bool Arith Lia Lists.List.
Require Import M124Table.
Open Scope Z_scope.

Definition phi (q : nat) := if Nat.eqb q 127 then 124%nat else q.
Definition mapI (i : instr) := I (out i) (delta i) (phi (target i)).

Definition M : table := fun q b =>
  match q, b with
  | 110%nat, false => Some (I false 1 124)
  | 124%nat, false => Some (I false (-1) 127)
  | 127%nat, false => Some (I false 1 8)
  | 127%nat, true  => Some (I true 1 59)
  | _, _ => K q b
  end.

(* The unbounded quantifier is reduced to a complete finite row certificate. *)
Lemma K_large q b : (303 <= q)%nat -> K q b = None.
Proof.
  intros H. do 303 (destruct q as [|q]; [lia|]).
  destruct b; reflexivity.
Qed.

Definition inc_check (dst : nat) (mark : bool) (q : nat) (b : bool) :=
  match K q b with
  | Some i => if Nat.eqb (target i) dst
              then andb (Bool.eqb (out i) mark) (Z.eqb (delta i) 1) else true
  | None => true
  end.

Lemma inc124_all : forallb (fun q => andb (inc_check 124 true q false)
  (inc_check 124 true q true)) (seq 0 303) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma inc127_all : forallb (fun q => andb (inc_check 127 false q false)
  (inc_check 127 false q true)) (seq 0 303) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma finite_spec (P : nat -> bool -> bool) q b :
  (q < 303)%nat ->
  forallb (fun q => andb (P q false) (P q true)) (seq 0 303) = true ->
  P q b = true.
Proof.
  intros B H. apply forallb_forall with (x:=q) in H.
  - apply andb_true_iff in H. destruct b; tauto.
  - apply in_seq. lia.
Qed.

Lemma K_incoming124 q b i : K q b = Some i -> target i = 124%nat ->
  out i = true /\ delta i = 1.
Proof.
  intros E Q. destruct (Nat.lt_ge_cases q 303) as [B|B].
  - pose proof (finite_spec (inc_check 124 true) q b B inc124_all) as H.
    unfold inc_check in H. rewrite E,Q,Nat.eqb_refl in H.
    apply andb_true_iff in H. destruct H as [W D].
    apply Z.eqb_eq in D. destruct (out i); cbn in W; try discriminate; auto.
  - rewrite K_large in E by exact B. discriminate.
Qed.
Lemma K_incoming127 q b i : K q b = Some i -> target i = 127%nat ->
  out i = false /\ delta i = 1.
Proof.
  intros E Q. destruct (Nat.lt_ge_cases q 303) as [B|B].
  - pose proof (finite_spec (inc_check 127 false) q b B inc127_all) as H.
    unfold inc_check in H. rewrite E,Q,Nat.eqb_refl in H.
    apply andb_true_iff in H. destruct H as [W D].
    apply Z.eqb_eq in D. destruct (out i); cbn in W; try discriminate; auto.
  - rewrite K_large in E by exact B. discriminate.
Qed.

Definition eqI (a b : instr) := andb (Bool.eqb (out a) (out b))
  (andb (Z.eqb (delta a) (delta b)) (Nat.eqb (target a) (target b))).
Definition eqO (a b : option instr) := match a,b with
  | None,None => true | Some a,Some b => eqI a b | _,_ => false end.
Lemma eqO_sound a b : eqO a b = true -> a=b.
Proof.
  destruct a as [[w d q]|], b as [[w' d' q']|]; cbn; try discriminate; auto.
  unfold eqI; cbn. rewrite !andb_true_iff, Bool.eqb_true_iff, Z.eqb_eq,
    Nat.eqb_eq. intros [-> [-> ->]]. reflexivity.
Qed.
Definition outer_check q b :=
  if orb (Nat.eqb q 124) (Nat.eqb q 127) then true
  else eqO (M (phi q) b) (option_map mapI (K q b)).
Lemma outer_all : forallb (fun q => andb (outer_check q false)
  (outer_check q true)) (seq 0 303) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma K_M_outer q b : q <> 124%nat -> q <> 127%nat ->
  M (phi q) b = option_map mapI (K q b).
Proof.
  intros A B. destruct (Nat.lt_ge_cases q 303) as [L|L].
  - pose proof (finite_spec outer_check q b L outer_all) as H.
    unfold outer_check in H. assert (E : Nat.eqb q 124 = false)
      by (apply Nat.eqb_neq; exact A).
    assert (F : Nat.eqb q 127 = false) by (apply Nat.eqb_neq; exact B).
    rewrite E,F in H. cbn in H. now apply eqO_sound.
  - do 303 (destruct q as [|q]; [lia|]). destruct b; reflexivity.
Qed.

