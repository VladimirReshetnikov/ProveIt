(** Elementary dependent case analysis, minimization, and square pairing. *)

From Stdlib Require Import Arith.Compare_dec Arith.PeanoNat Arith.Wf_nat Lia Logic.Classical
  Vectors.Fin.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition nat_cases {F : nat -> Type}
    (hzero : F 0) (hsucc : forall n, F (S n))
    (n : nat) : F n :=
  match n as k return F k with
  | 0 => hzero
  | S k => hsucc k
  end.

Lemma nat_cases_zero : forall F (hzero : F 0) hsucc,
  nat_cases hzero hsucc 0 = hzero.
Proof. reflexivity. Qed.

Lemma nat_cases_succ : forall F (hzero : F 0) hsucc n,
  nat_cases hzero hsucc (S n) = hsucc n.
Proof. reflexivity. Qed.

Lemma nat_ne_succ_max_left : forall n m,
  n <> S (Nat.max n m).
Proof.
  intros n m H. pose proof (Nat.le_max_l n m). lia.
Qed.

Lemma nat_ne_succ_max_right : forall n m,
  n <> S (Nat.max m n).
Proof.
  intros n m H. pose proof (Nat.le_max_r m n). lia.
Qed.

Fixpoint nat_fold {A} (a : A) (step : nat -> A -> A) (n : nat) : A :=
  match n with
  | 0 => a
  | S k => step k (nat_fold a step k)
  end.

Lemma nat_fold_ext_below : forall A (a : A)
    (f g : nat -> A -> A) n,
  (forall m, m < n -> forall x, f m x = g m x) ->
  nat_fold a f n = nat_fold a g n.
Proof.
  intros A a f g n. induction n as [|n IH]; intro Hfg; simpl.
  - reflexivity.
  - rewrite (IH (fun m Hm x => Hfg m (Nat.lt_lt_succ_r _ _ Hm) x)).
    apply Hfg. apply Nat.lt_succ_diag_r.
Qed.

Theorem nat_least_number : forall P : nat -> Prop,
  (exists n, P n) ->
  exists n, P n /\ forall m, m < n -> ~ P m.
Proof.
  intros P [bound Hbound].
  assert (Hleast : forall n,
    (exists m, m <= n /\ P m) ->
    exists m, P m /\ forall k, k < m -> ~ P k).
  { intro n. induction n as [|n IH]; intros [m [Hm HP]].
    - assert (m = 0) by lia. subst. exists 0. split; [exact HP | lia].
    - destruct (classic (exists m, m <= n /\ P m)) as [Hprev | Hprev].
      + exact (IH Hprev).
      + assert (Hmnot : ~ m <= n).
        { intro Hmn. apply Hprev. exists m. now split. }
        assert (m = S n) by lia. subst.
        exists (S n). split; [exact HP |].
        intros k Hk Hpk. apply Hprev. exists k. split; [lia | exact Hpk]. }
  apply (Hleast bound). exists bound. split; [lia | exact Hbound].
Qed.

Definition nat_to_fin (n x : nat) : option (Fin.t n) :=
  match lt_dec x n with
  | left Hlt => Some (Fin.of_nat_lt Hlt)
  | right _ => None
  end.

Lemma nat_positive_of_nonzero : forall n,
  n <> 0 -> 0 < n.
Proof. intros n Hn. lia. Qed.

Lemma nat_one_le_of_odd : forall n,
  Nat.odd n = true -> 1 <= n.
Proof. intros [|n] Hodd; [discriminate | lia]. Qed.

Definition nat_square_pair (a b : nat) : nat :=
  if Nat.ltb a b then b * b + a else a * a + a + b.

Theorem nat_square_pair_monotone : forall a1 a2 b1 b2,
  a1 <= a2 -> b1 <= b2 ->
  nat_square_pair a1 b1 <= nat_square_pair a2 b2.
Proof.
  intros a1 a2 b1 b2 Ha Hb. unfold nat_square_pair.
  destruct (Nat.ltb_spec a1 b1);
    destruct (Nat.ltb_spec a2 b2); nia.
Qed.
