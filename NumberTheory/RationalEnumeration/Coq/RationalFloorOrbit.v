(*
  Coq port of the Calkin-Wilf pair core from
  the Lean module RationalEnumeration.RationalFloorOrbit.

  This Coq module establishes the executable pair generator, inverse index map,
  rational-number bridge, and exact-once enumeration theorem for nonnegative
  rationals.
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qfield.
From Stdlib Require Import ZArith.ZArith.

Import ListNotations.

Local Open Scope nat_scope.

Module LeanProofs.
Module RationalFloorOrbit.

(* ## Stern-Brocot / Calkin-Wilf pair generator *)

Definition Coprime (a b : nat) : Prop :=
  Nat.gcd a b = 1.

Fixpoint cwPairFuel (fuel n : nat) : nat * nat :=
  match fuel with
  | 0 => (1, 1)
  | S fuel' =>
      match n with
      | 0 => (1, 1)
      | S m =>
          let p := cwPairFuel fuel' (m / 2) in
          if Nat.even m
          then (fst p, fst p + snd p)
          else (fst p + snd p, snd p)
      end
  end.

Definition cwPair (n : nat) : nat * nat :=
  cwPairFuel n n.

Theorem cwPair_zero : cwPair 0 = (1, 1).
Proof. reflexivity. Qed.

Lemma div2_lt_succ (m : nat) : m / 2 < S m.
Proof.
  destruct m as [|m].
  - simpl. lia.
  - eapply Nat.lt_trans.
    + apply Nat.div_lt; lia.
    + lia.
Qed.

Theorem cwPairFuel_ge (n fuel : nat) :
    n <= fuel -> cwPairFuel fuel n = cwPair n.
Proof.
  revert fuel.
  induction n as [n ih] using lt_wf_ind.
  intros fuel hle.
  unfold cwPair.
  destruct n as [|m].
  - destruct fuel; reflexivity.
  - destruct fuel as [|fuel']; [lia|].
    cbn [cwPairFuel fst snd].
    assert (hidx : m / 2 < S m) by apply div2_lt_succ.
    rewrite (ih (m / 2) hidx fuel') by lia.
    rewrite (ih (m / 2) hidx m) by lia.
    reflexivity.
Qed.

Theorem cwPair_unfold_succ (m : nat) :
    cwPair (S m) =
      let p := cwPair (m / 2) in
      if Nat.even m
      then (fst p, fst p + snd p)
      else (fst p + snd p, snd p).
Proof.
  unfold cwPair at 1.
  cbn [cwPairFuel fst snd].
  rewrite cwPairFuel_ge.
  - reflexivity.
  - pose proof (div2_lt_succ m). lia.
Qed.

Theorem cwPair_left (n : nat) :
    cwPair (2 * n + 1) =
      let p := cwPair n in (fst p, fst p + snd p).
Proof.
  replace (2 * n + 1) with (S (2 * n)) by lia.
  rewrite cwPair_unfold_succ.
  replace ((2 * n) / 2) with n by
    (symmetry; rewrite Nat.mul_comm; apply Nat.div_mul; lia).
  rewrite Nat.even_even.
  reflexivity.
Qed.

Theorem cwPair_right (n : nat) :
    cwPair (2 * n + 2) =
      let p := cwPair n in (fst p + snd p, snd p).
Proof.
  replace (2 * n + 2) with (S (2 * n + 1)) by lia.
  rewrite cwPair_unfold_succ.
  replace ((2 * n + 1) / 2) with n.
  - rewrite Nat.even_odd.
    reflexivity.
  - replace (2 * n + 1) with (Nat.b2n true + 2 * n) by (simpl; lia).
    rewrite Nat.add_b2n_double_div2.
    reflexivity.
Qed.

Lemma coprime_add_right {a b : nat} :
    Coprime a b -> Coprime a (a + b).
Proof.
  intro h.
  unfold Coprime in *.
  rewrite Nat.add_comm.
  now rewrite Nat.gcd_add_diag_r.
Qed.

Lemma coprime_add_left {a b : nat} :
    Coprime a b -> Coprime (a + b) b.
Proof.
  intro h.
  unfold Coprime in *.
  rewrite Nat.gcd_comm.
  rewrite Nat.gcd_add_diag_r.
  now rewrite Nat.gcd_comm.
Qed.

Theorem cwPairFuel_pos (fuel n : nat) :
    0 < fst (cwPairFuel fuel n) /\ 0 < snd (cwPairFuel fuel n).
Proof.
  revert n.
  induction fuel as [|fuel ih]; intro n.
  - simpl. lia.
  - destruct n as [|m].
    + simpl. lia.
    + cbn [cwPairFuel fst snd].
      pose proof (ih (m / 2)) as hp.
      destruct (cwPairFuel fuel (m / 2)) as [a b] eqn:Hp.
      cbn [fst snd] in hp |- *.
      cbn [fst snd].
      destruct hp as [ha hb].
      destruct (Nat.even m); cbn [fst snd]; lia.
Qed.

Theorem cwPair_pos (n : nat) :
    0 < fst (cwPair n) /\ 0 < snd (cwPair n).
Proof.
  apply cwPairFuel_pos.
Qed.

Theorem cwPairFuel_coprime (fuel n : nat) :
    Coprime (fst (cwPairFuel fuel n)) (snd (cwPairFuel fuel n)).
Proof.
  revert n.
  induction fuel as [|fuel ih]; intro n.
  - reflexivity.
  - destruct n as [|m].
    + reflexivity.
    + cbn [cwPairFuel fst snd].
      pose proof (ih (m / 2)) as hc.
      destruct (cwPairFuel fuel (m / 2)) as [a b] eqn:Hp.
      cbn [fst snd] in hc |- *.
      cbn [fst snd].
      destruct (Nat.even m).
      * cbn [fst snd]. now apply coprime_add_right.
      * cbn [fst snd]. now apply coprime_add_left.
Qed.

Theorem cwPair_coprime (n : nat) :
    Coprime (fst (cwPair n)) (snd (cwPair n)).
Proof.
  apply cwPairFuel_coprime.
Qed.

(* ## Inverse index and the pair <-> position round-trips *)

Fixpoint cwIndexFuel (fuel a b : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
      if ((a =? 0) || (b =? 0))%bool then 0
      else if a =? b then 0
      else if a <? b
           then 2 * cwIndexFuel fuel' a (b - a) + 1
           else 2 * cwIndexFuel fuel' (a - b) b + 2
  end.

Definition cwIndex (a b : nat) : nat :=
  cwIndexFuel (a + b + 1) a b.

Theorem cwIndexFuel_ge (a b fuel : nat) :
    a + b + 1 <= fuel -> cwIndexFuel fuel a b = cwIndex a b.
Proof.
  revert a b.
  induction fuel as [fuel ih] using lt_wf_ind.
  intros a b hle.
  destruct fuel as [|fuel']; [lia|].
  unfold cwIndex.
  replace (a + b + 1) with (S (a + b)) by lia.
  cbn [cwIndexFuel].
  destruct (((a =? 0) || (b =? 0))%bool) eqn:hz.
  - reflexivity.
  - apply Bool.orb_false_iff in hz as [ha0 hb0].
    apply Nat.eqb_neq in ha0.
    apply Nat.eqb_neq in hb0.
    destruct (a =? b) eqn:heq.
    + reflexivity.
    + apply Nat.eqb_neq in heq.
      destruct (a <? b) eqn:hlt.
      * apply Nat.ltb_lt in hlt.
        rewrite (ih fuel') by lia.
        rewrite (ih (a + b)) by lia.
        reflexivity.
      * apply Nat.ltb_ge in hlt.
        rewrite (ih fuel') by lia.
        rewrite (ih (a + b)) by lia.
        reflexivity.
Qed.

Theorem cwIndex_eq_of_eq {a b : nat} (ha : 0 < a) (hb : 0 < b) (h : a = b) :
    cwIndex a b = 0.
Proof.
  subst a.
  unfold cwIndex.
  replace (b + b + 1) with (S (b + b)) by lia.
  cbn [cwIndexFuel].
  replace (b =? 0) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (b =? b) with true by (symmetry; apply Nat.eqb_refl).
  reflexivity.
Qed.

(* Unfolding one layer of [cwIndex] on a pair of distinct positive arguments
   is the same work in both recursive branches: discharge the three "not
   zero, not equal" guards, then take the [a <? b] branch and re-fold the
   fuelled recursion.  Only the direction of that last test differs, so it is
   passed in, together with the [ltb] lemma that decides it. *)
Ltac cwIndex_step a b lt_val lt_lemma :=
  unfold cwIndex at 1;
  replace (a + b + 1) with (S (a + b)) by lia;
  cbn [cwIndexFuel];
  replace (a =? 0) with false by (symmetry; apply Nat.eqb_neq; lia);
  replace (b =? 0) with false by (symmetry; apply Nat.eqb_neq; lia);
  replace (a =? b) with false by (symmetry; apply Nat.eqb_neq; lia);
  replace (a <? b) with lt_val by (symmetry; apply lt_lemma; lia);
  cbn;
  rewrite cwIndexFuel_ge by lia;
  reflexivity.

Theorem cwIndex_left {a b : nat} (ha : 0 < a) (h : a < b) :
    cwIndex a b = 2 * cwIndex a (b - a) + 1.
Proof. cwIndex_step a b true Nat.ltb_lt. Qed.

Theorem cwIndex_right {a b : nat} (hb : 0 < b) (h : b < a) :
    cwIndex a b = 2 * cwIndex (a - b) b + 2.
Proof. cwIndex_step a b false Nat.ltb_ge. Qed.

Theorem coprime_sub_right {a b : nat} (h : a < b) (hc : Coprime a b) :
    Coprime a (b - a).
Proof.
  unfold Coprime in *.
  now rewrite Nat.gcd_sub_diag_r by lia.
Qed.

Theorem coprime_sub_left {a b : nat} (h : b < a) (hc : Coprime a b) :
    Coprime (a - b) b.
Proof.
  unfold Coprime in *.
  rewrite Nat.gcd_comm.
  rewrite Nat.gcd_sub_diag_r by lia.
  now rewrite Nat.gcd_comm.
Qed.

Theorem cwPair_cwIndex (a b : nat) (ha : 0 < a) (hb : 0 < b)
    (hc : Coprime a b) :
    cwPair (cwIndex a b) = (a, b).
Proof.
  remember (a + b) as s eqn:hs.
  revert a b hs ha hb hc.
  induction s as [s ih] using lt_wf_ind.
  intros a b hs ha hb hc.
  destruct (Nat.lt_trichotomy a b) as [hlt | [heq | hgt]].
  - assert (hbsub : 0 < b - a) by lia.
    pose proof (ih (a + (b - a)) ltac:(lia)
      a (b - a) eq_refl ha hbsub (coprime_sub_right hlt hc)) as hp.
    rewrite (cwIndex_left ha hlt).
    rewrite cwPair_left.
    rewrite hp.
    cbn [fst snd].
    f_equal; lia.
  - subst a.
    unfold Coprime in hc.
    rewrite Nat.gcd_diag in hc.
    assert (hb1 : b = 1) by lia.
    subst b.
    rewrite cwIndex_eq_of_eq by lia.
    reflexivity.
  - assert (hasub : 0 < a - b) by lia.
    pose proof (ih ((a - b) + b) ltac:(lia)
      (a - b) b eq_refl hasub hb (coprime_sub_left hgt hc)) as hp.
    rewrite (cwIndex_right hb hgt).
    rewrite cwPair_right.
    rewrite hp.
    cbn [fst snd].
    f_equal; lia.
Qed.

(* The even/odd splits of [m] via [Nat.div2] recur four times in the two
   proofs below; factor them into named lemmas.  Both are the one Euclidean
   split below, read at the two possible parities: stating it with the parity
   as a [b2n] summand lets each case be settled by [lia] after deciding
   [Nat.odd m], instead of re-deriving the parity fact by hand. *)
Lemma div2_split (m : nat) : m = 2 * (m / 2) + Nat.b2n (Nat.odd m).
Proof.
  pose proof (Nat.div2_odd m) as hsplit.
  rewrite <- Nat.div2_div. lia.
Qed.

Lemma even_double {m : nat} (h : Nat.even m = true) : m = 2 * (m / 2).
Proof.
  pose proof (div2_split m) as hs.
  rewrite <- Nat.negb_odd in h.
  destruct (Nat.odd m); simpl in *; [discriminate | lia].
Qed.

Lemma odd_double {m : nat} (h : Nat.even m = false) : m = 2 * (m / 2) + 1.
Proof.
  pose proof (div2_split m) as hs.
  rewrite <- Nat.negb_odd in h.
  destruct (Nat.odd m); simpl in *; [lia | discriminate].
Qed.

Theorem cwIndex_cwPair (n : nat) :
    cwIndex (fst (cwPair n)) (snd (cwPair n)) = n.
Proof.
  induction n as [n ih] using lt_wf_ind.
  destruct n as [|m].
  - rewrite cwPair_zero.
    cbn [fst snd].
    now rewrite cwIndex_eq_of_eq by lia.
  - rewrite cwPair_unfold_succ.
    pose proof (cwPair_pos (m / 2)) as hp.
    pose proof (ih (m / 2) (div2_lt_succ m)) as ihp.
    destruct (cwPair (m / 2)) as [a b] eqn:Hp.
    cbn [fst snd] in hp, ihp |- *.
    destruct hp as [ha hb].
    destruct (Nat.even m) eqn:heven.
    + pose proof (even_double heven) as hm.
      cbn [fst snd].
      assert (hidx : cwIndex a (a + b) = 2 * cwIndex a (a + b - a) + 1).
      { apply cwIndex_left; lia. }
      rewrite hidx.
      replace (a + b - a) with b by lia.
      rewrite ihp.
      lia.
    + pose proof (odd_double heven) as hm.
      cbn [fst snd].
      assert (hidx : cwIndex (a + b) b = 2 * cwIndex (a + b - b) b + 2).
      { apply cwIndex_right; lia. }
      rewrite hidx.
      replace (a + b - b) with a by lia.
      rewrite ihp.
      lia.
Qed.

(* ## Bridge to Q and the orbit map *)

Definition pairNext (p : nat * nat) : nat * nat :=
  let a := fst p in
  let b := snd p in
  (b, (2 * (a / b) + 1) * b - a).

Theorem div_lt_mul_add (a b : nat) (hb : 0 < b) :
    a < (a / b) * b + b.
Proof.
  pose proof (Nat.div_mod a b ltac:(lia)) as h.
  pose proof (Nat.mod_upper_bound a b ltac:(lia)) as hm.
  rewrite h at 1.
  rewrite Nat.mul_comm.
  lia.
Qed.

Theorem pairNext_left_child (a b : nat) (hb : 0 < b) :
    pairNext (a, a + b) = (a + b, b).
Proof.
  unfold pairNext.
  cbn [fst snd].
  rewrite Nat.div_small by lia.
  f_equal.
  assert (hle : a <= (2 * 0 + 1) * (a + b)) by lia.
  lia.
Qed.

Theorem pairNext_right_child_arith {a b : nat} (hb : 0 < b) :
    b + ((2 * (a / b) + 1) * b - a) =
      (2 * (a / b + 1) + 1) * b - (a + b).
Proof.
  pose proof (div_lt_mul_add a b hb) as hlt.
  assert (hle1 : a <= (2 * (a / b) + 1) * b) by lia.
  assert (hle2 : a + b <= (2 * (a / b + 1) + 1) * b) by lia.
  lia.
Qed.

Theorem cwPair_succ (n : nat) : cwPair (n + 1) = pairNext (cwPair n).
Proof.
  induction n as [n ih] using lt_wf_ind.
  destruct n as [|m].
  - reflexivity.
  - destruct (Nat.even m) eqn:heven.
    + pose proof (even_double heven) as hm.
      replace (S m + 1) with (2 * (m / 2) + 2) by lia.
      replace (S m) with (2 * (m / 2) + 1) by lia.
      rewrite cwPair_right.
      rewrite cwPair_left.
      pose proof (cwPair_pos (m / 2)) as hp.
      destruct (cwPair (m / 2)) as [a b] eqn:Hp.
      cbn [fst snd] in hp |- *.
      rewrite pairNext_left_child by lia.
      reflexivity.
    + pose proof (odd_double heven) as hm.
      replace (S m + 1) with (2 * (m / 2 + 1) + 1) by lia.
      replace (S m) with (2 * (m / 2) + 2) by lia.
      rewrite cwPair_left.
      rewrite cwPair_right.
      rewrite (ih (m / 2)) by apply div2_lt_succ.
      pose proof (cwPair_pos (m / 2)) as hp.
      destruct (cwPair (m / 2)) as [a b] eqn:Hp.
      cbn [fst snd] in hp |- *.
      unfold pairNext.
      cbn [fst snd].
      destruct hp as [_ hb].
      assert (hdiv : (a + b) / b = a / b + 1).
      { replace (a + b) with (1 * b + a) by lia.
        rewrite Nat.div_add_l by lia.
        lia.
      }
      rewrite hdiv.
      f_equal.
      exact (pairNext_right_child_arith hb).
Qed.

Definition positiveDenOfNat (b : nat) : positive :=
  Pos.of_succ_nat (Nat.pred b).

Lemma Zpos_positiveDenOfNat (b : nat) (hb : 0 < b) :
    Z.pos (positiveDenOfNat b) = Z.of_nat b.
Proof.
  unfold positiveDenOfNat.
  rewrite Zpos_P_of_succ_nat.
  destruct b as [|b]; [lia|].
  simpl.
  lia.
Qed.

Definition pairRat (p : nat * nat) : Q :=
  Qmake (Z.of_nat (fst p)) (positiveDenOfNat (snd p)).

Definition qOfNat (n : nat) : Q :=
  inject_Z (Z.of_nat n).

Definition qfloorNat (q : Q) : nat :=
  Z.to_nat ((Qnum q / Z.pos (Qden q))%Z).

Theorem qfloorNat_pairRat (a b : nat) (hb : 0 < b) :
    qfloorNat (pairRat (a, b)) = a / b.
Proof.
  unfold qfloorNat, pairRat.
  cbn [fst snd Qnum Qden].
  rewrite Zpos_positiveDenOfNat by lia.
  rewrite Z2Nat.inj_div by lia.
  rewrite Nat2Z.id.
  rewrite Nat2Z.id.
  reflexivity.
Qed.

Theorem pairRat_eq_div (a b : nat) (hb : 0 < b) :
    Qeq (pairRat (a, b)) (Qdiv (qOfNat a) (qOfNat b)).
Proof.
  unfold pairRat, qOfNat.
  cbn [fst snd].
  rewrite <- (Zpos_positiveDenOfNat b hb).
  apply Qmake_Qdiv.
Qed.

Theorem qOfNat_nonzero (n : nat) (hn : 0 < n) :
    ~ Qeq (qOfNat n) (inject_Z 0%Z).
Proof.
  unfold qOfNat, inject_Z, Qeq.
  cbn.
  lia.
Qed.

Definition rationalNext (q : Q) : Q :=
  Qinv (Qplus (Qminus (inject_Z 1%Z) q)
    (Qmult (inject_Z 2%Z) (qOfNat (qfloorNat q)))).

Theorem pairNext_den_pos (a b : nat) (hb : 0 < b) :
    0 < snd (pairNext (a, b)).
Proof.
  unfold pairNext.
  cbn [fst snd].
  pose proof (div_lt_mul_add a b hb).
  lia.
Qed.

Local Open Scope Q_scope.

Theorem rationalNext_pairRat_eq (a b : nat) (hb : (0 < b)%nat) :
    rationalNext (pairRat (a, b)) = pairRat (pairNext (a, b)).
Proof.
  unfold rationalNext.
  rewrite qfloorNat_pairRat by lia.
  unfold pairRat, pairNext, qOfNat.
  cbn [fst snd].
  unfold Qminus, Qplus, Qopp, Qmult, Qinv, inject_Z.
  cbn [Qnum Qden].
  rewrite !Zpos_positiveDenOfNat by
    (pose proof (div_lt_mul_add a b hb); lia).
  set (d := ((2 * (a / b) + 1) * b - a)%nat).
  assert (hdpos : (0 < d)%nat).
  { subst d. pose proof (div_lt_mul_add a b hb). lia. }
  assert (hnum :
    ((1 * Z.of_nat b + - Z.of_nat a * 1) * Z.pos (1 * 1) +
      2 * Z.of_nat (a / b) * Z.pos (1 * positiveDenOfNat b))%Z =
      Z.pos (positiveDenOfNat d)).
  { rewrite Zpos_positiveDenOfNat by exact hdpos.
    subst d.
    rewrite Nat2Z.inj_sub by
      (pose proof (div_lt_mul_add a b hb); lia).
    rewrite Nat2Z.inj_mul.
    repeat rewrite Nat2Z.inj_add.
    repeat rewrite Pos.mul_1_l.
    rewrite Zpos_positiveDenOfNat by exact hb.
    rewrite Nat2Z.inj_mul.
    ring.
  }
  rewrite hnum.
  cbn.
  repeat rewrite Pos.mul_1_l.
  repeat rewrite Pos.mul_1_r.
  rewrite Zpos_positiveDenOfNat by exact hb.
  reflexivity.
Qed.

(** The setoid form is a direct consequence of the syntactic identity. *)
Theorem rationalNext_pairRat (a b : nat) (hb : (0 < b)%nat) :
    rationalNext (pairRat (a, b)) == pairRat (pairNext (a, b)).
Proof.
  rewrite rationalNext_pairRat_eq by exact hb.
  reflexivity.
Qed.

Definition cwRat (n : nat) : Q :=
  pairRat (cwPair n).

Theorem rationalNext_cwRat_eq (n : nat) :
    rationalNext (cwRat n) = cwRat (n + 1).
Proof.
  unfold cwRat.
  rewrite cwPair_succ.
  destruct (cwPair n) as [a b] eqn:Hp.
  pose proof (cwPair_pos n) as hpos.
  rewrite Hp in hpos.
  apply rationalNext_pairRat_eq.
  cbn [snd] in hpos.
  lia.
Qed.

Theorem rationalNext_cwRat (n : nat) :
    rationalNext (cwRat n) == cwRat (n + 1).
Proof.
  rewrite rationalNext_cwRat_eq.
  reflexivity.
Qed.

Fixpoint rationalFloorOrbit (n : nat) : Q :=
  match n with
  | O => inject_Z 0%Z
  | S n' => rationalNext (rationalFloorOrbit n')
  end.

Theorem rationalFloorOrbit_zero : rationalFloorOrbit 0 = inject_Z 0%Z.
Proof. reflexivity. Qed.

Theorem rationalNext_zero : rationalNext (inject_Z 0%Z) =
    pairRat (1%nat, 1%nat).
Proof. reflexivity. Qed.

Theorem rationalFloorOrbit_succ (n : nat) :
    rationalFloorOrbit (n + 1) = cwRat n.
Proof.
  induction n as [|n ih].
  - change (rationalNext (inject_Z 0%Z) = cwRat 0).
    rewrite rationalNext_zero.
    unfold cwRat.
    now rewrite cwPair_zero.
  - change (rationalNext (rationalFloorOrbit (n + 1)) = cwRat (S n)).
    rewrite ih.
    rewrite <- Nat.add_1_r.
    exact (rationalNext_cwRat_eq n).
Qed.

Theorem pairRat_ne_zero {a b : nat} (ha : (0 < a)%nat) :
    ~ pairRat (a, b) == inject_Z 0%Z.
Proof.
  unfold pairRat, inject_Z, Qeq.
  cbn [fst snd Qnum Qden].
  lia.
Qed.

Theorem cwRat_ne_zero (n : nat) :
    ~ cwRat n == inject_Z 0%Z.
Proof.
  unfold cwRat.
  pose proof (cwPair_pos n) as hpos.
  destruct (cwPair n) as [a b] eqn:Hp.
  cbn [fst] in hpos.
  apply pairRat_ne_zero.
  lia.
Qed.

Theorem rationalFloorOrbit_eq_zero_iff (n : nat) :
    rationalFloorOrbit n == inject_Z 0%Z <-> n = 0%nat.
Proof.
  split.
  - intro h.
    destruct n as [|n].
    + reflexivity.
    + replace (S n) with (n + 1)%nat in h by lia.
      rewrite rationalFloorOrbit_succ in h.
      exfalso.
      exact (cwRat_ne_zero n h).
  - intro h.
    subst n.
    reflexivity.
Qed.

(* ## Injectivity and the exactly-once enumeration *)

Lemma positiveDenOfNat_pos_to_nat (p : positive) :
    positiveDenOfNat (Pos.to_nat p) = p.
Proof.
  apply Pos2Z.inj.
  rewrite Zpos_positiveDenOfNat by apply Pos2Nat.is_pos.
  apply positive_nat_Z.
Qed.

Definition qredNumNat (q : Q) : nat :=
  Z.to_nat (Qnum (Qred q)).

Definition qredDenNat (q : Q) : nat :=
  Pos.to_nat (Qden (Qred q)).

Lemma Qred_num_nonneg (q : Q) (hq : 0 <= q) :
    (0 <= Qnum (Qred q))%Z.
Proof.
  pose proof (proj2 (Qred_le (inject_Z 0%Z) q) hq) as hred.
  change (0 <= Qred q) in hred.
  unfold Qle in hred.
  cbn in hred.
  rewrite Z.mul_1_r in hred.
  exact hred.
Qed.

Lemma qredDenNat_pos (q : Q) : (0 < qredDenNat q)%nat.
Proof.
  unfold qredDenNat.
  apply Pos2Nat.is_pos.
Qed.

Theorem pairRat_of_Qred_nonneg (q : Q) (hq : 0 <= q) :
    pairRat (qredNumNat q, qredDenNat q) == q.
Proof.
  pose proof (Qred_num_nonneg q hq) as hnum.
  eapply Qeq_trans with (y := Qred q).
  - unfold qredNumNat, qredDenNat, pairRat, Qeq.
    cbn [fst snd Qnum Qden].
    rewrite Z2Nat.id by exact hnum.
    rewrite positiveDenOfNat_pos_to_nat.
    reflexivity.
  - apply Qred_correct.
Qed.

Lemma qredNumNat_pos_of_nonneg_nonzero (q : Q)
    (hq : 0 <= q) (hnez : ~ q == inject_Z 0%Z) :
    (0 < qredNumNat q)%nat.
Proof.
  unfold qredNumNat.
  pose proof (Qred_num_nonneg q hq) as hnonneg.
  assert (hnum_ne : Qnum (Qred q) <> 0%Z).
  { intro hnum.
    apply hnez.
    eapply Qeq_trans.
    - apply Qeq_sym. apply Qred_correct.
    - unfold Qeq.
      rewrite hnum.
      cbn [Qnum Qden inject_Z].
      lia.
  }
  assert (hpos : (0 < Qnum (Qred q))%Z) by lia.
  destruct (Z.to_nat (Qnum (Qred q))) as [|n] eqn:hnat.
  - exfalso.
    pose proof (Z2Nat.id (Qnum (Qred q)) hnonneg) as hid.
    rewrite hnat in hid.
    simpl in hid.
    lia.
  - lia.
Qed.

Lemma pos_divide_of_nat_divide (p a : positive) :
    Nat.divide (Pos.to_nat p) (Pos.to_nat a) -> (p | a)%positive.
Proof.
  intros [z hz].
  destruct z as [|z].
  - exfalso.
    rewrite Nat.mul_0_l in hz.
    pose proof (Pos2Nat.is_pos a).
    lia.
  - exists (Pos.of_succ_nat z).
    apply Pos2Nat.inj.
    rewrite Pos2Nat.inj_mul.
    rewrite SuccNat2Pos.id_succ.
    exact hz.
Qed.

Lemma pos_ggcd_outputs_coprime_nat (a b g aa bb : positive)
    (h : Pos.ggcd a b = (g, (aa, bb))) :
    Coprime (Pos.to_nat aa) (Pos.to_nat bb).
Proof.
  unfold Coprime.
  apply Nat.gcd_unique.
  - exists (Pos.to_nat aa). lia.
  - exists (Pos.to_nat bb). lia.
  - intros q hqa hqb.
    destruct q as [|q].
    + destruct hqa as [z hz].
      rewrite Nat.mul_0_r in hz.
      pose proof (Pos2Nat.is_pos aa).
      lia.
    + set (p := Pos.of_succ_nat q).
      assert (hpaa : (p | aa)%positive).
      { apply pos_divide_of_nat_divide.
        unfold p.
        rewrite SuccNat2Pos.id_succ.
        exact hqa.
      }
      assert (hpbb : (p | bb)%positive).
      { apply pos_divide_of_nat_divide.
        unfold p.
        rewrite SuccNat2Pos.id_succ.
        exact hqb.
      }
      pose proof (Pos.ggcd_greatest a b) as hg.
      rewrite h in hg.
      cbn in hg.
      specialize (hg p hpaa hpbb).
      exists 1%nat.
      unfold p in hg.
      apply (f_equal Pos.to_nat) in hg.
      rewrite SuccNat2Pos.id_succ in hg.
      rewrite Pos2Nat.inj_1 in hg.
      lia.
Qed.

Theorem qred_pair_coprime (q : Q) (hq : 0 <= q) :
    Coprime (qredNumNat q) (qredDenNat q).
Proof.
  destruct q as [n d].
  unfold qredNumNat, qredDenNat, Qred.
  cbn [Qnum Qden].
  destruct n as [|p|p].
  - unfold Coprime. reflexivity.
  - destruct (Pos.ggcd p d) as [g [aa bb]] eqn:hg.
    cbn [Z.ggcd snd].
    rewrite hg.
    cbn [snd Qnum Qden].
    rewrite Z2Nat.inj_pos.
    rewrite Pos2Z.id.
    apply pos_ggcd_outputs_coprime_nat with (a := p) (b := d) (g := g).
    exact hg.
  - unfold Qle in hq.
    cbn [Qnum Qden inject_Z] in hq.
    lia.
Qed.

Theorem pairRat_inj {a b c d : nat}
    (hb : (0 < b)%nat) (hd : (0 < d)%nat)
    (hab : Coprime a b) (hcd : Coprime c d)
    (h : pairRat (a, b) == pairRat (c, d)) :
    a = c /\ b = d.
Proof.
  assert (hcross : (a * d = c * b)%nat).
  { unfold pairRat, Qeq in h.
    cbn [fst snd Qnum Qden] in h.
    rewrite !Zpos_positiveDenOfNat in h by lia.
    apply Nat2Z.inj.
    rewrite !Nat2Z.inj_mul.
    exact h.
  }
  assert (hbdivd : Nat.divide b d).
  { apply (Nat.gauss b a d).
    - exists c.
      rewrite hcross.
      lia.
    - rewrite Nat.gcd_comm.
      exact hab.
  }
  assert (hddivb : Nat.divide d b).
  { apply (Nat.gauss d c b).
    - exists a.
      rewrite <- hcross.
      lia.
    - rewrite Nat.gcd_comm.
      exact hcd.
  }
  assert (hbd : b = d) by (apply Nat.divide_antisym; assumption).
  subst d.
  split; [|reflexivity].
  apply (proj1 (Nat.mul_cancel_r a c b (ltac:(lia)))).
  exact hcross.
Qed.

Theorem rationalFloorOrbit_exists_pair (a b : nat)
    (ha : (0 < a)%nat) (hb : (0 < b)%nat) (hc : Coprime a b) :
    rationalFloorOrbit (cwIndex a b + 1) == pairRat (a, b).
Proof.
  rewrite rationalFloorOrbit_succ.
  unfold cwRat.
  rewrite cwPair_cwIndex by assumption.
  reflexivity.
Qed.

Theorem rationalFloorOrbit_exists_of_nonneg_nonzero_reduced_coprime
    (q : Q) (hq : 0 <= q) (hnez : ~ q == inject_Z 0%Z)
    (hc : Coprime (qredNumNat q) (qredDenNat q)) :
    rationalFloorOrbit (cwIndex (qredNumNat q) (qredDenNat q) + 1) == q.
Proof.
  rewrite rationalFloorOrbit_succ.
  unfold cwRat.
  rewrite cwPair_cwIndex.
  - apply pairRat_of_Qred_nonneg; exact hq.
  - apply qredNumNat_pos_of_nonneg_nonzero; assumption.
  - apply qredDenNat_pos.
  - exact hc.
Qed.

Theorem rationalFloorOrbit_exists_of_nonneg_nonzero
    (q : Q) (hq : 0 <= q) (hnez : ~ q == inject_Z 0%Z) :
    rationalFloorOrbit (cwIndex (qredNumNat q) (qredDenNat q) + 1) == q.
Proof.
  apply rationalFloorOrbit_exists_of_nonneg_nonzero_reduced_coprime;
    try assumption.
  apply qred_pair_coprime.
  exact hq.
Qed.

Theorem rationalFloorOrbit_unique_of_nonneg_nonzero
    (q : Q) (n : nat) (hq : 0 <= q) (hnez : ~ q == inject_Z 0%Z)
    (hn : rationalFloorOrbit n == q) :
    n = (cwIndex (qredNumNat q) (qredDenNat q) + 1)%nat.
Proof.
  destruct n as [|k].
  - exfalso.
    apply hnez.
    apply Qeq_sym.
    exact hn.
  - replace (S k) with (k + 1)%nat in hn by lia.
    rewrite rationalFloorOrbit_succ in hn.
    destruct (cwPair k) as [a b] eqn:hpair.
    pose proof (cwPair_pos k) as hpos.
    pose proof (cwPair_coprime k) as hc.
    rewrite hpair in hpos, hc.
    cbn [fst snd] in hpos, hc.
    unfold cwRat in hn.
    rewrite hpair in hn.
    pose proof (pairRat_of_Qred_nonneg q hq) as hqpair.
    assert (hpairs :
        pairRat (a, b) == pairRat (qredNumNat q, qredDenNat q)).
    { eapply Qeq_trans; [exact hn|].
      apply Qeq_sym.
      exact hqpair.
    }
    pose proof (pairRat_inj (a := a) (b := b)
      (c := qredNumNat q) (d := qredDenNat q)
      (ltac:(destruct hpos; lia)) (qredDenNat_pos q)
      hc (qred_pair_coprime q hq) hpairs) as [haeq hbeq].
    pose proof (cwIndex_cwPair k) as hidx.
    rewrite hpair in hidx.
    cbn [fst snd] in hidx.
    subst a b.
    lia.
Qed.

Theorem rationalFloorOrbit_visits_each_nonnegative_rat_exactly_once
    (q : Q) (hq : 0 <= q) :
    exists n : nat, rationalFloorOrbit n == q /\
      forall m : nat, rationalFloorOrbit m == q -> m = n.
Proof.
  destruct (Qeq_dec q (inject_Z 0%Z)) as [hzero|hnez].
  - exists 0%nat.
    split.
    + apply Qeq_sym.
      exact hzero.
    + intros m hm.
      apply rationalFloorOrbit_eq_zero_iff.
      eapply Qeq_trans; [exact hm|exact hzero].
  - exists (cwIndex (qredNumNat q) (qredDenNat q) + 1)%nat.
    split.
    + apply rationalFloorOrbit_exists_of_nonneg_nonzero; assumption.
    + intros m hm.
      apply rationalFloorOrbit_unique_of_nonneg_nonzero with (q := q);
        assumption.
Qed.

Local Open Scope nat_scope.

(* ## Executable spot checks *)

Theorem pairRat_first_values :
    map pairRat [(1, 1); (1, 2); (2, 1); (1, 3)] =
      [Qmake 1 1; Qmake 1 2; Qmake 2 1; Qmake 1 3].
Proof.
  reflexivity.
Qed.

Theorem cwPair_first_values :
    map cwPair [0; 1; 2; 3; 4; 5; 6; 7] =
      [(1, 1); (1, 2); (2, 1); (1, 3);
       (3, 2); (2, 3); (3, 1); (1, 4)].
Proof.
  vm_compute. reflexivity.
Qed.

End RationalFloorOrbit.
End LeanProofs.
