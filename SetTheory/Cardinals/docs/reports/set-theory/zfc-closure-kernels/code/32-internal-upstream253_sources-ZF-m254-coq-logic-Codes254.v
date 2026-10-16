(** * Codes254: the numeric formula coding of the zfc_254 source program (zf/m254/inputs/source.py).

    Dual Cantor pairing  P a b = tri (a+b) + b,  with the source's unpair loop as inverse:
    one step maps (S a, b) to (a, S b) and (0, b) to (S b, 0).

    Formula codes (four constructors, no negation):
      Imp(A,B) = 4 P(A,B)    Rel(i,j) = 4 P(i,j) + 1    All(i,A) = 4 P(i,A) + 2    Eq(i,j) = 4 P(i,j) + 3
    F = 1 = Rel(0,0);  0 = Imp(0,0) ("truth", not the code of any finite formula).
    Derived:  wn A = A -> F,  wa A B = wn (A -> wn B),  wex x A = wn (All x (wn A)).

    The AX rows rho1..rho8 and the gated bundle are exactly the formulas the source's [axioms]
    method builds (validated in zf/m254/logic/spec.py, validate.py). *)
From Coq Require Import Arith Lia.

Fixpoint tri (n : nat) : nat := match n with 0 => 0 | S m => S m + tri m end.

Definition P (a b : nat) : nat := tri (a + b) + b.

Definition unP_step (o : nat * nat) : nat * nat :=
  match o with
  | (S a, b) => (a, S b)
  | (0, b) => (S b, 0)
  end.

Definition unP (z : nat) : nat * nat := Nat.iter z unP_step (0, 0).

Lemma tri_S n : tri (S n) = S n + tri n.
Proof. reflexivity. Qed.

Lemma P_unP_step a b : P (fst (unP_step (a, b))) (snd (unP_step (a, b))) = S (P a b).
Proof.
  unfold P. destruct a as [|a]; cbn [unP_step fst snd].
  - rewrite !Nat.add_0_r, !Nat.add_0_l. cbn [tri]. lia.
  - replace (a + S b) with (S a + b) by lia. lia.
Qed.

Lemma P_0 a b : P a b = 0 -> a = 0 /\ b = 0.
Proof.
  unfold P. destruct (a + b) as [|s] eqn:E; cbn [tri]; intro H; lia.
Qed.

(** every positive code has a predecessor along the unpair walk *)
Lemma P_pred a b : P a b <> 0 -> exists a' b', P a' b' + 1 = P a b /\ unP_step (a', b') = (a, b).
Proof.
  intro Hn. destruct b as [|b].
  - destruct a as [|a]; [unfold P in Hn; cbn in Hn; lia|].
    exists 0, a. split; [|reflexivity].
    pose proof (P_unP_step 0 a) as H. cbn [unP_step fst snd] in H. lia.
  - exists (S a), b. split; [|reflexivity].
    pose proof (P_unP_step (S a) b) as H. cbn [unP_step fst snd] in H. lia.
Qed.

Lemma unP_P a b : unP (P a b) = (a, b).
Proof.
  remember (P a b) as n eqn:E. revert a b E. induction n as [|n IH]; intros a b E.
  - symmetry in E. destruct (P_0 a b E) as [-> ->]. reflexivity.
  - destruct (P_pred a b ltac:(lia)) as [a' [b' [H1 H2]]].
    change (unP (S n)) with (unP_step (unP n)). rewrite (IH a' b') by lia. exact H2.
Qed.

Lemma P_unP z : P (fst (unP z)) (snd (unP z)) = z.
Proof.
  induction z as [|z IH]; [reflexivity|].
  change (unP (S z)) with (unP_step (unP z)). destruct (unP z) as [a b].
  rewrite P_unP_step. cbn [fst snd] in IH. now rewrite IH.
Qed.

Lemma P_ge_l a b : a <= P a b.
Proof.
  unfold P. assert (forall n, n <= tri n) by (induction n; cbn; lia).
  specialize (H (a + b)). lia.
Qed.

Lemma P_ge_r a b : b <= P a b.
Proof. unfold P. lia. Qed.

Lemma unP_le z : fst (unP z) <= z /\ snd (unP z) <= z.
Proof.
  pose proof (P_unP z) as E. pose proof (P_ge_l (fst (unP z)) (snd (unP z))).
  pose proof (P_ge_r (fst (unP z)) (snd (unP z))). lia.
Qed.

Lemma unP_0 : unP 0 = (0, 0).
Proof. reflexivity. Qed.

Lemma P_inj a b a' b' : P a b = P a' b' -> a = a' /\ b = b'.
Proof. intro H. pose proof (unP_P a b) as E. rewrite H, unP_P in E. now injection E. Qed.

(** ** Formula codes *)
Definition wim (a b : nat) : nat := 4 * P a b.
Definition wel (i j : nat) : nat := 4 * P i j + 1.
Definition wal (i a : nat) : nat := 4 * P i a + 2.
Definition weq (i j : nat) : nat := 4 * P i j + 3.
Definition F : nat := 1.
Definition wn (a : nat) : nat := wim a F.
Definition wa (a b : nat) : nat := wn (wim a (wn b)).
Definition wex (x a : nat) : nat := wn (wal x (wn a)).

Lemma wel_0_0 : wel 0 0 = F.
Proof. reflexivity. Qed.

(** ** The AX rows (paper App. A2 names; pushed rho8 first, rho1 ends on top) *)
Definition rho8 (a b c u : nat) : nat := wim (wim (wim c u) a) (wim (wim a c) (wim b c)).  (* L *)
Definition rho7 (a b c : nat) : nat := wim (weq c a) (wim (weq c b) (weq a b)).          (* Euclid *)
Definition rho6 (a b : nat) : nat := wim (wex a (wal a b)) b.                            (* B6c *)
Definition rho5 (a b c : nat) : nat := wim (weq c a) (wim (wel c b) (wel a b)).          (* cong left *)
Definition rho4 (a b c : nat) : nat := wim (wal a (wal b c)) (wal b (wal a c)).          (* commutation *)
Definition rho3 (a b c : nat) : nat := wim (weq a b) (wim (wel c a) (wel c b)).          (* cong right *)
Definition rho2 (a b c : nat) : nat := wim (wal a (wim b c)) (wim (wal a b) (wal a c)).  (* QI *)
Definition rho1 (a b : nat) : nat := wex a (weq a b).                                    (* E.a a=b *)

(** ** The gated bundle: container C, global-image collection G (c = matrix code = output-set
    label), atomic vacuity *)
Definition bundleC (a b c : nat) : nat :=
  wex b (wa (wal a (wim (wel a b)
                          (wa (wex c (wa (wal b (wim (wal c (wim (wel c b) (wel c a))) (wel b c)))
                                         (wel c b)))
                              (wal c (wim (wel c a) (wel c b))))))
            (wel c b)).
Definition bundleG (a b c : nat) : nat :=
  wex c (wa (wal a (wim (wel a b) (wal b (wim c (wex b (wa c (wel b c)))))))
            (wal b (wim (wel b c) (wex a c)))).
Definition bundle (a b c : nat) : nat :=
  wa (wa (bundleC a b c) (bundleG a b c))
     (wa (wim (wel a b) (wal c (wel a b))) (wim (weq a b) (wal c (weq a b)))).

(** ** Residues mod 4 (the NIP halting test compares with F = 1) *)
Lemma wim_ne_F a b : wim a b <> F.
Proof. unfold wim, F. lia. Qed.
Lemma wal_ne_F a b : wal a b <> F.
Proof. unfold wal, F. lia. Qed.
Lemma wn_ne_F a : wn a <> F.
Proof. apply wim_ne_F. Qed.
Lemma wex_ne_F x a : wex x a <> F.
Proof. apply wim_ne_F. Qed.
Lemma wa_ne_F a b : wa a b <> F.
Proof. apply wim_ne_F. Qed.
Lemma bundle_ne_F a b c : bundle a b c <> F.
Proof. apply wa_ne_F. Qed.

Lemma wim_pos_r a b : 0 < b -> wim a b <> 0.
Proof. unfold wim. pose proof (P_ge_r a b). lia. Qed.
