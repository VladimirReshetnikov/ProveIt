(** * Bundle254: the gated AX bundle as a named wff, and its decoding / encoding.

      BW a b c phi = ((BC a b c) /\ (BG a b c phi)) /\ (BV a b c)
    BC: container (CP at the free point c), BG: global-image collection over the free domain b with
    matrix phi and collection-set label c, BV: atomic vacuity.  The machine's bundle a b c is
    BW a b c (D c), with c both the matrix code and the label. *)
From Coq Require Import Arith Lia.
From ZF Require Import Logic.
From M254L Require Import Codes254 Wff254.

Definition BC (a b c : nat) : wff :=
  Wex b (Wa (Wal a (Wim (Wel a b)
                        (Wa (Wex c (Wa (Wal b (Wim (Wal c (Wim (Wel c b) (Wel c a))) (Wel b c)))
                                       (Wel c b)))
                            (Wal c (Wim (Wel c a) (Wel c b))))))
            (Wel c b)).

Definition BG (a b c : nat) (phi : wff) : wff :=
  Wex c (Wa (Wal a (Wim (Wel a b) (Wal b (Wim phi (Wex b (Wa phi (Wel b c)))))))
            (Wal b (Wim (Wel b c) (Wex a phi)))).

Definition BV (a b c : nat) : wff :=
  Wa (Wim (Wel a b) (Wal c (Wel a b))) (Wim (Weq a b) (Wal c (Weq a b))).

Definition BW (a b c : nat) (phi : wff) : wff := Wa (Wa (BC a b c) (BG a b c phi)) (BV a b c).

(** ** Side conditions *)
Lemma wel_ne1 x y : (x, y) <> (0, 0) -> wel x y <> 1.
Proof.
  intros H E. unfold wel in E. assert (P x y = 0) by lia. apply P_0 in H0 as [-> ->]. now apply H.
Qed.

Lemma pair_ne00_l x y : x <> 0 -> (x, y) <> (0, 0).
Proof. intros H E. injection E as -> ->. now apply H. Qed.
Lemma pair_ne00_r x y : y <> 0 -> (x, y) <> (0, 0).
Proof. intros H E. injection E as -> ->. now apply H. Qed.

Lemma wel_ne0 x y : wel x y <> 0.        Proof. unfold wel. lia. Qed.
Lemma weq_ne0 x y : weq x y <> 0.        Proof. unfold weq. lia. Qed.
Lemma wal_ne0 x y : wal x y <> 0.        Proof. unfold wal. lia. Qed.
Lemma weq_ne1 x y : weq x y <> 1.        Proof. unfold weq. lia. Qed.
Lemma wal_ne1 x y : wal x y <> 1.        Proof. unfold wal. lia. Qed.
Lemma wn_ne0 a : wn a <> 0.
Proof. unfold wn, F. apply wim_pos_r. lia. Qed.
Lemma wex_ne0 x a : wex x a <> 0.        Proof. apply wn_ne0. Qed.
Lemma wa_ne0 a b : wa a b <> 0.          Proof. apply wn_ne0. Qed.
Lemma wn_ne1 a : wn a <> 1.              Proof. apply wim_ne_F. Qed.
Lemma wex_ne1 x a : wex x a <> 1.        Proof. apply wim_ne_F. Qed.
Lemma wa_ne1 a b : wa a b <> 1.          Proof. apply wim_ne_F. Qed.
Lemma wim_ne1 a b : wim a b <> 1.        Proof. apply wim_ne_F. Qed.
Lemma wim_ne0 a b : (a, b) <> (0, 0) -> wim a b <> 0.
Proof. intro H. pose proof (wim_pos a b H). lia. Qed.

Ltac sidec :=
  first [ assumption
        | apply wel_ne0 | apply weq_ne0 | apply wal_ne0 | apply wn_ne0 | apply wex_ne0 | apply wa_ne0
        | apply weq_ne1 | apply wal_ne1 | apply wn_ne1 | apply wex_ne1 | apply wa_ne1 | apply wim_ne1
        | (apply wel_ne1; first [ apply pair_ne00_l; congruence | apply pair_ne00_r; congruence ])
        | (apply pair_ne00_l; sidec) | (apply pair_ne00_r; sidec)
        | (apply wim_ne0; sidec) ].

Ltac Dsimp :=
  repeat first [ rewrite D_wa | rewrite D_wex | rewrite D_wn | rewrite D_wal | rewrite D_wel
               | rewrite D_weq | (rewrite D_wim by sidec) ].

Lemma D_bundle a b c : c <> a -> c <> b -> D (bundle a b c) = BW a b c (D c).
Proof.
  intros H1 H2. unfold bundle, bundleC, bundleG.
  assert (H1' : (c, a) <> (0, 0)) by (intro E; injection E as -> ->; now apply H1).
  assert (H2' : (c, b) <> (0, 0)) by (intro E; injection E as -> ->; now apply H2).
  assert (H3' : (b, c) <> (0, 0)) by (intro E; injection E as -> ->; now apply H2).
  assert (E1 : wel c a <> 1) by now apply wel_ne1.
  assert (E2 : wel c b <> 1) by now apply wel_ne1.
  assert (E3 : wel b c <> 1) by now apply wel_ne1.
  Dsimp. reflexivity.
Qed.
