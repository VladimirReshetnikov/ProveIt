(** * Sound224: every theorem of the 224's calculus is a theorem of K230's.

    Each enabled 224 bundle is derived in [thm230] from two K230 bundles: [bundle230 a b c]
    supplies the K core (equivalent to the fused core by double-negation cancellation) and the
    membership vacuity, and [bundle230 a b (wel a b)] supplies the restricted equality helper as
    its equality vacuity, since the binder [wel a b] differs from both endpoints. *)
From Stdlib Require Import Arith Lia List.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K230S Require Import KCode230 KQuotZFC.
From K230L Require Import Codes230 Thm230 Comp_Prop230 Consistency230.
From K224 Require Import Codes224 Thm224.
Import ListNotations.
Unset Implicit Arguments.

(** ** Provable equivalence of codes in [thm230] *)
Definition eqv (a b : nat) : Prop := thm230 (wim a b) /\ thm230 (wim b a).

Lemma eqv_refl a : eqv a a.
Proof. split; apply thm_I. Qed.

Lemma dni a : thm230 (wim a (wim (wim a 1) 1)).
Proof. apply der_thm. do 2 apply ded. apply (dmp _ a); hyp. Qed.

Lemma eqv_trans a b c : eqv a b -> eqv b c -> eqv a c.
Proof.
  intros [H1 H2] [H3 H4]. split; apply der_thm, ded.
  - apply (dmp _ b); [apply dthm, H3|]. apply (dmp _ a); [apply dthm, H1|hyp].
  - apply (dmp _ b); [apply dthm, H2|]. apply (dmp _ c); [apply dthm, H4|hyp].
Qed.

Lemma eqv_dn_l a b : eqv a b -> eqv (wim (wim a F) F) b.
Proof.
  intros H. apply (eqv_trans _ a); [|exact H]. split; [apply thm_DNE|apply dni].
Qed.

Lemma eqv_dn_r a b : eqv a b -> eqv a (wim (wim b F) F).
Proof.
  intros H. apply (eqv_trans _ b); [exact H|]. split; [apply dni|apply thm_DNE].
Qed.

Lemma eqv_wim a a' b b' : eqv a a' -> eqv b b' -> eqv (wim a b) (wim a' b').
Proof.
  intros [Ha1 Ha2] [Hb1 Hb2]. split; apply der_thm; do 2 apply ded.
  - apply (dmp _ b); [apply dthm, Hb1|]. apply (dmp _ a); [hyp|].
    apply (dmp _ a'); [apply dthm, Ha2|hyp].
  - apply (dmp _ b'); [apply dthm, Hb2|]. apply (dmp _ a'); [hyp|].
    apply (dmp _ a); [apply dthm, Ha1|hyp].
Qed.

Lemma imp_wal x a b : thm230 (wim a b) -> thm230 (wim (wal x a) (wal x b)).
Proof. intros H. exact (T_mp _ _ (T_gen x _ H) (T_r2 x a b)). Qed.

Lemma eqv_wal x a b : eqv a b -> eqv (wal x a) (wal x b).
Proof. intros [H1 H2]. split; apply imp_wal; assumption. Qed.

Local Opaque KCode230.P KCode230.wim KCode230.wal KCode230.wel KCode230.weq.

Ltac eqv_solve :=
  first
  [ apply eqv_refl
  | apply eqv_dn_l; eqv_solve
  | apply eqv_dn_r; eqv_solve
  | apply eqv_wim; eqv_solve
  | apply eqv_wal; eqv_solve ].

(** The three [E_x (A & B)] cancellation sites of the K core. *)
Lemma kcore_kf224 a b c : eqv (kcore a b c c) (kf224 a b c).
Proof.
  unfold kcore, ksubset, krequest, kf224, wa, wex, wn. eqv_solve.
Qed.

Local Transparent KCode230.wel KCode230.P.

Lemma wel_fresh a b : wel a b <> a /\ wel a b <> b.
Proof. unfold wel. pose proof (P_ge_l a b). pose proof (P_ge_r a b). lia. Qed.

Local Opaque KCode230.P KCode230.wel.

Lemma bundle224_thm230 a b c : c <> a -> c <> b -> thm230 (bundle224 a b c).
Proof.
  intros Ha Hb.
  pose proof (T_bundle a b c Ha Hb) as H1.
  destruct (wel_fresh a b) as [Hra Hrb].
  pose proof (T_bundle a b (wel a b) Hra Hrb) as H2.
  unfold bundle, bundle230 in H1, H2.
  assert (HK : thm230 (k230 a b c)) by (apply der_thm; eapply der_andl; apply dthm, H1).
  assert (HV : thm230 (vacuity230 a b c)) by (apply der_thm; eapply der_andr; apply dthm, H1).
  assert (HV2 : thm230 (vacuity230 a b (wel a b))) by (apply der_thm; eapply der_andr; apply dthm, H2).
  unfold vacuity230 in HV, HV2.
  assert (HR : thm230 (vrel a b c)) by (apply der_thm; eapply der_andl; apply dthm, HV).
  assert (HH : thm230 (helper224 a b)) by (apply der_thm; eapply der_andr; apply dthm, HV2).
  assert (HF : thm230 (kf224 a b c)) by (exact (T_mp _ _ HK (proj1 (kcore_kf224 a b c)))).
  unfold bundle224, wn. apply der_thm, ded.
  apply (dmp _ (helper224 a b)); [|apply dthm, HH].
  apply (dmp _ (vrel a b c)); [|apply dthm, HR].
  apply (dmp _ (kf224 a b c)); [hyp|apply dthm, HF].
Qed.

Theorem thm224_thm230 n : thm224 n -> thm230 n.
Proof.
  induction 1.
  - exact T_true.
  - exact (T_mp _ _ IHthm224_1 IHthm224_2).
  - exact (T_gen _ _ IHthm224).
  - apply T_r1.
  - apply T_r2.
  - apply T_r3.
  - apply T_r4.
  - apply T_r5.
  - apply T_r6.
  - apply T_r7.
  - apply T_r8.
  - now apply bundle224_thm230.
Qed.

(** Soundness: a numerical refutation in the 224's calculus is a ZFC inconsistency. *)
Theorem thm224_sound : thm224 1 -> StandardZFC ⊢TC ⊥.
Proof. intros H. apply thm230_iff_standardZFC, thm224_thm230, H. Qed.

Print Assumptions thm224_sound.
