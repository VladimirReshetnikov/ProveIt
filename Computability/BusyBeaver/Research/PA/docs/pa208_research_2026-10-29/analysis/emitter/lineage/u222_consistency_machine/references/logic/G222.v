(** Copy of rocq224/src/G222.v (SHA256 9220953ff4dbfc3a6e2394450fe6f98b3e45a0d7f87a2f9737b8bcbfbe952206) under namespace K217F. *)
(** * G222: the merged equality row recovers reflexivity, the helper and rho7 (Source 128).

    With [r = wel x x], rho1 gives [Ex r (r = x)] and [G(x,x,r)] turns [r = x] into
    [All r (x = x)]; existential monotonicity and rho6 then give [x = x]. The helper is
    [G(a,b,a)] with reflexivity. Specialization of [All_(wel a b) (a = b)] goes through
    [Ex r] (rho1), the helper ([Ex r All r]) and rho6, which yields rho7 from G. Only G, rho1,
    rho2, rho6, MP, GEN and propositional logic are used. *)
From Stdlib Require Import Arith Lia List.
From K230L Require Import Codes230.
From K215F Require Import Codes222 Thm222 CD222 Prop222.
Import ListNotations.
Unset Implicit Arguments.

Lemma contra2 a b : thm222 (wim a b) -> thm222 (wim (wim b 1) (wim a 1)).
Proof.
  intro H. apply der_thm. do 2 apply ded.
  apply (dmp _ b); [hyp|]. apply (dmp _ a); [apply dthm, H|hyp].
Qed.

Lemma contra_thm a b : thm222 (wim (wim a b) (wim (wim b 1) (wim a 1))).
Proof.
  apply der_thm. do 3 apply ded.
  apply (dmp _ b); [hyp|]. apply (dmp _ a); hyp.
Qed.

(** [All r (A -> B) -> (Ex r A -> Ex r B)] *)
Lemma all_ex r a b : thm222 (wim (wal r (wim a b)) (wim (wex r a) (wex r b))).
Proof.
  pose proof (W_mp _ _ (W_gen r _ (contra_thm a b)) (W_r2 r (wim a b) (wim (wim b 1) (wim a 1)))) as H1.
  unfold wex, wn, F. apply der_thm, ded.
  apply (dmp _ (wim (wal r (wim b 1)) (wal r (wim a 1)))).
  - apply dthm, contra_thm.
  - apply (dmp _ (wal r (wim (wim b 1) (wim a 1)))); [apply dthm, W_r2|].
    apply (dmp _ (wal r (wim a b))); [apply dthm, H1|hyp].
Qed.

Lemma ex_mono r a b : thm222 (wim a b) -> thm222 (wim (wex r a) (wex r b)).
Proof. intro H. exact (W_mp _ _ (W_gen r _ H) (all_ex r a b)). Qed.

Theorem refl222 x : thm222 (weq x x).
Proof.
  set (z := wel x x).
  assert (H1 : thm222 (wim (weq z x) (wal z (weq x x)))).
  { apply der_thm, ded. apply (dmp _ (weq z x)); [|hyp].
    apply (dmp _ (weq z x)); [apply dthm, W_rG|hyp]. }
  pose proof (W_mp _ _ (W_r1 z x) (ex_mono z _ _ H1)) as H2.
  exact (W_mp _ _ H2 (W_r6 z (weq x x))).
Qed.

Theorem helper222 a b : thm222 (wim (weq a b) (wal (wel a b) (weq a b))).
Proof. exact (W_mp _ _ (refl222 a) (W_rG a b a)). Qed.

Lemma spec_eq a b : thm222 (wim (wal (wel a b) (weq a b)) (weq a b)).
Proof.
  set (r := wel a b). set (p := weq a b).
  assert (K1 : thm222 (wim (wal r p) (wal r (wim (weq r a) p)))).
  { exact (W_mp _ _ (W_gen r _ (thm_K p (weq r a))) (W_r2 r p (wim (weq r a) p))). }
  apply der_thm, ded.
  apply (dmp _ (wex r (wal r p))); [apply dthm, W_r6|].
  apply (dmp _ (wex r p)); [apply dthm, ex_mono, helper222|].
  apply (dmp _ (wex r (weq r a))); [|apply dthm, W_r1].
  apply (dmp _ (wal r (wim (weq r a) p))); [apply dthm, all_ex|].
  apply (dmp _ (wal r p)); [apply dthm, K1|hyp].
Qed.

Theorem rho7_222 a b c : thm222 (rho7 a b c).
Proof.
  unfold rho7. apply der_thm. do 2 apply ded.
  apply (dmp _ (wal (wel a b) (weq a b))); [apply dthm, spec_eq|].
  apply (dmp _ (weq c b)); [|hyp]. apply (dmp _ (weq c a)); [apply dthm, W_rG|hyp].
Qed.

Print Assumptions rho7_222.
