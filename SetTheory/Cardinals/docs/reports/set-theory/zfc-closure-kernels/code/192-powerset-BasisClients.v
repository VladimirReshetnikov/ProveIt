(** Verbatim propositional client segment from production Prop222.v:
    identity, the derivability datatype, deduction, discharge and weakening.
    Only the import prelude is reduced to its actual dependencies. *)
From Coq Require Import List.
From K230L Require Import Codes230.
From K215F Require Import Thm222 CD222.
Import ListNotations.

Lemma thm_I p : thm222 (wim p p).
Proof.
  exact (W_mp _ _ (thm_K p p) (W_mp _ _ (thm_K p (wim p p)) (thm_S p (wim p p) p))).
Qed.

(** ** Hilbert derivations with hypotheses, deduction theorem *)
Inductive der222 (G : list nat) : nat -> Prop :=
  | dhyp n : In n G -> der222 G n
  | dthm n : thm222 n -> der222 G n
  | dmp a b : der222 G (wim a b) -> der222 G a -> der222 G b.

Lemma ded G h a : der222 (h :: G) a -> der222 G (wim h a).
Proof.
  induction 1 as [n [<-|Hn] | n Hn | a b _ IH1 _ IH2].
  - apply dthm. apply thm_I.
  - apply (dmp _ n); [apply dthm, thm_K | now apply dhyp].
  - apply (dmp _ n); [apply dthm, thm_K | now apply dthm].
  - apply (dmp _ (wim h a)); [|exact IH2].
    apply (dmp _ (wim h (wim a b))); [apply dthm, thm_S | exact IH1].
Qed.

Lemma der_thm a : der222 [] a -> thm222 a.
Proof.
  induction 1 as [n [] | n Hn | a b _ IH1 _ IH2]; [exact Hn | exact (W_mp _ _ IH2 IH1)].
Qed.

Lemma der_weak G G' a : der222 G a -> incl G G' -> der222 G' a.
Proof.
  intros Hd Hi. induction Hd as [n Hn | n Hn | x y _ IH1 _ IH2];
    [apply dhyp; auto | now apply dthm | eapply dmp; eauto].
Qed.

Print Assumptions thm_I.
Print Assumptions ded.
Print Assumptions der_thm.
Print Assumptions der_weak.
