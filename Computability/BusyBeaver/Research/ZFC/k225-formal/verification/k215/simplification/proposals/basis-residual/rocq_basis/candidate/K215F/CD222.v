(** Shared implication basis for the unrestricted numerical calculus.
    This adapter replaces the separate 107-step CD222 derivation.
    The four public theorem statements are unchanged. *)
From K230L Require Import Codes230.
From K215F Require Import Thm222.
From K215F Require DominatedImplication.

Module Core := DominatedImplication.

(** Every unrestricted axiom meets the vacuous guard. *)
Local Definition language : Core.Language nat := {|
  Core.imp := wim;
  Core.below := fun _ _ => True;
  Core.refl := fun _ => I;
  Core.grow_left := fun _ _ _ _ => I;
  Core.grow_right := fun _ _ _ _ => I
|}.

Local Definition restricted : Core.Restricted language thm222.
Proof.
  constructor.
  - intros a b Hab Ha. exact (W_mp a b Ha Hab).
  - intros a b c u _. exact (W_r8 a b c u).
Defined.

Lemma thm_K (p q : nat) : thm222 (wim p (wim q p)).
Proof. exact (Core.basisK language thm222 restricted p q). Qed.
Lemma thm_P (p q : nat) : thm222 (wim (wim (wim p q) p) p).
Proof. exact (Core.basisPeirce language thm222 restricted p q). Qed.
Lemma thm_B (p q r : nat) : thm222 (wim (wim p q) (wim (wim q r) (wim p r))).
Proof. exact (Core.composition language thm222 restricted p q r). Qed.
Lemma thm_S (p q r : nat) : thm222 (wim (wim p (wim q r)) (wim (wim p q) (wim p r))).
Proof. exact (Core.basisS language thm222 restricted p q r). Qed.
