(** The existing four-name CD222 interface, from the shared six-goal core.
    This replaces the independent 107-certificate proof. The named cd_0..cd_106
    intermediate certificates are implementation details, absent from clients. *)
From K230L Require Import Codes230.
From K215F Require Import Thm222 DominatedImplication.

(** Unrestricted logic needs no arithmetic domination relation. *)
Local Definition language : DominatedImplication.Language nat := {|
  DominatedImplication.imp := wim;
  DominatedImplication.below := fun _ _ => True;
  DominatedImplication.refl := fun _ => I;
  DominatedImplication.grow_left := fun _ _ _ _ => I;
  DominatedImplication.grow_right := fun _ _ _ _ => I
|}.

Local Definition calculus : DominatedImplication.Restricted language thm222.
Proof.
  constructor.
  - intros a b hab ha. exact (W_mp a b ha hab).
  - intros a b c u _. exact (W_r8 a b c u).
Defined.

Lemma thm_K (p q : nat) : thm222 (wim p (wim q p)).
Proof. exact (DominatedImplication.basisK language thm222 calculus p q). Qed.

Lemma thm_P (p q : nat) : thm222 (wim (wim (wim p q) p) p).
Proof. exact (DominatedImplication.basisPeirce language thm222 calculus p q). Qed.

Lemma thm_B (p q r : nat) : thm222 (wim (wim p q) (wim (wim q r) (wim p r))).
Proof. exact (DominatedImplication.composition language thm222 calculus p q r). Qed.

Lemma thm_S (p q r : nat) : thm222 (wim (wim p (wim q r)) (wim (wim p q) (wim p r))).
Proof. exact (DominatedImplication.basisS language thm222 calculus p q r). Qed.

Print Assumptions thm_K.
Print Assumptions thm_P.
Print Assumptions thm_B.
Print Assumptions thm_S.
