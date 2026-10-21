(** * ThmDom: the dominated calculus of the 217 (Source 149).

    [thm222] with rho8 restricted to the instances whose fourth argument is at most its first:
    the only rho8 instances the 217's AX command emits.  It derives exactly [thm222]'s codes:
    a restricted row is a row, and every row follows from the restricted ones ([rho8_all],
    Source 149's certificate). *)
From Coq Require Import Arith Lia.
From K230L Require Import Codes230.
From K215F Require Import Codes222 Thm222 DomRho8.

Inductive thmDom : nat -> Prop :=
  | D_true : thmDom 0
  | D_mp t b : thmDom t -> thmDom (wim t b) -> thmDom b
  | D_gen a h : thmDom h -> thmDom (wal a h)
  | D_r1 a b : thmDom (rho1 a b)
  | D_r2 a b c : thmDom (rho2 a b c)
  | D_r3 a b c : thmDom (rho3 a b c)
  | D_r4 a b c : thmDom (rho4 a b c)
  | D_r5 a b c : thmDom (rho5 a b c)
  | D_r6 a b : thmDom (rho6 a b)
  | D_rG a b c : thmDom (growG a b c)
  | D_r8 a b c u : u <= a -> thmDom (rho8 a b c u)
  | D_bundle a b c : c <> a -> c <> b -> thmDom (bundle222 a b c).

Lemma thm222_of_thmDom n : thmDom n -> thm222 n.
Proof.
  induction 1.
  - exact W_true.
  - now apply (W_mp t).
  - now apply W_gen.
  - apply W_r1.
  - apply W_r2.
  - apply W_r3.
  - apply W_r4.
  - apply W_r5.
  - apply W_r6.
  - apply W_rG.
  - apply W_r8.
  - now apply W_bundle.
Qed.

Lemma domImp : DomImp thmDom.
Proof.
  constructor.
  - exact D_true.
  - intros a b H1 H2. exact (D_mp a b H2 H1).
  - exact D_r8.
Qed.

Lemma thmDom_of_thm222 n : thm222 n -> thmDom n.
Proof.
  induction 1.
  - exact D_true.
  - now apply (D_mp t).
  - now apply D_gen.
  - apply D_r1.
  - apply D_r2.
  - apply D_r3.
  - apply D_r4.
  - apply D_r5.
  - apply D_r6.
  - apply D_rG.
  - apply (rho8_all thmDom domImp).
  - now apply D_bundle.
Qed.

Theorem thmDom_iff n : thmDom n <-> thm222 n.
Proof. split; [apply thm222_of_thmDom | apply thmDom_of_thm222]. Qed.

Print Assumptions thmDom_iff.
