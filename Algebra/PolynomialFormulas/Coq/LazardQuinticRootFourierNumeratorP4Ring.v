From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Shared reflective-ring support for the four small P4 root-polynomial
    certificates.  Each certificate module registers this theory locally,
    because tactic registrations do not cross compiled-module boundaries. *)
Module PolynomialFormulasLazardQuinticRootFourierNumeratorP4Ring.

Import GRing.Theory.
Local Open Scope ring_scope.

Section RootFourierNumeratorP4Ring.

Variable F : fieldType.

Definition lazard_p4_ring_carrier : Type := F.
Definition lazard_p4_ring_zero : lazard_p4_ring_carrier := @GRing.zero F.
Definition lazard_p4_ring_one : lazard_p4_ring_carrier := @GRing.one F.
Definition lazard_p4_ring_add :
    lazard_p4_ring_carrier -> lazard_p4_ring_carrier ->
      lazard_p4_ring_carrier :=
  @GRing.add F.
Definition lazard_p4_ring_mul :
    lazard_p4_ring_carrier -> lazard_p4_ring_carrier ->
      lazard_p4_ring_carrier :=
  @GRing.mul F.
Definition lazard_p4_ring_sub :
    lazard_p4_ring_carrier -> lazard_p4_ring_carrier ->
      lazard_p4_ring_carrier :=
  fun x y => x - y.
Definition lazard_p4_ring_opp :
    lazard_p4_ring_carrier -> lazard_p4_ring_carrier :=
  @GRing.opp F.
Definition lazard_p4_ring_eq :
    lazard_p4_ring_carrier -> lazard_p4_ring_carrier -> Prop :=
  @eq lazard_p4_ring_carrier.

Lemma lazard_p4_ring_addE (x y : F) :
  x + y = lazard_p4_ring_add x y. Proof. reflexivity. Qed.
Lemma lazard_p4_ring_mulE (x y : F) :
  x * y = lazard_p4_ring_mul x y. Proof. reflexivity. Qed.
Lemma lazard_p4_ring_subE (x y : F) :
  x - y = lazard_p4_ring_sub x y. Proof. reflexivity. Qed.
Lemma lazard_p4_ring_oppE (x : F) :
  - x = lazard_p4_ring_opp x. Proof. reflexivity. Qed.
Lemma lazard_p4_ring_zeroE :
  (0 : F) = lazard_p4_ring_zero. Proof. reflexivity. Qed.
Lemma lazard_p4_ring_oneE :
  (1 : F) = lazard_p4_ring_one. Proof. reflexivity. Qed.

Lemma lazard_p4_ring_theory :
  @ring_theory lazard_p4_ring_carrier lazard_p4_ring_zero
    lazard_p4_ring_one lazard_p4_ring_add lazard_p4_ring_mul
    lazard_p4_ring_sub lazard_p4_ring_opp lazard_p4_ring_eq.
Proof.
constructor; unfold lazard_p4_ring_carrier, lazard_p4_ring_zero,
  lazard_p4_ring_one, lazard_p4_ring_add, lazard_p4_ring_mul,
  lazard_p4_ring_sub, lazard_p4_ring_opp, lazard_p4_ring_eq; intros.
- exact: add0r.
- exact: addrC.
- exact: addrA.
- exact: mul1r.
- exact: mulrC.
- exact: mulrA.
- exact: mulrDl.
- reflexivity.
- exact: addrN.
Qed.

Lemma lazard_p4_fourteen_natrE :
  (14%:R : F) = 10%:R + 4%:R.
Proof. exact: (@natrD F 10 4). Qed.

Lemma lazard_p4_forty_five_natrE :
  (45%:R : F) = 40%:R + 5%:R.
Proof. exact: (@natrD F 40 5). Qed.

Lemma lazard_p4_seventy_two_natrE :
  (72%:R : F) = 70%:R + 2%:R.
Proof. exact: (@natrD F 70 2). Qed.

End RootFourierNumeratorP4Ring.

End PolynomialFormulasLazardQuinticRootFourierNumeratorP4Ring.
