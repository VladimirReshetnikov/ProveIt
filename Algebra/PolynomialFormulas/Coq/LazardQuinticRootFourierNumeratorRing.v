From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Shared reflective-ring support for the root-specialized P2 and P3
    numerator certificates.  The carrier bridge is public, but every
    certificate file registers the theory locally: [Add Ring] registrations
    do not survive compiled-module boundaries. *)
Module PolynomialFormulasLazardQuinticRootFourierNumeratorRing.

Import GRing.Theory.
Local Open Scope ring_scope.

Section RootFourierNumeratorRing.

Variable F : fieldType.

Definition lazard_numerator_ring_carrier : Type := F.
Definition lazard_numerator_ring_zero : lazard_numerator_ring_carrier :=
  @GRing.zero F.
Definition lazard_numerator_ring_one : lazard_numerator_ring_carrier :=
  @GRing.one F.
Definition lazard_numerator_ring_add :
    lazard_numerator_ring_carrier -> lazard_numerator_ring_carrier ->
      lazard_numerator_ring_carrier := @GRing.add F.
Definition lazard_numerator_ring_mul :
    lazard_numerator_ring_carrier -> lazard_numerator_ring_carrier ->
      lazard_numerator_ring_carrier := @GRing.mul F.
Definition lazard_numerator_ring_sub :
    lazard_numerator_ring_carrier -> lazard_numerator_ring_carrier ->
      lazard_numerator_ring_carrier := fun x y => x - y.
Definition lazard_numerator_ring_opp :
    lazard_numerator_ring_carrier -> lazard_numerator_ring_carrier :=
  @GRing.opp F.
Definition lazard_numerator_ring_eq :
    lazard_numerator_ring_carrier -> lazard_numerator_ring_carrier -> Prop :=
  @eq lazard_numerator_ring_carrier.

Lemma lazard_numerator_ring_addE (x y : F) :
  x + y = lazard_numerator_ring_add x y. Proof. reflexivity. Qed.
Lemma lazard_numerator_ring_mulE (x y : F) :
  x * y = lazard_numerator_ring_mul x y. Proof. reflexivity. Qed.
Lemma lazard_numerator_ring_subE (x y : F) :
  x - y = lazard_numerator_ring_sub x y. Proof. reflexivity. Qed.
Lemma lazard_numerator_ring_oppE (x : F) :
  - x = lazard_numerator_ring_opp x. Proof. reflexivity. Qed.
Lemma lazard_numerator_ring_zeroE :
  (0 : F) = lazard_numerator_ring_zero. Proof. reflexivity. Qed.
Lemma lazard_numerator_ring_oneE :
  (1 : F) = lazard_numerator_ring_one. Proof. reflexivity. Qed.

Lemma lazard_numerator_ring_theory :
  @ring_theory lazard_numerator_ring_carrier lazard_numerator_ring_zero
    lazard_numerator_ring_one lazard_numerator_ring_add
    lazard_numerator_ring_mul lazard_numerator_ring_sub
    lazard_numerator_ring_opp lazard_numerator_ring_eq.
Proof.
constructor; unfold lazard_numerator_ring_carrier,
  lazard_numerator_ring_zero, lazard_numerator_ring_one,
  lazard_numerator_ring_add, lazard_numerator_ring_mul,
  lazard_numerator_ring_sub, lazard_numerator_ring_opp,
  lazard_numerator_ring_eq; intros.
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

(** Numeral decompositions used by the displayed Lazard coefficients.  They
    keep the reflective tactic's coefficient language down to [0], [1],
    addition, and multiplication. *)
Lemma lazard_numerator_two_natrE : (2%:R : F) = 1 + 1.
Proof. exact: (@natrD F 1 1). Qed.
Lemma lazard_numerator_three_natrE : (3%:R : F) = 2%:R + 1.
Proof. exact: (@natrD F 2 1). Qed.
Lemma lazard_numerator_four_natrE : (4%:R : F) = 2%:R * 2%:R.
Proof. exact: (@natrM F 2 2). Qed.
Lemma lazard_numerator_five_natrE : (5%:R : F) = 4%:R + 1.
Proof. exact: (@natrD F 4 1). Qed.
Lemma lazard_numerator_six_natrE : (6%:R : F) = 3%:R * 2%:R.
Proof. exact: (@natrM F 3 2). Qed.
Lemma lazard_numerator_seven_natrE : (7%:R : F) = 6%:R + 1.
Proof. exact: (@natrD F 6 1). Qed.
Lemma lazard_numerator_eight_natrE : (8%:R : F) = 4%:R * 2%:R.
Proof. exact: (@natrM F 4 2). Qed.
Lemma lazard_numerator_ten_natrE : (10%:R : F) = 5%:R * 2%:R.
Proof. exact: (@natrM F 5 2). Qed.
Lemma lazard_numerator_eleven_natrE : (11%:R : F) = 10%:R + 1.
Proof. exact: (@natrD F 10 1). Qed.
Lemma lazard_numerator_twelve_natrE : (12%:R : F) = 6%:R * 2%:R.
Proof. exact: (@natrM F 6 2). Qed.
Lemma lazard_numerator_fourteen_natrE : (14%:R : F) = 7%:R * 2%:R.
Proof. exact: (@natrM F 7 2). Qed.
Lemma lazard_numerator_fifteen_natrE : (15%:R : F) = 3%:R * 5%:R.
Proof. exact: (@natrM F 3 5). Qed.
Lemma lazard_numerator_sixteen_natrE : (16%:R : F) = 8%:R * 2%:R.
Proof. exact: (@natrM F 8 2). Qed.
Lemma lazard_numerator_seventeen_natrE : (17%:R : F) = 16%:R + 1.
Proof. exact: (@natrD F 16 1). Qed.
Lemma lazard_numerator_eighteen_natrE : (18%:R : F) = 3%:R * 6%:R.
Proof. exact: (@natrM F 3 6). Qed.
Lemma lazard_numerator_twenty_natrE : (20%:R : F) = 10%:R * 2%:R.
Proof. exact: (@natrM F 10 2). Qed.
Lemma lazard_numerator_twenty_one_natrE : (21%:R : F) = 3%:R * 7%:R.
Proof. exact: (@natrM F 3 7). Qed.
Lemma lazard_numerator_twenty_two_natrE : (22%:R : F) = 2%:R * 11%:R.
Proof. exact: (@natrM F 2 11). Qed.
Lemma lazard_numerator_twenty_three_natrE : (23%:R : F) = 22%:R + 1.
Proof. exact: (@natrD F 22 1). Qed.
Lemma lazard_numerator_twenty_five_natrE : (25%:R : F) = 5%:R * 5%:R.
Proof. exact: (@natrM F 5 5). Qed.
Lemma lazard_numerator_twenty_six_natrE : (26%:R : F) = 20%:R + 6%:R.
Proof. exact: (@natrD F 20 6). Qed.
Lemma lazard_numerator_twenty_eight_natrE : (28%:R : F) = 4%:R * 7%:R.
Proof. exact: (@natrM F 4 7). Qed.
Lemma lazard_numerator_thirty_natrE : (30%:R : F) = 3%:R * 10%:R.
Proof. exact: (@natrM F 3 10). Qed.
Lemma lazard_numerator_thirty_three_natrE : (33%:R : F) = 3%:R * 11%:R.
Proof. exact: (@natrM F 3 11). Qed.
Lemma lazard_numerator_thirty_four_natrE : (34%:R : F) = 2%:R * 17%:R.
Proof. exact: (@natrM F 2 17). Qed.
Lemma lazard_numerator_thirty_five_natrE : (35%:R : F) = 5%:R * 7%:R.
Proof. exact: (@natrM F 5 7). Qed.
Lemma lazard_numerator_forty_natrE : (40%:R : F) = 4%:R * 10%:R.
Proof. exact: (@natrM F 4 10). Qed.
Lemma lazard_numerator_fifty_natrE : (50%:R : F) = 5%:R * 10%:R.
Proof. exact: (@natrM F 5 10). Qed.
Lemma lazard_numerator_fifty_eight_natrE : (58%:R : F) = 50%:R + 8%:R.
Proof. exact: (@natrD F 50 8). Qed.
Lemma lazard_numerator_sixty_eight_natrE : (68%:R : F) = 4%:R * 17%:R.
Proof. exact: (@natrM F 4 17). Qed.
Lemma lazard_numerator_seventy_natrE : (70%:R : F) = 7%:R * 10%:R.
Proof. exact: (@natrM F 7 10). Qed.
Lemma lazard_numerator_seventy_six_natrE : (76%:R : F) = 70%:R + 6%:R.
Proof. exact: (@natrD F 70 6). Qed.
Lemma lazard_numerator_hundred_natrE : (100%:R : F) = 10%:R * 10%:R.
Proof. exact: (@natrM F 10 10). Qed.
Lemma lazard_numerator_hundred_five_natrE : (105%:R : F) = 100%:R + 5%:R.
Proof. exact: (@natrD F 100 5). Qed.
Lemma lazard_numerator_hundred_twenty_five_natrE :
  (125%:R : F) = 5%:R * 25%:R.
Proof. exact: (@natrM F 5 25). Qed.
Lemma lazard_numerator_hundred_forty_natrE : (140%:R : F) = 2%:R * 70%:R.
Proof. exact: (@natrM F 2 70). Qed.

Lemma lazard_numerator_expr1 (x : F) : x ^+ 1 = x.
Proof. by rewrite expr1. Qed.
Lemma lazard_numerator_expr2 (x : F) : x ^+ 2 = x * x.
Proof. by rewrite expr2. Qed.
Lemma lazard_numerator_expr3 (x : F) : x ^+ 3 = x * x * x.
Proof. by rewrite exprSr expr2. Qed.
Lemma lazard_numerator_expr4 (x : F) : x ^+ 4 = x * x * x * x.
Proof. by rewrite exprSr lazard_numerator_expr3. Qed.
Lemma lazard_numerator_expr5 (x : F) : x ^+ 5 = x * x * x * x * x.
Proof. by rewrite exprSr lazard_numerator_expr4. Qed.

End RootFourierNumeratorRing.

End PolynomialFormulasLazardQuinticRootFourierNumeratorRing.

(** Syntactic preparation shared by the isolated certificate modules.  The
    final [change] and [ring] remain local because every client chooses its
    own registered theory name. *)
Ltac lazard_numerator_prepare :=
  repeat first
    [ rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_hundred_forty_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_hundred_twenty_five_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_hundred_five_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_hundred_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_seventy_six_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_seventy_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_sixty_eight_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_fifty_eight_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_fifty_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_forty_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_thirty_five_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_thirty_four_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_thirty_three_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_thirty_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_twenty_eight_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_twenty_six_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_twenty_five_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_twenty_three_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_twenty_two_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_twenty_one_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_twenty_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_eighteen_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_seventeen_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_sixteen_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_fifteen_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_fourteen_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_twelve_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_eleven_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_ten_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_eight_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_seven_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_six_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_five_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_four_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_three_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_two_natrE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_expr5
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_expr4
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_expr3
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_expr2
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_expr1
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_ring_addE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_ring_mulE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_ring_subE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_ring_oppE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_ring_zeroE
    | rewrite PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_ring_oneE ].
