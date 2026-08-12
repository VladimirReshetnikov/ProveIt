From mathcomp Require Import all_ssreflect all_algebra.
From PolynomialFormulas Require Import
  LazardQuinticRootProjections LazardQuinticQuadratic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Lazard's coefficient formulas for the three Fourier components remaining
    after P1 has been chosen.  P22 contains Reshetnikov's corrections of the
    two misprinted terms: [8 p^3 q] and [70 q^3]. *)
Module PolynomialFormulasLazardQuinticFourierNumerators.

Import GRing.Theory.
Local Open Scope ring_scope.

Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module Q := PolynomialFormulasLazardQuinticQuadratic.

Section FourierNumerators.

Variable F : fieldType.

Definition lazard_invariant_E
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  (3%:R * RP.lazard_root_p c ^+ 2 + 20%:R * RP.lazard_root_r c) *
      RP.lazard_root_i6 i +
    (- RP.lazard_root_p c * RP.lazard_root_q c -
      50%:R * RP.lazard_root_s c) * RP.lazard_root_i5 i +
    (3%:R * RP.lazard_root_p c ^+ 3 +
      12%:R * RP.lazard_root_p c * RP.lazard_root_r c +
      3%:R * RP.lazard_root_q c ^+ 2) * RP.lazard_root_i4 i +
    4%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_r c -
    3%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c ^+ 2 +
    40%:R * RP.lazard_root_p c * RP.lazard_root_q c *
      RP.lazard_root_s c +
    16%:R * RP.lazard_root_p c * RP.lazard_root_r c ^+ 2 -
    21%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_r c +
    125%:R * RP.lazard_root_s c ^+ 2.

Definition lazard_p41
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  - 5%:R * RP.lazard_root_p c.

Definition lazard_p42
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  5%:R *
    (10%:R * RP.lazard_root_i7 i -
      4%:R * RP.lazard_root_p c * RP.lazard_root_i5 i -
      14%:R * RP.lazard_root_q c * RP.lazard_root_i4 i -
      4%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c +
      45%:R * RP.lazard_root_p c * RP.lazard_root_s c -
      72%:R * RP.lazard_root_q c * RP.lazard_root_r c).

Definition lazard_p31
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  - 25%:R * RP.lazard_root_q c.

Definition lazard_p32
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  25%:R *
    (- 10%:R * RP.lazard_root_i8 i +
      2%:R * RP.lazard_root_p c * RP.lazard_root_i6 i -
      22%:R * RP.lazard_root_q c * RP.lazard_root_i5 i +
      2%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_i4 i +
      20%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c +
      2%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 -
      35%:R * RP.lazard_root_q c * RP.lazard_root_s c -
      40%:R * RP.lazard_root_r c ^+ 2).

Definition lazard_p33
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  5%:R *
    (35%:R * RP.lazard_root_i8 i -
      4%:R * RP.lazard_root_p c * RP.lazard_root_i6 i +
      23%:R * RP.lazard_root_q c * RP.lazard_root_i5 i +
      (- 6%:R * RP.lazard_root_p c ^+ 2 +
        12%:R * RP.lazard_root_r c) * RP.lazard_root_i4 i -
      58%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c +
      14%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 -
      105%:R * RP.lazard_root_q c * RP.lazard_root_s c +
      76%:R * RP.lazard_root_r c ^+ 2).

Definition lazard_p34
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  5%:R *
    (5%:R * RP.lazard_root_i8 i -
      22%:R * RP.lazard_root_p c * RP.lazard_root_i6 i +
      14%:R * RP.lazard_root_q c * RP.lazard_root_i5 i +
      (- 18%:R * RP.lazard_root_p c ^+ 2 +
        16%:R * RP.lazard_root_r c) * RP.lazard_root_i4 i -
      34%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c +
      22%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 -
      140%:R * RP.lazard_root_q c * RP.lazard_root_s c +
      68%:R * RP.lazard_root_r c ^+ 2).

Definition lazard_p21
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  5%:R *
    (3%:R * RP.lazard_root_i4 i +
      2%:R * RP.lazard_root_p c ^+ 2 -
      16%:R * RP.lazard_root_r c).

(** Corrected P22.  The printed terms [8 p^3] and [70 q^3 q] are
    respectively [8 p^3 q] and [70 q^3]. *)
Definition lazard_p22
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  25%:R *
    (- 10%:R * RP.lazard_root_q c * RP.lazard_root_i6 i +
      (8%:R * RP.lazard_root_p c ^+ 2 -
        50%:R * RP.lazard_root_r c) * RP.lazard_root_i5 i +
      (- 2%:R * RP.lazard_root_p c * RP.lazard_root_q c -
        25%:R * RP.lazard_root_s c) * RP.lazard_root_i4 i +
      8%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_q c +
      70%:R * RP.lazard_root_q c ^+ 3 -
      20%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_s c -
      26%:R * RP.lazard_root_p c * RP.lazard_root_q c *
        RP.lazard_root_r c +
      50%:R * RP.lazard_root_r c * RP.lazard_root_s c).

Definition lazard_p23
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  25%:R *
    (- 4%:R * RP.lazard_root_p c * RP.lazard_root_i7 i -
      RP.lazard_root_q c * RP.lazard_root_i6 i +
      4%:R * RP.lazard_root_r c * RP.lazard_root_i5 i +
      (- 3%:R * RP.lazard_root_p c * RP.lazard_root_q c +
        15%:R * RP.lazard_root_s c) * RP.lazard_root_i4 i +
      26%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_s c -
      26%:R * RP.lazard_root_p c * RP.lazard_root_q c *
        RP.lazard_root_r c +
      7%:R * RP.lazard_root_q c ^+ 3 -
      40%:R * RP.lazard_root_r c * RP.lazard_root_s c).

Definition lazard_p24
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  25%:R *
    (3%:R * RP.lazard_root_p c * RP.lazard_root_i7 i -
      18%:R * RP.lazard_root_q c * RP.lazard_root_i6 i +
      22%:R * RP.lazard_root_r c * RP.lazard_root_i5 i +
      (- 14%:R * RP.lazard_root_p c * RP.lazard_root_q c +
        20%:R * RP.lazard_root_s c) * RP.lazard_root_i4 i +
      18%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_s c -
      33%:R * RP.lazard_root_p c * RP.lazard_root_q c *
        RP.lazard_root_r c +
      21%:R * RP.lazard_root_q c ^+ 3 +
      30%:R * RP.lazard_root_r c * RP.lazard_root_s c).

Definition lazard_fourier_P4_formula
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F)
    (v : Q.lazard_quadratic_triple F) (p1 : F) : F :=
  lazard_p41 c / (2%:R * p1) +
    lazard_p42 c i / (2%:R * Q.lazard_epsilon v * p1).

Definition lazard_fourier_P3_formula
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F)
    (v : Q.lazard_quadratic_triple F) (p1 : F) : F :=
  lazard_p31 c / (4%:R * p1 ^+ 2) +
    lazard_p32 c i / (4%:R * Q.lazard_epsilon v * p1 ^+ 2) +
    (lazard_p33 c i * Q.lazard_t v +
      lazard_p34 c i * Q.lazard_u v) /
      (10%:R * lazard_invariant_E c i * p1 ^+ 2).

Definition lazard_fourier_P2_formula
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F)
    (v : Q.lazard_quadratic_triple F) (p1 : F) : F :=
  lazard_p21 c i / (4%:R * p1 ^+ 3) +
    lazard_p22 c i / (4%:R * Q.lazard_epsilon v * p1 ^+ 3) +
    (lazard_p23 c i * Q.lazard_t v +
      lazard_p24 c i * Q.lazard_u v) /
      (10%:R * lazard_invariant_E c i * p1 ^+ 3).

End FourierNumerators.

End PolynomialFormulasLazardQuinticFourierNumerators.
