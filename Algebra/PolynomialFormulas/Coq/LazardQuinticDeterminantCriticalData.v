From mathcomp Require Import all_ssreflect all_algebra all_field.
From PolynomialFormulas Require Import
  LazardQuinticRootProjections
  LazardQuinticDeterminantCertificateMatrix
  LazardCubicQuadraticElimination
  LazardQuinticCriticalElimination.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Polynomial-in-[s] data for the final Figure-3 determinant certificate.
    The split is exactly the one used by the Lean certificate: the critical
    cubic coefficients have degrees [2,1,0,0], the critical remainder
    coefficients have degrees [4,2,2], and the compact determinant numerator
    has degree six with zero degree-five coefficient. *)
Module PolynomialFormulasLazardQuinticDeterminantCriticalData.

Import GRing.Theory.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module DM := PolynomialFormulasLazardQuinticDeterminantCertificateMatrix.
Module CE := PolynomialFormulasLazardQuinticCriticalElimination.
Module CQ := PolynomialFormulasLazardCubicQuadraticElimination.
Local Open Scope ring_scope.

Section CertificateData.

Variable F : fieldType.

Definition lazard_detcritical_A00
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  (3%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_r c -
    RP.lazard_root_p c ^+ 3 * RP.lazard_root_q c ^+ 2 +
    8%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c ^+ 2 +
    RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 * RP.lazard_root_r c -
    2%:R * RP.lazard_root_q c ^+ 4 -
    80%:R * RP.lazard_root_r c ^+ 3) / 2%:R.

Definition lazard_detcritical_A01
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  5%:R * RP.lazard_root_q c *
    (RP.lazard_root_p c ^+ 2 + 10%:R * RP.lazard_root_r c).

Definition lazard_detcritical_A02
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  125%:R * RP.lazard_root_p c / 2%:R.

Definition lazard_detcritical_A10
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  - RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c -
    RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 -
    60%:R * RP.lazard_root_r c ^+ 2.

Definition lazard_detcritical_A11
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  25%:R * RP.lazard_root_q c.

Definition lazard_detcritical_A20
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  - 3%:R *
    (RP.lazard_root_p c ^+ 2 + 20%:R * RP.lazard_root_r c) / 2%:R.

Definition lazard_detcritical_A30
    (_c : RP.LazardDepressedRootCoefficients F) : F := - 5%:R.

Definition lazard_detcritical_B00
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  (81%:R * RP.lazard_root_p c ^+ 8 * RP.lazard_root_r c -
    27%:R * RP.lazard_root_p c ^+ 7 * RP.lazard_root_q c ^+ 2 -
    2124%:R * RP.lazard_root_p c ^+ 6 * RP.lazard_root_r c ^+ 2 +
    1827%:R * RP.lazard_root_p c ^+ 5 * RP.lazard_root_q c ^+ 2 *
      RP.lazard_root_r c -
    394%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_q c ^+ 4 +
    17200%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_r c ^+ 3 -
    26760%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_q c ^+ 2 *
      RP.lazard_root_r c ^+ 2 +
    11400%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c ^+ 4 *
      RP.lazard_root_r c -
    40000%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c ^+ 4 -
    1680%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 6 +
    14000%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 *
      RP.lazard_root_r c ^+ 3 -
    4900%:R * RP.lazard_root_q c ^+ 4 * RP.lazard_root_r c ^+ 2) /
    500%:R.

Definition lazard_detcritical_B01
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  RP.lazard_root_q c *
    (27%:R * RP.lazard_root_p c ^+ 6 +
      2790%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_r c -
      360%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_q c ^+ 2 +
      1600%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c ^+ 2 +
      7800%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 *
        RP.lazard_root_r c -
      1200%:R * RP.lazard_root_q c ^+ 4 -
      20000%:R * RP.lazard_root_r c ^+ 3) / 50%:R.

Definition lazard_detcritical_B02
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  - 5%:R *
    (81%:R * RP.lazard_root_p c ^+ 5 -
      264%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_r c +
      328%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c ^+ 2 -
      240%:R * RP.lazard_root_p c * RP.lazard_root_r c ^+ 2 -
      840%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_r c) / 4%:R.

Definition lazard_detcritical_B03
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  - 1500%:R * RP.lazard_root_p c * RP.lazard_root_q c.

Definition lazard_detcritical_B04
    (_c : RP.LazardDepressedRootCoefficients F) : F := - 3125%:R.

Definition lazard_detcritical_B10
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  - (162%:R * RP.lazard_root_p c ^+ 6 * RP.lazard_root_r c -
      18%:R * RP.lazard_root_p c ^+ 5 * RP.lazard_root_q c ^+ 2 -
      3600%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_r c ^+ 2 +
      2705%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_q c ^+ 2 *
        RP.lazard_root_r c -
      250%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c ^+ 4 +
      20000%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c ^+ 3 -
      14500%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 *
        RP.lazard_root_r c ^+ 2 +
      4200%:R * RP.lazard_root_q c ^+ 4 * RP.lazard_root_r c) /
    250%:R.

Definition lazard_detcritical_B11
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  RP.lazard_root_q c *
    (9%:R * RP.lazard_root_p c ^+ 4 +
      1220%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c -
      320%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 -
      4000%:R * RP.lazard_root_r c ^+ 2) / 10%:R.

Definition lazard_detcritical_B12
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  - 5%:R *
    (9%:R * RP.lazard_root_p c ^+ 3 -
      420%:R * RP.lazard_root_p c * RP.lazard_root_r c -
      160%:R * RP.lazard_root_q c ^+ 2) / 2%:R.

Definition lazard_detcritical_B20
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  - (81%:R * RP.lazard_root_p c ^+ 6 -
      1800%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_r c +
      1140%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_q c ^+ 2 +
      10000%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c ^+ 2 -
      11000%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 *
        RP.lazard_root_r c +
      3600%:R * RP.lazard_root_q c ^+ 4) / 500%:R.

Definition lazard_detcritical_B21
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  RP.lazard_root_q c *
    (3%:R * RP.lazard_root_p c ^+ 2 - 100%:R * RP.lazard_root_r c).

Definition lazard_detcritical_B22
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  450%:R * RP.lazard_root_p c.

Definition lazard_detcritical_PA0
    (c : RP.LazardDepressedRootCoefficients F) : {poly F} :=
  (lazard_detcritical_A00 c)%:P +
    (lazard_detcritical_A01 c)%:P * 'X +
    (lazard_detcritical_A02 c)%:P * 'X ^+ 2.

Definition lazard_detcritical_PA1
    (c : RP.LazardDepressedRootCoefficients F) : {poly F} :=
  (lazard_detcritical_A10 c)%:P +
    (lazard_detcritical_A11 c)%:P * 'X.

Definition lazard_detcritical_PA2
    (c : RP.LazardDepressedRootCoefficients F) : {poly F} :=
  (lazard_detcritical_A20 c)%:P.

Definition lazard_detcritical_PA3
    (c : RP.LazardDepressedRootCoefficients F) : {poly F} :=
  (lazard_detcritical_A30 c)%:P.

Definition lazard_detcritical_PB0
    (c : RP.LazardDepressedRootCoefficients F) : {poly F} :=
  (lazard_detcritical_B00 c)%:P +
    (lazard_detcritical_B01 c)%:P * 'X +
    (lazard_detcritical_B02 c)%:P * 'X ^+ 2 +
    (lazard_detcritical_B03 c)%:P * 'X ^+ 3 +
    (lazard_detcritical_B04 c)%:P * 'X ^+ 4.

Definition lazard_detcritical_PB1
    (c : RP.LazardDepressedRootCoefficients F) : {poly F} :=
  (lazard_detcritical_B10 c)%:P +
    (lazard_detcritical_B11 c)%:P * 'X +
    (lazard_detcritical_B12 c)%:P * 'X ^+ 2.

Definition lazard_detcritical_PB2
    (c : RP.LazardDepressedRootCoefficients F) : {poly F} :=
  (lazard_detcritical_B20 c)%:P +
    (lazard_detcritical_B21 c)%:P * 'X +
    (lazard_detcritical_B22 c)%:P * 'X ^+ 2.

Definition lazard_detcritical_polynomial_value
    (a0 a1 a2 a3 b0 b1 b2 : {poly F}) : {poly F} :=
  a0 ^+ 2 * b2 ^+ 3 - a0 * a1 * b1 * b2 ^+ 2 -
    2%:R *: (a0 * a2 * b0 * b2 ^+ 2) +
    a0 * a2 * b1 ^+ 2 * b2 +
    3%:R *: (a0 * a3 * b0 * b1 * b2) - a0 * a3 * b1 ^+ 3 +
    a1 ^+ 2 * b0 * b2 ^+ 2 - a1 * a2 * b0 * b1 * b2 -
    2%:R *: (a1 * a3 * b0 ^+ 2 * b2) +
    a1 * a3 * b0 * b1 ^+ 2 + a2 ^+ 2 * b0 ^+ 2 * b2 -
    a2 * a3 * b0 ^+ 2 * b1 + a3 ^+ 2 * b0 ^+ 3.

Definition lazard_detcritical_V_polynomial
    (c : RP.LazardDepressedRootCoefficients F) : {poly F} :=
  lazard_detcritical_polynomial_value
    (lazard_detcritical_PA0 c) (lazard_detcritical_PA1 c)
    (lazard_detcritical_PA2 c) (lazard_detcritical_PA3 c)
    (lazard_detcritical_PB0 c) (lazard_detcritical_PB1 c)
    (lazard_detcritical_PB2 c).

Definition lazard_detcritical_N_polynomial
    (c : RP.LazardDepressedRootCoefficients F) : {poly F} :=
  (DM.lazard_det_certificate_N0 c)%:P +
    (DM.lazard_det_certificate_N1 c)%:P * 'X +
    (DM.lazard_det_certificate_N2 c)%:P * 'X ^+ 2 +
    (DM.lazard_det_certificate_N3 c)%:P * 'X ^+ 3 +
    (DM.lazard_det_certificate_N4 c)%:P * 'X ^+ 4 +
    (DM.lazard_det_certificate_N6 c)%:P * 'X ^+ 6.

Definition lazard_detcritical_target_polynomial
    (c : RP.LazardDepressedRootCoefficients F) : {poly F} :=
  - ((1%:R / 125%:R) *:
      (lazard_detcritical_N_polynomial c ^+ 2)).

End CertificateData.

End PolynomialFormulasLazardQuinticDeterminantCriticalData.
