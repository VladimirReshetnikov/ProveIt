From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Scalar coefficient data for the denominator-cleared fifth Figure-3
    identity.  Isolating the six coefficients makes the large certificate
    linear in the invariant variables and lets each coefficient be checked
    in an independent kernel unit. *)
Module PolynomialFormulasLazardQuinticRootInvariantRelationFifthData.

Import GRing.Theory.
Local Open Scope ring_scope.

Section FifthData.

Variable F : fieldType.

Variables p q r s : F.

(** Coefficients of the already-proved fourth-power relation. *)
Definition lazard_fifth_fourth_i8 : F :=
  19%:R * p ^+ 2 * r - 9%:R * p * q ^+ 2 +
    225%:R * q * s - 60%:R * r ^+ 2.

Definition lazard_fifth_fourth_i7 : F :=
  15%:R * p ^+ 2 * s - 8%:R * p * q * r +
    3%:R * q ^+ 3 + 100%:R * r * s.

Definition lazard_fifth_fourth_i6 : F :=
  - 4%:R * p ^+ 3 * r + 4%:R * p ^+ 2 * q ^+ 2 -
    105%:R * p * q * s - 16%:R * p * r ^+ 2 +
    29%:R * q ^+ 2 * r + 125%:R * s ^+ 2.

Definition lazard_fifth_fourth_i5 : F :=
  - 9%:R * p ^+ 3 * s + 17%:R * p ^+ 2 * q * r -
    8%:R * p * q ^+ 3 + 140%:R * p * r * s +
    155%:R * q ^+ 2 * s - 68%:R * q * r ^+ 2.

Definition lazard_fifth_fourth_i4 : F :=
  - 4%:R * p ^+ 4 * r + 4%:R * p ^+ 3 * q ^+ 2 -
    79%:R * p ^+ 2 * q * s - 16%:R * p ^+ 2 * r ^+ 2 +
    15%:R * p * q ^+ 2 * r - 25%:R * p * s ^+ 2 +
    4%:R * q ^+ 4 + 80%:R * q * r * s.

Definition lazard_fifth_fourth_constant : F :=
  6%:R * p ^+ 4 * q * s - 22%:R * p ^+ 4 * r ^+ 2 +
  16%:R * p ^+ 3 * q ^+ 2 * r - 4%:R * p ^+ 2 * q ^+ 4 -
  404%:R * p ^+ 2 * q * r * s + 68%:R * p ^+ 2 * r ^+ 3 +
  132%:R * p * q ^+ 3 * s + 42%:R * p * q ^+ 2 * r ^+ 2 +
  550%:R * p * r * s ^+ 2 - 30%:R * q ^+ 4 * r -
  50%:R * q ^+ 2 * s ^+ 2 + 20%:R * q * r ^+ 2 * s +
  16%:R * r ^+ 4.

(** Coefficients of the square relation. *)
Definition lazard_fifth_square_i8 : F := 5%:R.
Definition lazard_fifth_square_i7 : F := 0.
Definition lazard_fifth_square_i6 : F := - 2%:R * p.
Definition lazard_fifth_square_i5 : F := 4%:R * q.
Definition lazard_fifth_square_i4 : F := - 2%:R * p ^+ 2.
Definition lazard_fifth_square_constant : F :=
  - 6%:R * p ^+ 2 * r + 2%:R * p * q ^+ 2 +
    10%:R * q * s + 4%:R * r ^+ 2.

(** Coefficients of the four denominator-cleared Figure-2 reductions. *)
Definition lazard_fifth_product_i5_i8 : F := 0.
Definition lazard_fifth_product_i5_i7 : F := - p.
Definition lazard_fifth_product_i5_i6 : F := q.
Definition lazard_fifth_product_i5_i5 : F := - 2%:R * r.
Definition lazard_fifth_product_i5_i4 : F := p * q.
Definition lazard_fifth_product_i5_constant : F :=
  10%:R * r * s - 2%:R * q ^+ 3 +
    5%:R * p * q * r - 6%:R * p ^+ 2 * s.

Definition lazard_fifth_product_i6_i8 : F := - 9%:R * p.
Definition lazard_fifth_product_i6_i7 : F := - q.
Definition lazard_fifth_product_i6_i6 : F :=
  - 4%:R * r + 3%:R * p ^+ 2.
Definition lazard_fifth_product_i6_i5 : F :=
  5%:R * s - 7%:R * p * q.
Definition lazard_fifth_product_i6_i4 : F :=
  q ^+ 2 - 4%:R * p * r + 3%:R * p ^+ 3.
Definition lazard_fifth_product_i6_constant : F :=
  50%:R * s ^+ 2 + 2%:R * q ^+ 2 * r -
  4%:R * p * r ^+ 2 - 27%:R * p * q * s -
  3%:R * p ^+ 2 * q ^+ 2 + 10%:R * p ^+ 3 * r.

Definition lazard_fifth_product_i7_i8 : F := - 3%:R * q.
Definition lazard_fifth_product_i7_i7 : F := - 2%:R * r.
Definition lazard_fifth_product_i7_i6 : F := - 5%:R * s + p * q.
Definition lazard_fifth_product_i7_i5 : F := - 2%:R * q ^+ 2 - p * r.
Definition lazard_fifth_product_i7_i4 : F :=
  - 2%:R * q * r - 4%:R * p * s + p ^+ 2 * q.
Definition lazard_fifth_product_i7_constant : F :=
  - 6%:R * q * r ^+ 2 + 8%:R * q ^+ 2 * s -
  11%:R * p * r * s - p * q ^+ 3 +
  3%:R * p ^+ 2 * q * r + 3%:R * p ^+ 3 * s.

Definition lazard_fifth_product_i8_i8 : F :=
  - 4%:R * r + p ^+ 2.
Definition lazard_fifth_product_i8_i7 : F :=
  - 10%:R * s + p * q.
Definition lazard_fifth_product_i8_i6 : F :=
  - 4%:R * q ^+ 2 + 4%:R * p * r - p ^+ 3.
Definition lazard_fifth_product_i8_i5 : F :=
  2%:R * q * r - 7%:R * p * s + p ^+ 2 * q.
Definition lazard_fifth_product_i8_i4 : F :=
  - 8%:R * r ^+ 2 + 8%:R * q * s -
  5%:R * p * q ^+ 2 + 8%:R * p ^+ 2 * r - p ^+ 4.
Definition lazard_fifth_product_i8_constant : F :=
  - 16%:R * r ^+ 3 + 12%:R * q * r * s + 6%:R * q ^+ 4 -
  30%:R * p * s ^+ 2 - 18%:R * p * q ^+ 2 * r +
  12%:R * p ^+ 2 * r ^+ 2 + 15%:R * p ^+ 2 * q * s +
  p ^+ 3 * q ^+ 2 - 2%:R * p ^+ 4 * r.

(** Coefficients reconstructed from the fourth, square, and product
    relations.  The [i4] coefficient also receives [2 * fourth_constant]
    from [2*i4*fourth_rhs]. *)
Definition lazard_fifth_reconstructed_i8 : F :=
  lazard_fifth_fourth_i8 * lazard_fifth_product_i8_i8 +
  2%:R * lazard_fifth_fourth_i7 * lazard_fifth_product_i7_i8 +
  lazard_fifth_fourth_i6 * lazard_fifth_product_i6_i8 +
  2%:R * lazard_fifth_fourth_i5 * lazard_fifth_product_i5_i8 +
  2%:R * lazard_fifth_fourth_i4 * lazard_fifth_square_i8.

Definition lazard_fifth_reconstructed_i7 : F :=
  lazard_fifth_fourth_i8 * lazard_fifth_product_i8_i7 +
  2%:R * lazard_fifth_fourth_i7 * lazard_fifth_product_i7_i7 +
  lazard_fifth_fourth_i6 * lazard_fifth_product_i6_i7 +
  2%:R * lazard_fifth_fourth_i5 * lazard_fifth_product_i5_i7 +
  2%:R * lazard_fifth_fourth_i4 * lazard_fifth_square_i7.

Definition lazard_fifth_reconstructed_i6 : F :=
  lazard_fifth_fourth_i8 * lazard_fifth_product_i8_i6 +
  2%:R * lazard_fifth_fourth_i7 * lazard_fifth_product_i7_i6 +
  lazard_fifth_fourth_i6 * lazard_fifth_product_i6_i6 +
  2%:R * lazard_fifth_fourth_i5 * lazard_fifth_product_i5_i6 +
  2%:R * lazard_fifth_fourth_i4 * lazard_fifth_square_i6.

Definition lazard_fifth_reconstructed_i5 : F :=
  lazard_fifth_fourth_i8 * lazard_fifth_product_i8_i5 +
  2%:R * lazard_fifth_fourth_i7 * lazard_fifth_product_i7_i5 +
  lazard_fifth_fourth_i6 * lazard_fifth_product_i6_i5 +
  2%:R * lazard_fifth_fourth_i5 * lazard_fifth_product_i5_i5 +
  2%:R * lazard_fifth_fourth_i4 * lazard_fifth_square_i5.

Definition lazard_fifth_reconstructed_i4 : F :=
  2%:R * lazard_fifth_fourth_constant +
  lazard_fifth_fourth_i8 * lazard_fifth_product_i8_i4 +
  2%:R * lazard_fifth_fourth_i7 * lazard_fifth_product_i7_i4 +
  lazard_fifth_fourth_i6 * lazard_fifth_product_i6_i4 +
  2%:R * lazard_fifth_fourth_i5 * lazard_fifth_product_i5_i4 +
  2%:R * lazard_fifth_fourth_i4 * lazard_fifth_square_i4.

Definition lazard_fifth_reconstructed_constant : F :=
  lazard_fifth_fourth_i8 * lazard_fifth_product_i8_constant +
  2%:R * lazard_fifth_fourth_i7 * lazard_fifth_product_i7_constant +
  lazard_fifth_fourth_i6 * lazard_fifth_product_i6_constant +
  2%:R * lazard_fifth_fourth_i5 * lazard_fifth_product_i5_constant +
  2%:R * lazard_fifth_fourth_i4 * lazard_fifth_square_constant.

(** The six literal coefficients printed in Lazard's fifth equation. *)
Definition lazard_fifth_printed_i8 : F :=
  15%:R * p ^+ 4 * r - 5%:R * p ^+ 3 * q ^+ 2 +
  290%:R * p ^+ 2 * q * s - 152%:R * p ^+ 2 * r ^+ 2 -
  27%:R * p * q ^+ 2 * r - 1375%:R * p * s ^+ 2 +
  22%:R * q ^+ 4 - 700%:R * q * r * s + 240%:R * r ^+ 3.

Definition lazard_fifth_printed_i7 : F :=
  18%:R * p ^+ 4 * s - 11%:R * p ^+ 3 * q * r +
  3%:R * p ^+ 2 * q ^+ 3 - 530%:R * p ^+ 2 * r * s +
  110%:R * p * q ^+ 2 * s + 124%:R * p * q * r ^+ 2 -
  41%:R * q ^+ 3 * r - 2375%:R * q * s ^+ 2 +
  200%:R * r ^+ 2 * s.

Definition lazard_fifth_printed_i6 : F :=
  - 15%:R * p ^+ 5 * r + 5%:R * p ^+ 4 * q ^+ 2 -
  212%:R * p ^+ 3 * q * s + 168%:R * p ^+ 3 * r ^+ 2 -
  83%:R * p ^+ 2 * q ^+ 2 * r + 325%:R * p ^+ 2 * s ^+ 2 +
  10%:R * p * q ^+ 4 + 1560%:R * p * q * r * s -
  176%:R * p * r ^+ 3 - 620%:R * q ^+ 3 * s -
  12%:R * q ^+ 2 * r ^+ 2 - 1500%:R * r * s ^+ 2.

Definition lazard_fifth_printed_i5 : F :=
  15%:R * p ^+ 4 * q * r - 5%:R * p ^+ 3 * q ^+ 3 -
  147%:R * p ^+ 3 * r * s + 351%:R * p ^+ 2 * q ^+ 2 * s -
  90%:R * p ^+ 2 * q * r ^+ 2 - 43%:R * p * q ^+ 3 * r -
  3175%:R * p * q * s ^+ 2 - 420%:R * p * r ^+ 2 * s +
  20%:R * q ^+ 5 + 215%:R * q ^+ 2 * r * s +
  152%:R * q * r ^+ 3 + 625%:R * s ^+ 3.

Definition lazard_fifth_printed_i4 : F :=
  - 15%:R * p ^+ 6 * r + 5%:R * p ^+ 5 * q ^+ 2 -
  200%:R * p ^+ 4 * q * s + 200%:R * p ^+ 4 * r ^+ 2 -
  110%:R * p ^+ 3 * q ^+ 2 * r + 355%:R * p ^+ 3 * s ^+ 2 +
  15%:R * p ^+ 2 * q ^+ 4 + 1728%:R * p ^+ 2 * q * r * s -
  432%:R * p ^+ 2 * r ^+ 3 - 752%:R * p * q ^+ 3 * s +
  220%:R * p * q ^+ 2 * r ^+ 2 - 200%:R * p * r * s ^+ 2 -
  43%:R * q ^+ 4 * r + 1825%:R * q ^+ 2 * s ^+ 2 -
  2640%:R * q * r ^+ 2 * s + 512%:R * r ^+ 4.

Definition lazard_fifth_printed_constant : F :=
  - 30%:R * p ^+ 6 * r ^+ 2 + 25%:R * p ^+ 5 * q ^+ 2 * r +
  198%:R * p ^+ 5 * s ^+ 2 - 5%:R * p ^+ 4 * q ^+ 4 -
  491%:R * p ^+ 4 * q * r * s + 364%:R * p ^+ 4 * r ^+ 3 +
  181%:R * p ^+ 3 * q ^+ 3 * s -
  286%:R * p ^+ 3 * q ^+ 2 * r ^+ 2 -
  810%:R * p ^+ 3 * r * s ^+ 2 +
  95%:R * p ^+ 2 * q ^+ 4 * r +
  3005%:R * p ^+ 2 * q ^+ 2 * s ^+ 2 +
  4120%:R * p ^+ 2 * q * r ^+ 2 * s -
  1088%:R * p ^+ 2 * r ^+ 4 - 12%:R * p * q ^+ 6 -
  4095%:R * p * q ^+ 3 * r * s +
  612%:R * p * q ^+ 2 * r ^+ 3 -
  15875%:R * p * q * s ^+ 3 +
  900%:R * p * r ^+ 2 * s ^+ 2 +
  858%:R * q ^+ 5 * s - 34%:R * q ^+ 4 * r ^+ 2 +
  10700%:R * q ^+ 2 * r * s ^+ 2 -
  6240%:R * q * r ^+ 3 * s + 960%:R * r ^+ 5 +
  6250%:R * s ^+ 4.

Definition lazard_fifth_printed_numerator
    (i4 i5 i6 i7 i8 : F) : F :=
  lazard_fifth_printed_i8 * i8 +
  lazard_fifth_printed_i7 * i7 +
  lazard_fifth_printed_i6 * i6 +
  lazard_fifth_printed_i5 * i5 +
  lazard_fifth_printed_i4 * i4 +
  lazard_fifth_printed_constant.

End FifthData.

End PolynomialFormulasLazardQuinticRootInvariantRelationFifthData.
