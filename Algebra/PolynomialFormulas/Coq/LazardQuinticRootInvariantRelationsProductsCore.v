From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import LazardQuinticRootProjections.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Proof-free statements of Lazard's four denominator-cleared Figure-2
    product reductions.  Their root-origin certificates are compiled in four
    independent files. *)
Module PolynomialFormulasLazardQuinticRootInvariantRelationsProductsCore.

Import GRing.Theory.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Local Open Scope ring_scope.

Section ProductsCore.

Variable F : fieldType.

Definition lazard_i4_mul_i5_rhs
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  10%:R * RP.lazard_root_r c * RP.lazard_root_s c -
    2%:R * RP.lazard_root_q c ^+ 3 +
    5%:R * RP.lazard_root_p c * RP.lazard_root_q c *
      RP.lazard_root_r c -
    6%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_s c +
    RP.lazard_root_p c * RP.lazard_root_q c * RP.lazard_root_i4 i -
    2%:R * RP.lazard_root_r c * RP.lazard_root_i5 i +
    RP.lazard_root_q c * RP.lazard_root_i6 i -
    RP.lazard_root_p c * RP.lazard_root_i7 i.

Definition lazard_twice_i4_mul_i6_rhs
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  50%:R * RP.lazard_root_s c ^+ 2 +
    2%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_r c -
    4%:R * RP.lazard_root_p c * RP.lazard_root_r c ^+ 2 -
    27%:R * RP.lazard_root_p c * RP.lazard_root_q c *
      RP.lazard_root_s c -
    3%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c ^+ 2 +
    10%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_r c +
    RP.lazard_root_q c ^+ 2 * RP.lazard_root_i4 i -
    4%:R * RP.lazard_root_p c * RP.lazard_root_r c *
      RP.lazard_root_i4 i +
    3%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_i4 i +
    5%:R * RP.lazard_root_s c * RP.lazard_root_i5 i -
    7%:R * RP.lazard_root_p c * RP.lazard_root_q c *
      RP.lazard_root_i5 i -
    4%:R * RP.lazard_root_r c * RP.lazard_root_i6 i +
    3%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_i6 i -
    RP.lazard_root_q c * RP.lazard_root_i7 i -
    9%:R * RP.lazard_root_p c * RP.lazard_root_i8 i.

Definition lazard_i4_mul_i7_rhs
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  - 6%:R * RP.lazard_root_q c * RP.lazard_root_r c ^+ 2 +
    8%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_s c -
    11%:R * RP.lazard_root_p c * RP.lazard_root_r c *
      RP.lazard_root_s c -
    RP.lazard_root_p c * RP.lazard_root_q c ^+ 3 +
    3%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c *
      RP.lazard_root_r c +
    3%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_s c -
    2%:R * RP.lazard_root_q c * RP.lazard_root_r c *
      RP.lazard_root_i4 i -
    4%:R * RP.lazard_root_p c * RP.lazard_root_s c *
      RP.lazard_root_i4 i +
    RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c *
      RP.lazard_root_i4 i -
    2%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_i5 i -
    RP.lazard_root_p c * RP.lazard_root_r c * RP.lazard_root_i5 i -
    5%:R * RP.lazard_root_s c * RP.lazard_root_i6 i +
    RP.lazard_root_p c * RP.lazard_root_q c * RP.lazard_root_i6 i -
    2%:R * RP.lazard_root_r c * RP.lazard_root_i7 i -
    3%:R * RP.lazard_root_q c * RP.lazard_root_i8 i.

Definition lazard_twice_i4_mul_i8_rhs
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  - 16%:R * RP.lazard_root_r c ^+ 3 +
    12%:R * RP.lazard_root_q c * RP.lazard_root_r c *
      RP.lazard_root_s c +
    6%:R * RP.lazard_root_q c ^+ 4 -
    30%:R * RP.lazard_root_p c * RP.lazard_root_s c ^+ 2 -
    18%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 *
      RP.lazard_root_r c +
    12%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c ^+ 2 +
    15%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c *
      RP.lazard_root_s c +
    RP.lazard_root_p c ^+ 3 * RP.lazard_root_q c ^+ 2 -
    2%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_r c -
    8%:R * RP.lazard_root_r c ^+ 2 * RP.lazard_root_i4 i +
    8%:R * RP.lazard_root_q c * RP.lazard_root_s c *
      RP.lazard_root_i4 i -
    5%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 *
      RP.lazard_root_i4 i +
    8%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c *
      RP.lazard_root_i4 i -
    RP.lazard_root_p c ^+ 4 * RP.lazard_root_i4 i +
    2%:R * RP.lazard_root_q c * RP.lazard_root_r c *
      RP.lazard_root_i5 i -
    7%:R * RP.lazard_root_p c * RP.lazard_root_s c *
      RP.lazard_root_i5 i +
    RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c *
      RP.lazard_root_i5 i -
    4%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_i6 i +
    4%:R * RP.lazard_root_p c * RP.lazard_root_r c *
      RP.lazard_root_i6 i -
    RP.lazard_root_p c ^+ 3 * RP.lazard_root_i6 i -
    10%:R * RP.lazard_root_s c * RP.lazard_root_i7 i +
    RP.lazard_root_p c * RP.lazard_root_q c * RP.lazard_root_i7 i -
    4%:R * RP.lazard_root_r c * RP.lazard_root_i8 i +
    RP.lazard_root_p c ^+ 2 * RP.lazard_root_i8 i.

Record lazard_invariant_product_relations
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : Prop :=
    LazardInvariantProductRelations {
  lazard_mul_i5 :
    RP.lazard_root_i4 i * RP.lazard_root_i5 i =
      lazard_i4_mul_i5_rhs c i;
  lazard_twice_mul_i6 :
    2%:R * (RP.lazard_root_i4 i * RP.lazard_root_i6 i) =
      lazard_twice_i4_mul_i6_rhs c i;
  lazard_mul_i7 :
    RP.lazard_root_i4 i * RP.lazard_root_i7 i =
      lazard_i4_mul_i7_rhs c i;
  lazard_twice_mul_i8 :
    2%:R * (RP.lazard_root_i4 i * RP.lazard_root_i8 i) =
      lazard_twice_i4_mul_i8_rhs c i
}.

End ProductsCore.

End PolynomialFormulasLazardQuinticRootInvariantRelationsProductsCore.
