From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootProjections
  LazardQuinticRootFourierNumeratorRing
  LazardQuinticRootInvariantRelationsSquare
  LazardQuinticRootInvariantRelationsProductsCore
  LazardQuinticRootInvariantRelationsProducts
  LazardQuinticRootInvariantRelationsCube.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Root-origin versions of Lazard's Figure-2 product reductions and
    Figure-3 invariant equations.

    This module deliberately starts from the orbit sums in
    [LazardQuinticRootProjections].  In particular, the equations below are
    conclusions about an ordered depressed root tuple, not fields of an
    externally supplied invariant certificate.  The two product identities
    which are printed with halves are kept in denominator-cleared form; this
    makes their polynomial content valid without silently assuming
    characteristic zero. *)
Module PolynomialFormulasLazardQuinticRootInvariantRelations.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module SQ := PolynomialFormulasLazardQuinticRootInvariantRelationsSquare.
Module PC := PolynomialFormulasLazardQuinticRootInvariantRelationsProductsCore.
Module PS := PolynomialFormulasLazardQuinticRootInvariantRelationsProducts.
Module CB := PolynomialFormulasLazardQuinticRootInvariantRelationsCube.
Local Open Scope ring_scope.

Section RootInvariantRelations.

Variable F : fieldType.

(** Figure 2: [i4 * i5]. *)
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

(** Twice the Figure-2 right side for [i4 * i6]. *)
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

(** Figure 2: [i4 * i7]. *)
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

(** Twice the Figure-2 right side for [i4 * i8]. *)
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

(** The aggregate keeps its historical public record type, while the four
    expensive root-origin certificates live behind the proof-free core
    record.  These two conversion lemmas are definitionally just fieldwise
    repackaging: the right-side definitions above and in the core module have
    the same bodies. *)
Lemma lazard_invariant_product_relations_of_core
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) :
  PC.lazard_invariant_product_relations c i ->
  lazard_invariant_product_relations c i.
Proof.
case=> h5 h6 h7 h8; constructor.
- exact: h5.
- exact: h6.
- exact: h7.
- exact: h8.
Qed.

Lemma lazard_invariant_product_relations_to_core
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) :
  lazard_invariant_product_relations c i ->
  PC.lazard_invariant_product_relations c i.
Proof.
case=> h5 h6 h7 h8; constructor.
- exact: h5.
- exact: h6.
- exact: h7.
- exact: h8.
Qed.

(** Right side of the first equation in Lazard's Figure 3. *)
Definition lazard_i4_square_rhs
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  5%:R * RP.lazard_root_i8 i -
    2%:R * RP.lazard_root_p c * RP.lazard_root_i6 i +
    4%:R * RP.lazard_root_q c * RP.lazard_root_i5 i -
    2%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_i4 i -
    6%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c +
    2%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 +
    10%:R * RP.lazard_root_q c * RP.lazard_root_s c +
    4%:R * RP.lazard_root_r c ^+ 2.

(** Denominator-cleared numerator of the second equation in Figure 3. *)
Definition lazard_i4_cube_numerator
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  (3%:R * RP.lazard_root_p c ^+ 2 -
        20%:R * RP.lazard_root_r c) * RP.lazard_root_i8 i +
    (- RP.lazard_root_p c * RP.lazard_root_q c -
        50%:R * RP.lazard_root_s c) * RP.lazard_root_i7 i +
    (- 3%:R * RP.lazard_root_p c ^+ 3 +
        28%:R * RP.lazard_root_p c * RP.lazard_root_r c -
        12%:R * RP.lazard_root_q c ^+ 2) * RP.lazard_root_i6 i +
    (3%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c -
        45%:R * RP.lazard_root_p c * RP.lazard_root_s c -
        6%:R * RP.lazard_root_q c * RP.lazard_root_r c) *
      RP.lazard_root_i5 i +
    (- 3%:R * RP.lazard_root_p c ^+ 4 +
        36%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c -
        15%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 +
        60%:R * RP.lazard_root_q c * RP.lazard_root_s c -
        32%:R * RP.lazard_root_r c ^+ 2) * RP.lazard_root_i4 i -
    6%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_r c +
    3%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_q c ^+ 2 +
    41%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c *
      RP.lazard_root_s c +
    52%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c ^+ 2 -
    54%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 *
      RP.lazard_root_r c -
    250%:R * RP.lazard_root_p c * RP.lazard_root_s c ^+ 2 +
    14%:R * RP.lazard_root_q c ^+ 4 +
    140%:R * RP.lazard_root_q c * RP.lazard_root_r c *
      RP.lazard_root_s c -
    80%:R * RP.lazard_root_r c ^+ 3.

(** Right side of the second equation in Lazard's Figure 3. *)
Definition lazard_i4_cube_rhs
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  lazard_i4_cube_numerator c i / (2%:R : F).

(** Right side of the third equation in Lazard's Figure 3. *)
Definition lazard_i4_fourth_rhs
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  (19%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c -
      9%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 +
      225%:R * RP.lazard_root_q c * RP.lazard_root_s c -
      60%:R * RP.lazard_root_r c ^+ 2) * RP.lazard_root_i8 i +
  (15%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_s c -
      8%:R * RP.lazard_root_p c * RP.lazard_root_q c *
        RP.lazard_root_r c +
      3%:R * RP.lazard_root_q c ^+ 3 +
      100%:R * RP.lazard_root_r c * RP.lazard_root_s c) *
    RP.lazard_root_i7 i +
  (- 4%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_r c +
      4%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c ^+ 2 -
      105%:R * RP.lazard_root_p c * RP.lazard_root_q c *
        RP.lazard_root_s c -
      16%:R * RP.lazard_root_p c * RP.lazard_root_r c ^+ 2 +
      29%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_r c +
      125%:R * RP.lazard_root_s c ^+ 2) * RP.lazard_root_i6 i +
  (- 9%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_s c +
      17%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c *
        RP.lazard_root_r c -
      8%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 3 +
      140%:R * RP.lazard_root_p c * RP.lazard_root_r c *
        RP.lazard_root_s c +
      155%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_s c -
      68%:R * RP.lazard_root_q c * RP.lazard_root_r c ^+ 2) *
    RP.lazard_root_i5 i +
  (- 4%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_r c +
      4%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_q c ^+ 2 -
      79%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c *
        RP.lazard_root_s c -
      16%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c ^+ 2 +
      15%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 *
        RP.lazard_root_r c -
      25%:R * RP.lazard_root_p c * RP.lazard_root_s c ^+ 2 +
      4%:R * RP.lazard_root_q c ^+ 4 +
      80%:R * RP.lazard_root_q c * RP.lazard_root_r c *
        RP.lazard_root_s c) * RP.lazard_root_i4 i +
  6%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_q c *
    RP.lazard_root_s c -
  22%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_r c ^+ 2 +
  16%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_q c ^+ 2 *
    RP.lazard_root_r c -
  4%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c ^+ 4 -
  404%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c *
    RP.lazard_root_r c * RP.lazard_root_s c +
  68%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c ^+ 3 +
  132%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 3 *
    RP.lazard_root_s c +
  42%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 *
    RP.lazard_root_r c ^+ 2 +
  550%:R * RP.lazard_root_p c * RP.lazard_root_r c *
    RP.lazard_root_s c ^+ 2 -
  30%:R * RP.lazard_root_q c ^+ 4 * RP.lazard_root_r c -
  50%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_s c ^+ 2 +
  20%:R * RP.lazard_root_q c * RP.lazard_root_r c ^+ 2 *
    RP.lazard_root_s c +
  16%:R * RP.lazard_root_r c ^+ 4.

(** The fifth-power right side is intentionally left for a companion source
    shard, where its large coefficient table can be checked independently.
    This file gives definitions for the first three equations, proves the
    square equation, and proves the four root-origin Figure-2 reductions. *)

Record lazard_first_three_invariant_relations
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : Prop :=
    LazardFirstThreeInvariantRelations {
  lazard_square_relation :
    RP.lazard_root_i4 i ^+ 2 = lazard_i4_square_rhs c i;
  lazard_cube_relation :
    RP.lazard_root_i4 i ^+ 3 = lazard_i4_cube_rhs c i;
  lazard_fourth_relation :
    RP.lazard_root_i4 i ^+ 4 = lazard_i4_fourth_rhs c i
}.

Add Ring lazard_root_invariant_relations_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Lemma lazard_invariant_relations_nine_natrE : (9%:R : F) = 8%:R + 1.
Proof. exact: (@natrD F 8 1). Qed.

Lemma lazard_invariant_relations_twenty_seven_natrE :
  (27%:R : F) = 26%:R + 1.
Proof. exact: (@natrD F 26 1). Qed.

Lemma lazard_invariant_relations_nineteen_natrE :
  (19%:R : F) = 18%:R + 1.
Proof. exact: (@natrD F 18 1). Qed.
Lemma lazard_invariant_relations_twenty_nine_natrE :
  (29%:R : F) = 28%:R + 1.
Proof. exact: (@natrD F 28 1). Qed.
Lemma lazard_invariant_relations_thirty_two_natrE :
  (32%:R : F) = 16%:R + 16%:R.
Proof. exact: (@natrD F 16 16). Qed.
Lemma lazard_invariant_relations_thirty_six_natrE :
  (36%:R : F) = 18%:R + 18%:R.
Proof. exact: (@natrD F 18 18). Qed.
Lemma lazard_invariant_relations_forty_one_natrE :
  (41%:R : F) = 40%:R + 1.
Proof. exact: (@natrD F 40 1). Qed.
Lemma lazard_invariant_relations_forty_two_natrE :
  (42%:R : F) = 40%:R + 2%:R.
Proof. exact: (@natrD F 40 2). Qed.
Lemma lazard_invariant_relations_forty_five_natrE :
  (45%:R : F) = 40%:R + 5%:R.
Proof. exact: (@natrD F 40 5). Qed.
Lemma lazard_invariant_relations_fifty_two_natrE :
  (52%:R : F) = 26%:R + 26%:R.
Proof. exact: (@natrD F 26 26). Qed.
Lemma lazard_invariant_relations_fifty_four_natrE :
  (54%:R : F) = 27%:R + 27%:R.
Proof. exact: (@natrD F 27 27). Qed.
Lemma lazard_invariant_relations_sixty_natrE :
  (60%:R : F) = 30%:R + 30%:R.
Proof. exact: (@natrD F 30 30). Qed.
Lemma lazard_invariant_relations_seventy_nine_natrE :
  (79%:R : F) = 70%:R + 9%:R.
Proof. exact: (@natrD F 70 9). Qed.
Lemma lazard_invariant_relations_eighty_natrE :
  (80%:R : F) = 40%:R + 40%:R.
Proof. exact: (@natrD F 40 40). Qed.
Lemma lazard_invariant_relations_hundred_thirty_two_natrE :
  (132%:R : F) = 100%:R + 32%:R.
Proof. exact: (@natrD F 100 32). Qed.
Lemma lazard_invariant_relations_hundred_fifty_five_natrE :
  (155%:R : F) = 140%:R + 15%:R.
Proof. exact: (@natrD F 140 15). Qed.
Lemma lazard_invariant_relations_two_hundred_twenty_five_natrE :
  (225%:R : F) = 100%:R + 125%:R.
Proof. exact: (@natrD F 100 125). Qed.
Lemma lazard_invariant_relations_two_hundred_fifty_natrE :
  (250%:R : F) = 125%:R + 125%:R.
Proof. exact: (@natrD F 125 125). Qed.
Lemma lazard_invariant_relations_four_hundred_four_natrE :
  (404%:R : F) = 4%:R * 100%:R + 4%:R.
Proof.
rewrite -(@natrM F 4 100) -(@natrD F 400 4).
reflexivity.
Qed.
Lemma lazard_invariant_relations_five_hundred_fifty_natrE :
  (550%:R : F) = 50%:R * 11%:R.
Proof. exact: (@natrM F 50 11). Qed.

Ltac finish_lazard_root_invariant_relations_ring :=
  repeat first
    [ rewrite lazard_invariant_relations_five_hundred_fifty_natrE
    | rewrite lazard_invariant_relations_four_hundred_four_natrE
    | rewrite lazard_invariant_relations_two_hundred_fifty_natrE
    | rewrite lazard_invariant_relations_two_hundred_twenty_five_natrE
    | rewrite lazard_invariant_relations_hundred_fifty_five_natrE
    | rewrite lazard_invariant_relations_hundred_thirty_two_natrE
    | rewrite lazard_invariant_relations_eighty_natrE
    | rewrite lazard_invariant_relations_seventy_nine_natrE
    | rewrite lazard_invariant_relations_sixty_natrE
    | rewrite lazard_invariant_relations_fifty_four_natrE
    | rewrite lazard_invariant_relations_fifty_two_natrE
    | rewrite lazard_invariant_relations_forty_five_natrE
    | rewrite lazard_invariant_relations_forty_two_natrE
    | rewrite lazard_invariant_relations_forty_one_natrE
    | rewrite lazard_invariant_relations_thirty_six_natrE
    | rewrite lazard_invariant_relations_thirty_two_natrE
    | rewrite lazard_invariant_relations_twenty_nine_natrE
    | rewrite lazard_invariant_relations_twenty_seven_natrE
    | rewrite lazard_invariant_relations_nineteen_natrE
    | rewrite lazard_invariant_relations_nine_natrE ];
  lazard_numerator_prepare;
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

(** The first Figure-3 equation, derived directly from the five orbit sums. *)
Theorem lazard_root_invariants_square
    (roots : 5.-tuple F) (hsum : RP.lazard_root_esymm1 roots = 0) :
  RP.lazard_root_i4 (RP.lazard_root_invariants roots) ^+ 2 =
    lazard_i4_square_rhs (RP.lazard_depressed_of_roots roots)
      (RP.lazard_root_invariants roots).
Proof.
exact: SQ.lazard_root_invariants_square hsum.
Qed.

(** All four denominator-cleared Figure-2 product reductions follow from
    the same root orbit definitions. *)
Theorem lazard_root_invariant_product_relations
    (roots : 5.-tuple F) (hsum : RP.lazard_root_esymm1 roots = 0) :
  lazard_invariant_product_relations
    (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots).
Proof.
exact: lazard_invariant_product_relations_of_core
  (PS.lazard_root_invariant_product_relations hsum).
Qed.

(** The second Figure-3 equation before division by two.  Its proof is a
    polynomial combination of the square equation and three of the four
    Figure-2 reductions. *)
Theorem lazard_i4_cube_twice_of_square_and_products
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F)
    (hsquare : RP.lazard_root_i4 i ^+ 2 = lazard_i4_square_rhs c i)
    (hproducts : lazard_invariant_product_relations c i) :
  2%:R * RP.lazard_root_i4 i ^+ 3 = lazard_i4_cube_numerator c i.
Proof.
exact: CB.lazard_i4_cube_twice_of_square_and_products
  hsquare (lazard_invariant_product_relations_to_core hproducts).
Qed.

(** Literal second Figure-3 equation.  The only extra premise is the
    denominator condition which the printed division by two requires. *)
Theorem lazard_i4_cube_of_square_and_products
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F)
    (two_neq0 : (2%:R : F) != 0)
    (hsquare : RP.lazard_root_i4 i ^+ 2 = lazard_i4_square_rhs c i)
    (hproducts : lazard_invariant_product_relations c i) :
  RP.lazard_root_i4 i ^+ 3 = lazard_i4_cube_rhs c i.
Proof.
exact: CB.lazard_i4_cube_of_square_and_products
  two_neq0 hsquare (lazard_invariant_product_relations_to_core hproducts).
Qed.

(** The third Figure-3 equation.  Multiplying the target by four lets the
    proof use only the denominator-cleared cube and product identities. *)
Theorem lazard_i4_fourth_of_square_cube_and_products
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F)
    (two_neq0 : (2%:R : F) != 0)
    (hsquare : RP.lazard_root_i4 i ^+ 2 = lazard_i4_square_rhs c i)
    (hcube_twice :
      2%:R * RP.lazard_root_i4 i ^+ 3 = lazard_i4_cube_numerator c i)
    (hproducts : lazard_invariant_product_relations c i) :
  RP.lazard_root_i4 i ^+ 4 = lazard_i4_fourth_rhs c i.
Proof.
case: hproducts=> h5 h6 h7 h8.
have four_neq0 : (4%:R : F) != 0.
  rewrite (@natrM F 2 2).
  apply: mulf_neq0.
  - exact: two_neq0.
  - exact: two_neq0.
apply: (mulfI four_neq0).
apply: subr0_eq.
transitivity
  (2%:R * RP.lazard_root_i4 i *
      (2%:R * RP.lazard_root_i4 i ^+ 3 -
        lazard_i4_cube_numerator c i) +
    (3%:R * RP.lazard_root_p c ^+ 2 -
        20%:R * RP.lazard_root_r c) *
      (2%:R * (RP.lazard_root_i4 i * RP.lazard_root_i8 i) -
        lazard_twice_i4_mul_i8_rhs c i) +
    2%:R *
      (- RP.lazard_root_p c * RP.lazard_root_q c -
        50%:R * RP.lazard_root_s c) *
      (RP.lazard_root_i4 i * RP.lazard_root_i7 i -
        lazard_i4_mul_i7_rhs c i) +
    (- 3%:R * RP.lazard_root_p c ^+ 3 +
        28%:R * RP.lazard_root_p c * RP.lazard_root_r c -
        12%:R * RP.lazard_root_q c ^+ 2) *
      (2%:R * (RP.lazard_root_i4 i * RP.lazard_root_i6 i) -
        lazard_twice_i4_mul_i6_rhs c i) +
    2%:R *
      (3%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c -
        45%:R * RP.lazard_root_p c * RP.lazard_root_s c -
        6%:R * RP.lazard_root_q c * RP.lazard_root_r c) *
      (RP.lazard_root_i4 i * RP.lazard_root_i5 i -
        lazard_i4_mul_i5_rhs c i) +
    2%:R *
      (- 3%:R * RP.lazard_root_p c ^+ 4 +
        36%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c -
        15%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 +
        60%:R * RP.lazard_root_q c * RP.lazard_root_s c -
        32%:R * RP.lazard_root_r c ^+ 2) *
      (RP.lazard_root_i4 i ^+ 2 - lazard_i4_square_rhs c i)).
- rewrite /lazard_i4_fourth_rhs /lazard_i4_cube_numerator
    /lazard_i4_square_rhs /lazard_i4_mul_i5_rhs
    /lazard_twice_i4_mul_i6_rhs /lazard_i4_mul_i7_rhs
    /lazard_twice_i4_mul_i8_rhs.
  finish_lazard_root_invariant_relations_ring.
- rewrite hcube_twice h8 h7 h6 h5 hsquare !subrr.
  finish_lazard_root_invariant_relations_ring.
Qed.

Theorem lazard_root_invariants_cube
    (roots : 5.-tuple F) (two_neq0 : (2%:R : F) != 0)
    (hsum : RP.lazard_root_esymm1 roots = 0) :
  RP.lazard_root_i4 (RP.lazard_root_invariants roots) ^+ 3 =
    lazard_i4_cube_rhs (RP.lazard_depressed_of_roots roots)
      (RP.lazard_root_invariants roots).
Proof.
exact: CB.lazard_root_invariants_cube two_neq0 hsum.
Qed.

Theorem lazard_root_invariants_fourth
    (roots : 5.-tuple F) (two_neq0 : (2%:R : F) != 0)
    (hsum : RP.lazard_root_esymm1 roots = 0) :
  RP.lazard_root_i4 (RP.lazard_root_invariants roots) ^+ 4 =
    lazard_i4_fourth_rhs (RP.lazard_depressed_of_roots roots)
      (RP.lazard_root_invariants roots).
Proof.
have hsquare := lazard_root_invariants_square hsum.
have hproducts := lazard_root_invariant_product_relations hsum.
have hcube_twice :=
  lazard_i4_cube_twice_of_square_and_products hsquare hproducts.
exact: lazard_i4_fourth_of_square_cube_and_products
  two_neq0 hsquare hcube_twice hproducts.
Qed.

End RootInvariantRelations.

End PolynomialFormulasLazardQuinticRootInvariantRelations.
