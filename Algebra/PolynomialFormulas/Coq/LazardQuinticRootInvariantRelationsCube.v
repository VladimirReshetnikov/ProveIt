From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  LazardQuinticRootProjections LazardQuinticRootFourierNumeratorRing
  LazardQuinticRootInvariantRelationsSquare
  LazardQuinticRootInvariantRelationsProductsCore
  LazardQuinticRootInvariantRelationsProducts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The second Figure-3 identity, assembled abstractly from the independently
    checked square and Figure-2 product relations. *)
Module PolynomialFormulasLazardQuinticRootInvariantRelationsCube.

Import GRing.Theory.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module SQ := PolynomialFormulasLazardQuinticRootInvariantRelationsSquare.
Module PC := PolynomialFormulasLazardQuinticRootInvariantRelationsProductsCore.
Module PS := PolynomialFormulasLazardQuinticRootInvariantRelationsProducts.
Local Open Scope ring_scope.

Section Cube.

Variable F : fieldType.

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

Definition lazard_i4_cube_rhs
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  lazard_i4_cube_numerator c i / (2%:R : F).

Add Ring lazard_root_invariant_relations_cube_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Lemma lazard_cube_nine_natrE : (9%:R : F) = 8%:R + 1.
Proof. exact: (@natrD F 8 1). Qed.
Lemma lazard_cube_twenty_seven_natrE : (27%:R : F) = 26%:R + 1.
Proof. exact: (@natrD F 26 1). Qed.
Lemma lazard_cube_thirty_two_natrE : (32%:R : F) = 16%:R + 16%:R.
Proof. exact: (@natrD F 16 16). Qed.
Lemma lazard_cube_thirty_six_natrE : (36%:R : F) = 18%:R + 18%:R.
Proof. exact: (@natrD F 18 18). Qed.
Lemma lazard_cube_forty_one_natrE : (41%:R : F) = 40%:R + 1.
Proof. exact: (@natrD F 40 1). Qed.
Lemma lazard_cube_forty_five_natrE : (45%:R : F) = 40%:R + 5%:R.
Proof. exact: (@natrD F 40 5). Qed.
Lemma lazard_cube_fifty_two_natrE : (52%:R : F) = 26%:R + 26%:R.
Proof. exact: (@natrD F 26 26). Qed.
Lemma lazard_cube_fifty_four_natrE : (54%:R : F) = 27%:R + 27%:R.
Proof. exact: (@natrD F 27 27). Qed.
Lemma lazard_cube_sixty_natrE : (60%:R : F) = 30%:R + 30%:R.
Proof. exact: (@natrD F 30 30). Qed.
Lemma lazard_cube_eighty_natrE : (80%:R : F) = 40%:R + 40%:R.
Proof. exact: (@natrD F 40 40). Qed.
Lemma lazard_cube_two_hundred_fifty_natrE :
  (250%:R : F) = 125%:R + 125%:R.
Proof. exact: (@natrD F 125 125). Qed.

Ltac finish_cube_ring :=
  repeat first
    [ rewrite lazard_cube_two_hundred_fifty_natrE
    | rewrite lazard_cube_eighty_natrE
    | rewrite lazard_cube_sixty_natrE
    | rewrite lazard_cube_fifty_four_natrE
    | rewrite lazard_cube_fifty_two_natrE
    | rewrite lazard_cube_forty_five_natrE
    | rewrite lazard_cube_forty_one_natrE
    | rewrite lazard_cube_thirty_six_natrE
    | rewrite lazard_cube_thirty_two_natrE
    | rewrite lazard_cube_twenty_seven_natrE
    | rewrite lazard_cube_nine_natrE ];
  lazard_numerator_prepare;
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

Theorem lazard_i4_cube_twice_of_square_and_products
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F)
    (hsquare : RP.lazard_root_i4 i ^+ 2 = SQ.lazard_i4_square_rhs c i)
    (hproducts : PC.lazard_invariant_product_relations c i) :
  2%:R * RP.lazard_root_i4 i ^+ 3 = lazard_i4_cube_numerator c i.
Proof.
case: hproducts=> h5 h6 h7 h8.
apply: subr0_eq.
transitivity
  (2%:R *
      (RP.lazard_root_i4 i - 2%:R * RP.lazard_root_p c ^+ 2) *
      (RP.lazard_root_i4 i ^+ 2 - SQ.lazard_i4_square_rhs c i) +
    8%:R * RP.lazard_root_q c *
      (RP.lazard_root_i4 i * RP.lazard_root_i5 i -
        PC.lazard_i4_mul_i5_rhs c i) -
    2%:R * RP.lazard_root_p c *
      (2%:R * (RP.lazard_root_i4 i * RP.lazard_root_i6 i) -
        PC.lazard_twice_i4_mul_i6_rhs c i) +
    5%:R *
      (2%:R * (RP.lazard_root_i4 i * RP.lazard_root_i8 i) -
        PC.lazard_twice_i4_mul_i8_rhs c i)).
- rewrite /lazard_i4_cube_numerator /SQ.lazard_i4_square_rhs
    /PC.lazard_i4_mul_i5_rhs /PC.lazard_twice_i4_mul_i6_rhs
    /PC.lazard_twice_i4_mul_i8_rhs.
  finish_cube_ring.
- rewrite hsquare h5 h6 h8 !subrr.
  finish_cube_ring.
Qed.

Theorem lazard_i4_cube_of_square_and_products
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F)
    (two_neq0 : (2%:R : F) != 0)
    (hsquare : RP.lazard_root_i4 i ^+ 2 = SQ.lazard_i4_square_rhs c i)
    (hproducts : PC.lazard_invariant_product_relations c i) :
  RP.lazard_root_i4 i ^+ 3 = lazard_i4_cube_rhs c i.
Proof.
apply: (mulfI two_neq0).
rewrite (lazard_i4_cube_twice_of_square_and_products hsquare hproducts)
  /lazard_i4_cube_rhs.
by rewrite [2%:R * (_ / 2%:R)]mulrC divfK.
Qed.

Theorem lazard_root_invariants_cube
    (roots : 5.-tuple F) (two_neq0 : (2%:R : F) != 0)
    (hsum : RP.lazard_root_esymm1 roots = 0) :
  RP.lazard_root_i4 (RP.lazard_root_invariants roots) ^+ 3 =
    lazard_i4_cube_rhs (RP.lazard_depressed_of_roots roots)
      (RP.lazard_root_invariants roots).
Proof.
exact: lazard_i4_cube_of_square_and_products two_neq0
  (SQ.lazard_root_invariants_square hsum)
  (PS.lazard_root_invariant_product_relations hsum).
Qed.

End Cube.

End PolynomialFormulasLazardQuinticRootInvariantRelationsCube.
