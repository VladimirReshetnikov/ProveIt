From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootProjections
  LazardQuinticRootFourierNumeratorRing
  LazardQuinticRootInvariantRelations
  LazardQuinticRootInvariantRelationFifthCertificate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The large fourth equation in Lazard's Figure 3, isolated from the
    smaller root-origin reductions so its literal coefficient table can be
    audited independently. *)
Module PolynomialFormulasLazardQuinticRootInvariantRelationFifth.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module IR := PolynomialFormulasLazardQuinticRootInvariantRelations.
Module FC := PolynomialFormulasLazardQuinticRootInvariantRelationFifthCertificate.
Local Open Scope ring_scope.

Section RootInvariantRelationFifth.

Variable F : fieldType.

(** Denominator-cleared numerator of the [i4^5] equation. *)
Definition lazard_i4_fifth_numerator
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  (15%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_r c -
      5%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_q c ^+ 2 +
      290%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c *
        RP.lazard_root_s c -
      152%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c ^+ 2 -
      27%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 *
        RP.lazard_root_r c -
      1375%:R * RP.lazard_root_p c * RP.lazard_root_s c ^+ 2 +
      22%:R * RP.lazard_root_q c ^+ 4 -
      700%:R * RP.lazard_root_q c * RP.lazard_root_r c *
        RP.lazard_root_s c +
      240%:R * RP.lazard_root_r c ^+ 3) * RP.lazard_root_i8 i +
  (18%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_s c -
      11%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_q c *
        RP.lazard_root_r c +
      3%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c ^+ 3 -
      530%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c *
        RP.lazard_root_s c +
      110%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 *
        RP.lazard_root_s c +
      124%:R * RP.lazard_root_p c * RP.lazard_root_q c *
        RP.lazard_root_r c ^+ 2 -
      41%:R * RP.lazard_root_q c ^+ 3 * RP.lazard_root_r c -
      2375%:R * RP.lazard_root_q c * RP.lazard_root_s c ^+ 2 +
      200%:R * RP.lazard_root_r c ^+ 2 * RP.lazard_root_s c) *
    RP.lazard_root_i7 i +
  (- 15%:R * RP.lazard_root_p c ^+ 5 * RP.lazard_root_r c +
      5%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_q c ^+ 2 -
      212%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_q c *
        RP.lazard_root_s c +
      168%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_r c ^+ 2 -
      83%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c ^+ 2 *
        RP.lazard_root_r c +
      325%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_s c ^+ 2 +
      10%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 4 +
      1560%:R * RP.lazard_root_p c * RP.lazard_root_q c *
        RP.lazard_root_r c * RP.lazard_root_s c -
      176%:R * RP.lazard_root_p c * RP.lazard_root_r c ^+ 3 -
      620%:R * RP.lazard_root_q c ^+ 3 * RP.lazard_root_s c -
      12%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_r c ^+ 2 -
      1500%:R * RP.lazard_root_r c * RP.lazard_root_s c ^+ 2) *
    RP.lazard_root_i6 i +
  (15%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_q c *
        RP.lazard_root_r c -
      5%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_q c ^+ 3 -
      147%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_r c *
        RP.lazard_root_s c +
      351%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c ^+ 2 *
        RP.lazard_root_s c -
      90%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c *
        RP.lazard_root_r c ^+ 2 -
      43%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 3 *
        RP.lazard_root_r c -
      3175%:R * RP.lazard_root_p c * RP.lazard_root_q c *
        RP.lazard_root_s c ^+ 2 -
      420%:R * RP.lazard_root_p c * RP.lazard_root_r c ^+ 2 *
        RP.lazard_root_s c +
      20%:R * RP.lazard_root_q c ^+ 5 +
      215%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_r c *
        RP.lazard_root_s c +
      152%:R * RP.lazard_root_q c * RP.lazard_root_r c ^+ 3 +
      625%:R * RP.lazard_root_s c ^+ 3) * RP.lazard_root_i5 i +
  (- 15%:R * RP.lazard_root_p c ^+ 6 * RP.lazard_root_r c +
      5%:R * RP.lazard_root_p c ^+ 5 * RP.lazard_root_q c ^+ 2 -
      200%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_q c *
        RP.lazard_root_s c +
      200%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_r c ^+ 2 -
      110%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_q c ^+ 2 *
        RP.lazard_root_r c +
      355%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_s c ^+ 2 +
      15%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c ^+ 4 +
      1728%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c *
        RP.lazard_root_r c * RP.lazard_root_s c -
      432%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c ^+ 3 -
      752%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 3 *
        RP.lazard_root_s c +
      220%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 *
        RP.lazard_root_r c ^+ 2 -
      200%:R * RP.lazard_root_p c * RP.lazard_root_r c *
        RP.lazard_root_s c ^+ 2 -
      43%:R * RP.lazard_root_q c ^+ 4 * RP.lazard_root_r c +
      1825%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_s c ^+ 2 -
      2640%:R * RP.lazard_root_q c * RP.lazard_root_r c ^+ 2 *
        RP.lazard_root_s c +
      512%:R * RP.lazard_root_r c ^+ 4) * RP.lazard_root_i4 i +
  (- 30%:R * RP.lazard_root_p c ^+ 6 * RP.lazard_root_r c ^+ 2 +
  25%:R * RP.lazard_root_p c ^+ 5 * RP.lazard_root_q c ^+ 2 *
    RP.lazard_root_r c +
  198%:R * RP.lazard_root_p c ^+ 5 * RP.lazard_root_s c ^+ 2 -
  5%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_q c ^+ 4 -
  491%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_q c *
    RP.lazard_root_r c * RP.lazard_root_s c +
  364%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_r c ^+ 3 +
  181%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_q c ^+ 3 *
    RP.lazard_root_s c -
  286%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_q c ^+ 2 *
    RP.lazard_root_r c ^+ 2 -
  810%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_r c *
    RP.lazard_root_s c ^+ 2 +
  95%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c ^+ 4 *
    RP.lazard_root_r c +
  3005%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c ^+ 2 *
    RP.lazard_root_s c ^+ 2 +
  4120%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c *
    RP.lazard_root_r c ^+ 2 * RP.lazard_root_s c -
  1088%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c ^+ 4 -
  12%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 6 -
  4095%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 3 *
    RP.lazard_root_r c * RP.lazard_root_s c +
  612%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 *
    RP.lazard_root_r c ^+ 3 -
  15875%:R * RP.lazard_root_p c * RP.lazard_root_q c *
    RP.lazard_root_s c ^+ 3 +
  900%:R * RP.lazard_root_p c * RP.lazard_root_r c ^+ 2 *
    RP.lazard_root_s c ^+ 2 +
  858%:R * RP.lazard_root_q c ^+ 5 * RP.lazard_root_s c -
  34%:R * RP.lazard_root_q c ^+ 4 * RP.lazard_root_r c ^+ 2 +
  10700%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_r c *
    RP.lazard_root_s c ^+ 2 -
  6240%:R * RP.lazard_root_q c * RP.lazard_root_r c ^+ 3 *
    RP.lazard_root_s c +
  960%:R * RP.lazard_root_r c ^+ 5 +
  6250%:R * RP.lazard_root_s c ^+ 4).

Definition lazard_i4_fifth_rhs
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  lazard_i4_fifth_numerator c i / (2%:R : F).

Record lazard_invariant_relations
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : Prop := LazardInvariantRelations {
  lazard_relation_square :
    RP.lazard_root_i4 i ^+ 2 = IR.lazard_i4_square_rhs c i;
  lazard_relation_cube :
    RP.lazard_root_i4 i ^+ 3 = IR.lazard_i4_cube_rhs c i;
  lazard_relation_fourth :
    RP.lazard_root_i4 i ^+ 4 = IR.lazard_i4_fourth_rhs c i;
  lazard_relation_fifth :
    RP.lazard_root_i4 i ^+ 5 = lazard_i4_fifth_rhs c i
}.

Add Ring lazard_root_invariant_relation_fifth_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

(** A factorized numeral table for the large printed coefficients.  Keeping
    this table separate prevents reflective normalization from expanding,
    for example, [15875] into that many copies of one. *)
Lemma lazard_fifth_13_natrE : (13%:R : F) = 12%:R + 1.
Proof. exact: (@natrD F 12 1). Qed.
Lemma lazard_fifth_24_natrE : (24%:R : F) = 12%:R + 12%:R.
Proof. exact: (@natrD F 12 12). Qed.
Lemma lazard_fifth_43_natrE : (43%:R : F) = 42%:R + 1.
Proof. exact: (@natrD F 42 1). Qed.
Lemma lazard_fifth_49_natrE : (49%:R : F) = 7%:R * 7%:R.
Proof. exact: (@natrM F 7 7). Qed.
Lemma lazard_fifth_64_natrE : (64%:R : F) = 8%:R * 8%:R.
Proof. exact: (@natrM F 8 8). Qed.
Lemma lazard_fifth_81_natrE : (81%:R : F) = 9%:R * 9%:R.
Proof. exact: (@natrM F 9 9). Qed.
Lemma lazard_fifth_83_natrE : (83%:R : F) = 76%:R + 7%:R.
Proof. exact: (@natrD F 76 7). Qed.
Lemma lazard_fifth_90_natrE : (90%:R : F) = 9%:R * 10%:R.
Proof. exact: (@natrM F 9 10). Qed.
Lemma lazard_fifth_95_natrE : (95%:R : F) = 76%:R + 19%:R.
Proof. exact: (@natrD F 76 19). Qed.
Lemma lazard_fifth_110_natrE : (110%:R : F) = 11%:R * 10%:R.
Proof. exact: (@natrM F 11 10). Qed.
Lemma lazard_fifth_120_natrE : (120%:R : F) = 12%:R * 10%:R.
Proof. exact: (@natrM F 12 10). Qed.
Lemma lazard_fifth_124_natrE : (124%:R : F) = 100%:R + 24%:R.
Proof. exact: (@natrD F 100 24). Qed.
Lemma lazard_fifth_144_natrE : (144%:R : F) = 12%:R * 12%:R.
Proof. exact: (@natrM F 12 12). Qed.
Lemma lazard_fifth_147_natrE : (147%:R : F) = 140%:R + 7%:R.
Proof. exact: (@natrD F 140 7). Qed.
Lemma lazard_fifth_152_natrE : (152%:R : F) = 76%:R * 2%:R.
Proof. exact: (@natrM F 76 2). Qed.
Lemma lazard_fifth_156_natrE : (156%:R : F) = 140%:R + 16%:R.
Proof. exact: (@natrD F 140 16). Qed.
Lemma lazard_fifth_168_natrE : (168%:R : F) = 14%:R * 12%:R.
Proof. exact: (@natrM F 14 12). Qed.
Lemma lazard_fifth_176_natrE : (176%:R : F) = 16%:R * 11%:R.
Proof. exact: (@natrM F 16 11). Qed.
Lemma lazard_fifth_180_natrE : (180%:R : F) = 18%:R * 10%:R.
Proof. exact: (@natrM F 18 10). Qed.
Lemma lazard_fifth_181_natrE : (181%:R : F) = 180%:R + 1.
Proof. exact: (@natrD F 180 1). Qed.
Lemma lazard_fifth_198_natrE : (198%:R : F) = 18%:R * 11%:R.
Proof. exact: (@natrM F 18 11). Qed.
Lemma lazard_fifth_200_natrE : (200%:R : F) = 20%:R * 10%:R.
Proof. exact: (@natrM F 20 10). Qed.
Lemma lazard_fifth_212_natrE : (212%:R : F) = 200%:R + 12%:R.
Proof. exact: (@natrD F 200 12). Qed.
Lemma lazard_fifth_215_natrE : (215%:R : F) = 200%:R + 15%:R.
Proof. exact: (@natrD F 200 15). Qed.
Lemma lazard_fifth_220_natrE : (220%:R : F) = 22%:R * 10%:R.
Proof. exact: (@natrM F 22 10). Qed.
Lemma lazard_fifth_240_natrE : (240%:R : F) = 12%:R * 20%:R.
Proof. exact: (@natrM F 12 20). Qed.
Lemma lazard_fifth_286_natrE : (286%:R : F) = 26%:R * 11%:R.
Proof. exact: (@natrM F 26 11). Qed.
Lemma lazard_fifth_290_natrE : (290%:R : F) = 29%:R * 10%:R.
Proof. exact: (@natrM F 29 10). Qed.
Lemma lazard_fifth_300_natrE : (300%:R : F) = 30%:R * 10%:R.
Proof. exact: (@natrM F 30 10). Qed.
Lemma lazard_fifth_325_natrE : (325%:R : F) = 300%:R + 25%:R.
Proof. exact: (@natrD F 300 25). Qed.
Lemma lazard_fifth_350_natrE : (350%:R : F) = 35%:R * 10%:R.
Proof. exact: (@natrM F 35 10). Qed.
Lemma lazard_fifth_351_natrE : (351%:R : F) = 350%:R + 1.
Proof. exact: (@natrD F 350 1). Qed.
Lemma lazard_fifth_355_natrE : (355%:R : F) = 350%:R + 5%:R.
Proof. exact: (@natrD F 350 5). Qed.
Lemma lazard_fifth_364_natrE : (364%:R : F) = 28%:R * 13%:R.
Proof. exact: (@natrM F 28 13). Qed.
Lemma lazard_fifth_420_natrE : (420%:R : F) = 42%:R * 10%:R.
Proof. exact: (@natrM F 42 10). Qed.
Lemma lazard_fifth_432_natrE : (432%:R : F) = 12%:R * 36%:R.
Proof. exact: (@natrM F 12 36). Qed.
Lemma lazard_fifth_490_natrE : (490%:R : F) = 49%:R * 10%:R.
Proof. exact: (@natrM F 49 10). Qed.
Lemma lazard_fifth_491_natrE : (491%:R : F) = 490%:R + 1.
Proof. exact: (@natrD F 490 1). Qed.
Lemma lazard_fifth_500_natrE : (500%:R : F) = 50%:R * 10%:R.
Proof. exact: (@natrM F 50 10). Qed.
Lemma lazard_fifth_512_natrE : (512%:R : F) = 64%:R * 8%:R.
Proof. exact: (@natrM F 64 8). Qed.
Lemma lazard_fifth_530_natrE : (530%:R : F) = 500%:R + 30%:R.
Proof. exact: (@natrD F 500 30). Qed.
Lemma lazard_fifth_600_natrE : (600%:R : F) = 30%:R * 20%:R.
Proof. exact: (@natrM F 30 20). Qed.
Lemma lazard_fifth_612_natrE : (612%:R : F) = 600%:R + 12%:R.
Proof. exact: (@natrD F 600 12). Qed.
Lemma lazard_fifth_620_natrE : (620%:R : F) = 600%:R + 20%:R.
Proof. exact: (@natrD F 600 20). Qed.
Lemma lazard_fifth_625_natrE : (625%:R : F) = 25%:R * 25%:R.
Proof. exact: (@natrM F 25 25). Qed.
Lemma lazard_fifth_700_natrE : (700%:R : F) = 70%:R * 10%:R.
Proof. exact: (@natrM F 70 10). Qed.
Lemma lazard_fifth_752_natrE : (752%:R : F) = 700%:R + 52%:R.
Proof. exact: (@natrD F 700 52). Qed.
Lemma lazard_fifth_800_natrE : (800%:R : F) = 8%:R * 100%:R.
Proof. exact: (@natrM F 8 100). Qed.
Lemma lazard_fifth_810_natrE : (810%:R : F) = 81%:R * 10%:R.
Proof. exact: (@natrM F 81 10). Qed.
Lemma lazard_fifth_858_natrE : (858%:R : F) = 800%:R + 58%:R.
Proof. exact: (@natrD F 800 58). Qed.
Lemma lazard_fifth_900_natrE : (900%:R : F) = 30%:R * 30%:R.
Proof. exact: (@natrM F 30 30). Qed.
Lemma lazard_fifth_960_natrE : (960%:R : F) = 12%:R * 80%:R.
Proof. exact: (@natrM F 12 80). Qed.
Lemma lazard_fifth_1000_natrE : (1000%:R : F) = 10%:R * 100%:R.
Proof. exact: (@natrM F 10 100). Qed.
Lemma lazard_fifth_1088_natrE : (1088%:R : F) = 68%:R * 16%:R.
Proof. exact: (@natrM F 68 16). Qed.
Lemma lazard_fifth_1375_natrE : (1375%:R : F) = 125%:R * 11%:R.
Proof. exact: (@natrM F 125 11). Qed.
Lemma lazard_fifth_1500_natrE : (1500%:R : F) = 15%:R * 100%:R.
Proof. exact: (@natrM F 15 100). Qed.
Lemma lazard_fifth_1560_natrE : (1560%:R : F) = 156%:R * 10%:R.
Proof. exact: (@natrM F 156 10). Qed.
Lemma lazard_fifth_1728_natrE : (1728%:R : F) = 144%:R * 12%:R.
Proof. exact: (@natrM F 144 12). Qed.
Lemma lazard_fifth_1800_natrE : (1800%:R : F) = 18%:R * 100%:R.
Proof. exact: (@natrM F 18 100). Qed.
Lemma lazard_fifth_1825_natrE : (1825%:R : F) = 1800%:R + 25%:R.
Proof. exact: (@natrD F 1800 25). Qed.
Lemma lazard_fifth_2375_natrE : (2375%:R : F) = 125%:R * 19%:R.
Proof. exact: (@natrM F 125 19). Qed.
Lemma lazard_fifth_2600_natrE : (2600%:R : F) = 26%:R * 100%:R.
Proof. exact: (@natrM F 26 100). Qed.
Lemma lazard_fifth_2640_natrE : (2640%:R : F) = 2600%:R + 40%:R.
Proof. exact: (@natrD F 2600 40). Qed.
Lemma lazard_fifth_3000_natrE : (3000%:R : F) = 30%:R * 100%:R.
Proof. exact: (@natrM F 30 100). Qed.
Lemma lazard_fifth_3005_natrE : (3005%:R : F) = 3000%:R + 5%:R.
Proof. exact: (@natrD F 3000 5). Qed.
Lemma lazard_fifth_3125_natrE : (3125%:R : F) = 125%:R * 25%:R.
Proof. exact: (@natrM F 125 25). Qed.
Lemma lazard_fifth_3175_natrE : (3175%:R : F) = 3125%:R + 50%:R.
Proof. exact: (@natrD F 3125 50). Qed.
Lemma lazard_fifth_4000_natrE : (4000%:R : F) = 40%:R * 100%:R.
Proof. exact: (@natrM F 40 100). Qed.
Lemma lazard_fifth_4095_natrE : (4095%:R : F) = 4000%:R + 95%:R.
Proof. exact: (@natrD F 4000 95). Qed.
Lemma lazard_fifth_4120_natrE : (4120%:R : F) = 4000%:R + 120%:R.
Proof. exact: (@natrD F 4000 120). Qed.
Lemma lazard_fifth_6000_natrE : (6000%:R : F) = 60%:R * 100%:R.
Proof. exact: (@natrM F 60 100). Qed.
Lemma lazard_fifth_6240_natrE : (6240%:R : F) = 6000%:R + 240%:R.
Proof. exact: (@natrD F 6000 240). Qed.
Lemma lazard_fifth_6250_natrE : (6250%:R : F) = 25%:R * 250%:R.
Proof. exact: (@natrM F 25 250). Qed.
Lemma lazard_fifth_10000_natrE : (10000%:R : F) = 100%:R * 100%:R.
Proof. exact: (@natrM F 100 100). Qed.
Lemma lazard_fifth_10700_natrE : (10700%:R : F) = 10000%:R + 700%:R.
Proof. exact: (@natrD F 10000 700). Qed.
Lemma lazard_fifth_15625_natrE : (15625%:R : F) = 125%:R * 125%:R.
Proof. exact: (@natrM F 125 125). Qed.
Lemma lazard_fifth_15875_natrE : (15875%:R : F) = 15625%:R + 250%:R.
Proof. exact: (@natrD F 15625 250). Qed.

Lemma lazard_fifth_expr6 (x : F) :
  x ^+ 6 = x * x * x * x * x * x.
Proof. by rewrite exprSr NR.lazard_numerator_expr5. Qed.

Ltac lazard_fifth_prepare :=
  repeat first
    [ rewrite lazard_fifth_15875_natrE
    | rewrite lazard_fifth_15625_natrE
    | rewrite lazard_fifth_10700_natrE
    | rewrite lazard_fifth_10000_natrE
    | rewrite lazard_fifth_6250_natrE
    | rewrite lazard_fifth_6240_natrE
    | rewrite lazard_fifth_6000_natrE
    | rewrite lazard_fifth_4120_natrE
    | rewrite lazard_fifth_4095_natrE
    | rewrite lazard_fifth_4000_natrE
    | rewrite lazard_fifth_3175_natrE
    | rewrite lazard_fifth_3125_natrE
    | rewrite lazard_fifth_3005_natrE
    | rewrite lazard_fifth_3000_natrE
    | rewrite lazard_fifth_2640_natrE
    | rewrite lazard_fifth_2600_natrE
    | rewrite lazard_fifth_2375_natrE
    | rewrite lazard_fifth_1825_natrE
    | rewrite lazard_fifth_1800_natrE
    | rewrite lazard_fifth_1728_natrE
    | rewrite lazard_fifth_1560_natrE
    | rewrite lazard_fifth_1500_natrE
    | rewrite lazard_fifth_1375_natrE
    | rewrite lazard_fifth_1088_natrE
    | rewrite lazard_fifth_1000_natrE
    | rewrite lazard_fifth_960_natrE
    | rewrite lazard_fifth_900_natrE
    | rewrite lazard_fifth_858_natrE
    | rewrite lazard_fifth_810_natrE
    | rewrite lazard_fifth_800_natrE
    | rewrite lazard_fifth_752_natrE
    | rewrite lazard_fifth_700_natrE
    | rewrite lazard_fifth_625_natrE
    | rewrite lazard_fifth_620_natrE
    | rewrite lazard_fifth_612_natrE
    | rewrite lazard_fifth_600_natrE
    | rewrite lazard_fifth_530_natrE
    | rewrite lazard_fifth_512_natrE
    | rewrite lazard_fifth_500_natrE
    | rewrite lazard_fifth_491_natrE
    | rewrite lazard_fifth_490_natrE
    | rewrite lazard_fifth_432_natrE
    | rewrite lazard_fifth_420_natrE
    | rewrite lazard_fifth_364_natrE
    | rewrite lazard_fifth_355_natrE
    | rewrite lazard_fifth_351_natrE
    | rewrite lazard_fifth_350_natrE
    | rewrite lazard_fifth_325_natrE
    | rewrite lazard_fifth_300_natrE
    | rewrite lazard_fifth_290_natrE
    | rewrite lazard_fifth_286_natrE
    | rewrite lazard_fifth_240_natrE
    | rewrite lazard_fifth_220_natrE
    | rewrite lazard_fifth_215_natrE
    | rewrite lazard_fifth_212_natrE
    | rewrite lazard_fifth_200_natrE
    | rewrite lazard_fifth_198_natrE
    | rewrite lazard_fifth_181_natrE
    | rewrite lazard_fifth_180_natrE
    | rewrite lazard_fifth_176_natrE
    | rewrite lazard_fifth_168_natrE
    | rewrite lazard_fifth_156_natrE
    | rewrite lazard_fifth_152_natrE
    | rewrite lazard_fifth_147_natrE
    | rewrite lazard_fifth_144_natrE
    | rewrite lazard_fifth_124_natrE
    | rewrite lazard_fifth_120_natrE
    | rewrite lazard_fifth_110_natrE
    | rewrite lazard_fifth_95_natrE
    | rewrite lazard_fifth_90_natrE
    | rewrite lazard_fifth_83_natrE
    | rewrite lazard_fifth_81_natrE
    | rewrite lazard_fifth_64_natrE
    | rewrite lazard_fifth_49_natrE
    | rewrite lazard_fifth_43_natrE
    | rewrite lazard_fifth_24_natrE
    | rewrite lazard_fifth_13_natrE
    | rewrite IR.lazard_invariant_relations_five_hundred_fifty_natrE
    | rewrite IR.lazard_invariant_relations_four_hundred_four_natrE
    | rewrite IR.lazard_invariant_relations_two_hundred_fifty_natrE
    | rewrite IR.lazard_invariant_relations_two_hundred_twenty_five_natrE
    | rewrite IR.lazard_invariant_relations_hundred_fifty_five_natrE
    | rewrite IR.lazard_invariant_relations_hundred_thirty_two_natrE
    | rewrite IR.lazard_invariant_relations_eighty_natrE
    | rewrite IR.lazard_invariant_relations_seventy_nine_natrE
    | rewrite IR.lazard_invariant_relations_sixty_natrE
    | rewrite IR.lazard_invariant_relations_fifty_four_natrE
    | rewrite IR.lazard_invariant_relations_fifty_two_natrE
    | rewrite IR.lazard_invariant_relations_forty_five_natrE
    | rewrite IR.lazard_invariant_relations_forty_two_natrE
    | rewrite IR.lazard_invariant_relations_forty_one_natrE
    | rewrite IR.lazard_invariant_relations_thirty_six_natrE
    | rewrite IR.lazard_invariant_relations_thirty_two_natrE
    | rewrite IR.lazard_invariant_relations_twenty_nine_natrE
    | rewrite IR.lazard_invariant_relations_twenty_seven_natrE
    | rewrite IR.lazard_invariant_relations_nineteen_natrE
    | rewrite IR.lazard_invariant_relations_nine_natrE
    | rewrite lazard_fifth_expr6 ];
  lazard_numerator_prepare.

Ltac finish_lazard_root_invariant_relation_fifth_ring :=
  lazard_fifth_prepare;
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

(** Denominator-cleared fourth Figure-3 equation.  This is a polynomial
    combination of the fourth-power equation and the same four Figure-2
    reductions; no invariant-relation certificate is an input. *)
Theorem lazard_i4_fifth_twice_of_square_fourth_and_products
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F)
    (hsquare : RP.lazard_root_i4 i ^+ 2 = IR.lazard_i4_square_rhs c i)
    (hfourth : RP.lazard_root_i4 i ^+ 4 = IR.lazard_i4_fourth_rhs c i)
    (hproducts : IR.lazard_invariant_product_relations c i) :
  2%:R * RP.lazard_root_i4 i ^+ 5 = lazard_i4_fifth_numerator c i.
Proof.
case: hproducts=> h5 h6 h7 h8.
apply: subr0_eq.
transitivity
  (2%:R * RP.lazard_root_i4 i *
      (RP.lazard_root_i4 i ^+ 4 - IR.lazard_i4_fourth_rhs c i) +
    (19%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c -
        9%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 +
        225%:R * RP.lazard_root_q c * RP.lazard_root_s c -
        60%:R * RP.lazard_root_r c ^+ 2) *
      (2%:R * (RP.lazard_root_i4 i * RP.lazard_root_i8 i) -
        IR.lazard_twice_i4_mul_i8_rhs c i) +
    2%:R *
      (15%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_s c -
        8%:R * RP.lazard_root_p c * RP.lazard_root_q c *
          RP.lazard_root_r c +
        3%:R * RP.lazard_root_q c ^+ 3 +
        100%:R * RP.lazard_root_r c * RP.lazard_root_s c) *
      (RP.lazard_root_i4 i * RP.lazard_root_i7 i -
        IR.lazard_i4_mul_i7_rhs c i) +
    (- 4%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_r c +
        4%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c ^+ 2 -
        105%:R * RP.lazard_root_p c * RP.lazard_root_q c *
          RP.lazard_root_s c -
        16%:R * RP.lazard_root_p c * RP.lazard_root_r c ^+ 2 +
        29%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_r c +
        125%:R * RP.lazard_root_s c ^+ 2) *
      (2%:R * (RP.lazard_root_i4 i * RP.lazard_root_i6 i) -
        IR.lazard_twice_i4_mul_i6_rhs c i) +
    2%:R *
      (- 9%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_s c +
        17%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c *
          RP.lazard_root_r c -
        8%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 3 +
        140%:R * RP.lazard_root_p c * RP.lazard_root_r c *
          RP.lazard_root_s c +
        155%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_s c -
        68%:R * RP.lazard_root_q c * RP.lazard_root_r c ^+ 2) *
      (RP.lazard_root_i4 i * RP.lazard_root_i5 i -
        IR.lazard_i4_mul_i5_rhs c i) +
    2%:R *
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
          RP.lazard_root_s c) *
      (RP.lazard_root_i4 i ^+ 2 - IR.lazard_i4_square_rhs c i)).
- exact: FC.lazard_i4_fifth_residual_certificate c i.
- by rewrite hfourth h8 h7 h6 h5 hsquare !subrr !mulr0 !addr0.
Qed.

Theorem lazard_i4_fifth_of_square_fourth_and_products
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F)
    (two_neq0 : (2%:R : F) != 0)
    (hsquare : RP.lazard_root_i4 i ^+ 2 = IR.lazard_i4_square_rhs c i)
    (hfourth : RP.lazard_root_i4 i ^+ 4 = IR.lazard_i4_fourth_rhs c i)
    (hproducts : IR.lazard_invariant_product_relations c i) :
  RP.lazard_root_i4 i ^+ 5 = lazard_i4_fifth_rhs c i.
Proof.
apply: (mulfI two_neq0).
rewrite (lazard_i4_fifth_twice_of_square_fourth_and_products
  hsquare hfourth hproducts) /lazard_i4_fifth_rhs.
by rewrite [2%:R * (_ / 2%:R)]mulrC divfK.
Qed.

Theorem lazard_root_invariants_fifth
    (roots : 5.-tuple F) (two_neq0 : (2%:R : F) != 0)
    (hsum : RP.lazard_root_esymm1 roots = 0) :
  RP.lazard_root_i4 (RP.lazard_root_invariants roots) ^+ 5 =
    lazard_i4_fifth_rhs (RP.lazard_depressed_of_roots roots)
      (RP.lazard_root_invariants roots).
Proof.
have hsquare := IR.lazard_root_invariants_square hsum.
have hproducts := IR.lazard_root_invariant_product_relations hsum.
have hfourth := IR.lazard_root_invariants_fourth two_neq0 hsum.
exact: lazard_i4_fifth_of_square_fourth_and_products
  two_neq0 hsquare hfourth hproducts.
Qed.

(** All four literal Figure-3 identities, constructed from the actual root
    orbit sums.  The only premise beyond depression is [2 != 0], required by
    the two printed divisions. *)
Theorem lazard_root_invariant_relations
    (roots : 5.-tuple F) (two_neq0 : (2%:R : F) != 0)
    (hsum : RP.lazard_root_esymm1 roots = 0) :
  lazard_invariant_relations
    (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots).
Proof.
constructor.
- exact: IR.lazard_root_invariants_square hsum.
- exact: IR.lazard_root_invariants_cube two_neq0 hsum.
- exact: IR.lazard_root_invariants_fourth two_neq0 hsum.
- exact: lazard_root_invariants_fifth two_neq0 hsum.
Qed.

End RootInvariantRelationFifth.

Print Assumptions lazard_i4_fifth_twice_of_square_fourth_and_products.
Print Assumptions lazard_root_invariants_fifth.
Print Assumptions lazard_root_invariant_relations.

End PolynomialFormulasLazardQuinticRootInvariantRelationFifth.

(** Public preparation tactic for downstream certificate modules.  Ltac
    definitions inside a module are not addressable as module fields after a
    compiled import, so the shared rewrite set is exported explicitly. *)
Ltac lazard_fifth_prepare :=
  repeat first
    [ rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_15875_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_15625_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_10700_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_10000_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_6250_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_6240_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_6000_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_4120_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_4095_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_4000_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_3175_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_3125_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_3005_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_3000_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_2640_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_2600_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_2375_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_1825_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_1800_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_1728_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_1560_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_1500_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_1375_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_1088_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_1000_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_960_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_900_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_858_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_810_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_800_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_752_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_700_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_625_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_620_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_612_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_600_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_530_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_512_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_500_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_491_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_490_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_432_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_420_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_364_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_355_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_351_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_350_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_325_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_300_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_290_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_286_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_240_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_220_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_215_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_212_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_200_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_198_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_181_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_180_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_176_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_168_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_156_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_152_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_147_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_144_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_124_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_120_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_110_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_95_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_90_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_83_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_81_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_64_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_49_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_43_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_24_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_13_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_five_hundred_fifty_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_four_hundred_four_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_two_hundred_fifty_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_two_hundred_twenty_five_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_hundred_fifty_five_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_hundred_thirty_two_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_eighty_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_seventy_nine_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_sixty_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_fifty_four_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_fifty_two_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_forty_five_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_forty_two_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_forty_one_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_thirty_six_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_thirty_two_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_twenty_nine_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_twenty_seven_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_nineteen_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_nine_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifth.lazard_fifth_expr6 ];
  lazard_numerator_prepare.
